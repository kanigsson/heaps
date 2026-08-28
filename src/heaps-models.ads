--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Multiset model of a key array, plus the handful of lemmas needed to reason
--  about the elementary transformations heap algorithms perform on arrays.
--
--  Everything here is ghost: it exists only to give the heaps a mathematical
--  model to state their postconditions against.
--
--  The model of the slice A (1 .. Lst) is the multiset of its keys. Two array
--  states are then a permutation of one another exactly when their models are
--  equal, and an operation that inserts or removes a key is described by an
--  Add on the model.

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every O(log n) operation into a quadratic one. Since the
--  contracts are discharged by proof, run-time checking of them is redundant,
--  so assertions are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;

package Heaps.Models with SPARK_Mode, Ghost, Always_Terminates is

   package KM renames Heaps.Key_Multisets;

   subtype Model is KM.Multiset;

   use type KM.Multiset;

   function Occurrences
     (A : Key_Array; Lst : Extended_Index) return Model
   is
     (if Lst = 0 then KM.Empty_Multiset
      else KM.Add (Occurrences (A, Lst - 1), A (Lst)))
   with
     Subprogram_Variant => (Decreases => Lst),
     Pre                => A'First = 1 and then Lst <= A'Last;
   --  The multiset of the keys held in A (1 .. Lst)

   function Occurrences_In
     (A : Key_Array; Fst : Positive; Lst : Extended_Index) return Model
   is
     (if Lst < Fst then KM.Empty_Multiset
      else KM.Add (Occurrences_In (A, Fst, Lst - 1), A (Lst)))
   with
     Subprogram_Variant => (Decreases => Lst),
     Pre                => A'First = 1 and then Lst <= A'Last;
   --  The multiset of the keys held in A (Fst .. Lst).
   --
   --  Occurrences models a prefix, which is all a heap whose keys occupy
   --  1 .. Last ever needs. A merge of two sorted runs is the one operation
   --  in the collection that leaves a hole in the middle of the array -- the
   --  part of the original run already consumed and not yet overwritten --
   --  and describing the two live regions on either side of it is what this
   --  is for.

   ---------------------------------
   -- Elementary multiset lemmas  --
   ---------------------------------

   --  Multiset equality is extensional, not the logical equality of the
   --  underlying values, so congruence of Add has to be established rather
   --  than assumed.

   procedure Lemma_Add_Congruent (X, Y : Model; E : Key_Type)
     with Pre => X = Y, Post => KM.Add (X, E) = KM.Add (Y, E);

   procedure Lemma_Add_Commutes (M : Model; E, F : Key_Type)
     with Post => KM.Add (KM.Add (M, E), F) = KM.Add (KM.Add (M, F), E);

   procedure Lemma_Add_Cancels (X, Y : Model; E : Key_Type)
     with Pre => KM.Add (X, E) = KM.Add (Y, E), Post => X = Y;

   ---------------------------------
   -- Sum lemmas                  --
   ---------------------------------

   --  A tree-shaped model is built by summing the models of two subtrees and
   --  adding the key of the node above them, so reasoning about it needs the
   --  monoid laws of Sum together with the one law that lets an Add move
   --  through a Sum. SPARKlib states only the symmetry of Sum; the rest
   --  follow from the occurrence count of each side and are discharged
   --  directly from the postconditions of Sum and Add.

   procedure Lemma_Sum_Empty (X : Model)
     with Post => KM.Sum (X, KM.Empty_Multiset) = X;

   procedure Lemma_Sum_Congruent (X, Y, Z : Model)
     with Pre => X = Y, Post => KM.Sum (X, Z) = KM.Sum (Y, Z);

   procedure Lemma_Sum_Assoc (X, Y, Z : Model)
     with Post => KM.Sum (KM.Sum (X, Y), Z) = KM.Sum (X, KM.Sum (Y, Z));

   procedure Lemma_Sum_Add (X, Y : Model; E : Key_Type)
     with Post => KM.Sum (X, KM.Add (Y, E)) = KM.Add (KM.Sum (X, Y), E);
   --  The law that carries a node's own key out through the sum of its two
   --  subtrees, and so the one every step of a recursive merge needs.

   procedure Lemma_Sum_Add_Left (X, Y : Model; E : Key_Type)
     with Post => KM.Sum (KM.Add (X, E), Y) = KM.Add (KM.Sum (X, Y), E);
   --  The same law on the other operand. A merge of two runs moves one key
   --  at a time out of a sum of what is left of each of them, and which of
   --  the two it comes from decides which of these two it needs.

   procedure Lemma_Sum_Empty_Left (X : Model)
     with Post => KM.Sum (KM.Empty_Multiset, X) = X;

   procedure Lemma_Sum_Symmetric (X, Y : Model)
     with Post => KM.Sum (X, Y) = KM.Sum (Y, X);

   -----------------------
   -- Array-level lemmas --
   -----------------------

   procedure Lemma_Same_Prefix (A, B : Key_Array; Lst : Extended_Index)
     with Pre  => A'First = 1
                  and then B'First = 1
                  and then Lst <= A'Last
                  and then Lst <= B'Last
                  and then (for all J in 1 .. Lst => A (J) = B (J)),
          Post => Occurrences (A, Lst) = Occurrences (B, Lst),
          Subprogram_Variant => (Decreases => Lst);
   --  Two arrays that agree on their first Lst slots have the same model

   procedure Lemma_Set (A, R : Key_Array; I : Index; Lst : Extended_Index)
     with Pre  => A'First = 1
                  and then R'First = 1
                  and then A'Last = R'Last
                  and then Lst <= A'Last
                  and then I <= Lst
                  and then (for all J in 1 .. Lst =>
                              (if J /= I then R (J) = A (J))),
          Post => KM.Add (Occurrences (R, Lst), A (I))
                  = KM.Add (Occurrences (A, Lst), R (I)),
          Subprogram_Variant => (Decreases => Lst);
   --  Overwriting a single slot exchanges one key for another in the model.
   --  The statement is deliberately symmetric — adding the discarded key on
   --  one side and the new key on the other — so that it needs no
   --  precondition about the discarded key still being present.

   procedure Lemma_Range_Is_Prefix (A : Key_Array; Lst : Extended_Index)
     with Pre  => A'First = 1 and then Lst <= A'Last,
          Post => Occurrences_In (A, 1, Lst) = Occurrences (A, Lst),
          Subprogram_Variant => (Decreases => Lst);
   --  A range that starts at the first slot is a prefix

   procedure Lemma_Range_Same
     (A, B : Key_Array; Fst : Positive; Lst : Extended_Index)
     with Pre  => A'First = 1
                  and then B'First = 1
                  and then Lst <= A'Last
                  and then Lst <= B'Last
                  and then (for all J in Fst .. Lst => A (J) = B (J)),
          Post => Occurrences_In (A, Fst, Lst) = Occurrences_In (B, Fst, Lst),
          Subprogram_Variant => (Decreases => Lst);
   --  Two arrays that agree over a range have the same model of it

   procedure Lemma_Range_Peel
     (A : Key_Array; Fst : Positive; Lst : Extended_Index)
     with Pre  => A'First = 1 and then Fst <= Lst and then Lst <= A'Last,
          Post => Occurrences_In (A, Fst, Lst)
                  = KM.Add (Occurrences_In (A, Fst + 1, Lst), A (Fst)),
          Subprogram_Variant => (Decreases => Lst);
   --  A range can be taken apart at its low end as well as at its high one.
   --  A merge writes its output from the high end downwards, so the region it
   --  has already filled grows one slot at a time at its *low* end, and this
   --  is the law that step needs.

   procedure Lemma_Range_Split
     (A : Key_Array; Mid : Extended_Index; Lst : Extended_Index)
     with Pre  => A'First = 1 and then Mid <= Lst and then Lst <= A'Last,
          Post => Occurrences (A, Lst)
                  = KM.Sum (Occurrences (A, Mid),
                            Occurrences_In (A, Mid + 1, Lst)),
          Subprogram_Variant => (Decreases => Lst);
   --  A prefix splits into a shorter prefix and the range above it. This is
   --  what turns the two live regions a merge leaves in the array back into
   --  the plain prefix model the rest of the collection speaks.

   procedure Lemma_Swap
     (A, R : Key_Array; I, J : Index; Lst : Extended_Index)
     with Pre  => A'First = 1
                  and then R'First = 1
                  and then A'Last = R'Last
                  and then Lst <= A'Last
                  and then I < J
                  and then J <= Lst
                  and then R (I) = A (J)
                  and then R (J) = A (I)
                  and then (for all M in 1 .. Lst =>
                              (if M /= I and M /= J then R (M) = A (M))),
          Post => Occurrences (R, Lst) = Occurrences (A, Lst),
          Subprogram_Variant => (Decreases => Lst);
   --  Exchanging the contents of two slots leaves the model alone. This is
   --  what makes a swap-based sift cheap to verify: the whole model argument
   --  of an operation reduces to the one slot that is genuinely added or
   --  removed, and every intermediate rearrangement is silent.

end Heaps.Models;
