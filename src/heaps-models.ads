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

end Heaps.Models;
