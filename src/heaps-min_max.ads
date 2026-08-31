--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Min-max heap stored implicitly in an array: a double-ended priority queue.
--
--  The tree is laid out exactly as in a binary heap -- the children of I are
--  at 2 * I and 2 * I + 1 -- but the levels alternate in role. Nodes on an
--  even depth (the root, its grandchildren, ...) are *min nodes* and hold the
--  smallest key of their subtree; nodes on an odd depth are *max nodes* and
--  hold the largest key of their subtree. The minimum of the whole heap is
--  therefore at the root and the maximum is the larger of its two children,
--  and both can be extracted in logarithmic time.

--  The ghost model, a multiset built by recursion over the key array, cannot
--  reasonably be evaluated at run time, and the contracts are discharged by
--  proof, so assertions are disabled here.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Min_Max with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). The slots beyond Last are
   --  irrelevant; they keep whatever value they last held.

   ---------------------------
   -- Shape of the tree     --
   ---------------------------

   function Parent (I : Index) return Extended_Index is (I / 2)
     with Post => Parent'Result < I;
   --  Index of the parent of I, or 0 when I is the root

   function Grandparent (I : Index) return Extended_Index is (I / 2 / 2)
     with Post => Grandparent'Result < I;
   --  Two levels up, or 0 near the root. Written as two halvings rather than
   --  as a division by four so that every property of it follows from the
   --  corresponding property of Parent, with no extra reasoning about
   --  integer division.

   function Min_Level (I : Index) return Boolean is
     (if I = 1 then True else not Min_Level (I / 2))
     with Ghost, Subprogram_Variant => (Decreases => I);
   --  Whether I sits on a min level. The levels alternate, so this is the
   --  parity of the depth of I; the recursive form is the one the proofs
   --  reason with. Is_Min_Level below is the executable counterpart.

   function Is_Min_Level (I : Index) return Boolean
     with Post => Is_Min_Level'Result = Min_Level (I);
   --  Same predicate, computed by halving I until the root is reached rather
   --  than by recursion, which is what the operations actually call.

   function Is_Ancestor (A, D : Index) return Boolean is
     (A = D or else (D > 1 and then Is_Ancestor (A, D / 2)))
     with Ghost,
          Subprogram_Variant => (Decreases => D),
          Post => (if Is_Ancestor'Result and then A /= D then 2 * A <= D);
   --  A is D or one of the nodes on the path from D to the root. Ancestry
   --  depends on the indices alone, so it is unaffected by anything the
   --  operations do to the keys.
   --
   --  The postcondition -- a proper descendant lies at least one level down --
   --  is carried by the function rather than by a separate lemma because
   --  almost every proof in the unit needs it, and needs it for indices the
   --  prover picks itself.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Ordered (Min_Side : Boolean; A, B : Key_Type) return Boolean is
     (if Min_Side then A <= B else B <= A);
   --  A comes before B on the given side. Every ordering constraint in this
   --  unit is stated through this function, which is what lets the two
   --  symmetric halves of a min-max heap share one implementation and one
   --  proof instead of two mirror images of each.

   function Better (Min_Side : Boolean; A, B : Key_Type) return Boolean is
     (if Min_Side then A < B else B < A);
   --  A is strictly preferable to B on the given side

   function Is_Heap (H : Heap) return Boolean is
     (for all A in 1 .. H.Last =>
        (for all D in 1 .. H.Last =>
           (if Is_Ancestor (A, D)
            then Ordered (Min_Level (A), H.Keys (A), H.Keys (D)))))
     with Ghost;
   --  The min-max ordering, stated the way it is used: every min node is a
   --  lower bound and every max node an upper bound of its whole subtree.
   --
   --  The local property -- each node against its parent and its grandparent
   --  -- is equivalent, but it is the wrong invariant to carry: a sift step
   --  moves a key across two levels, and justifying the move needs bounds on
   --  the subtree that the local property only yields through the constraint
   --  the step is repairing.

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => K <= H.Keys (I))
     with Ghost;
   --  K is a lower bound of every key currently stored in H

   function Is_Maximum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => H.Keys (I) <= K)
     with Ghost;
   --  K is an upper bound of every key currently stored in H

   -----------
   -- Model --
   -----------

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
     with Ghost;
   --  The heap seen as a bag of keys.

   ----------------
   -- Operations --
   ----------------

   function Size (H : Heap) return Extended_Index is (H.Last);

   function Is_Empty (H : Heap) return Boolean is (H.Last = 0);

   function Is_Full (H : Heap) return Boolean is (H.Last = H.Capacity);

   procedure Clear (H : in out Heap)
     with Post => Is_Empty (H)
                  and Is_Heap (H)
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type is (H.Keys (1))
     with Pre => not Is_Empty (H);

   function Max_Index (H : Heap) return Index is
     (if H.Last = 1 then 1
      elsif H.Last = 2 then 2
      elsif H.Keys (3) > H.Keys (2) then 3
      else 2)
     with Pre  => not Is_Empty (H),
          Post => Max_Index'Result <= H.Last;
   --  Where the maximum sits: the root when it is the only node, and
   --  otherwise the larger of the two max nodes just below it.

   function Peek_Max (H : Heap) return Key_Type is (H.Keys (Max_Index (H)))
     with Pre => not Is_Empty (H);

   function Min_Of (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Minimum (H, Min_Of'Result)
                  and then (for some I in 1 .. H.Last =>
                              Min_Of'Result = H.Keys (I));
   --  The minimum of the stored keys, found by a linear scan and without
   --  assuming anything about the ordering. It is a proved oracle: a test can
   --  compare it against Peek_Min without the comparison itself being a
   --  restatement of the heap property.

   function Max_Of (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Maximum (H, Max_Of'Result)
                  and then (for some I in 1 .. H.Last =>
                              Max_Of'Result = H.Keys (I));
   --  The same oracle for the other end

   procedure Lemma_Root_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, Peek_Min (H));
   --  The root dominates the whole array because every node descends from it

   procedure Lemma_Top_Is_Maximum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Maximum (H, Peek_Max (H));
   --  Every node other than the root descends from one of the two max nodes
   --  below it, and the root is a lower bound of everything, so the larger of
   --  those two is an upper bound of the whole array.

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Destructive meld: Into receives every key of From, which is left empty.
   --
   --  An implicit heap cannot splice two trees together, so this appends the
   --  keys of From and rebuilds the whole array bottom-up, which is O(n + m)
   --  where repeated insertion would be O(m log n).
   --
   --  Is_Heap (From) is required only for uniformity with the rest of the
   --  family. The rebuild does not depend on it.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

   procedure Extract_Max (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Max (H)'Old
                  and Is_Maximum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

   ------------------------------
   -- Lemmas about the shape   --
   ------------------------------

   --  Ancestry is a recursive predicate over the indices, so the handful of
   --  facts the operations need about it -- that the root is everybody's
   --  ancestor, that the path skips two levels at a time when the parity is
   --  fixed -- have to be established by induction rather than assumed.

   procedure Lemma_Root_Is_Ancestor (D : Index)
     with Ghost, Post => Is_Ancestor (1, D),
          Subprogram_Variant => (Decreases => D);

   procedure Lemma_Below_Root (D : Index)
     with Ghost, Pre  => D > 1,
          Post => Is_Ancestor (2, D) or else Is_Ancestor (3, D),
          Subprogram_Variant => (Decreases => D);

   procedure Lemma_Ancestor_Transitive (A, B, D : Index)
     with Ghost, Pre  => Is_Ancestor (A, B) and then Is_Ancestor (B, D),
          Post => Is_Ancestor (A, D),
          Subprogram_Variant => (Decreases => D);

   procedure Lemma_Skip_Level (A, D : Index)
     with Ghost,
          Pre  => Is_Ancestor (A, D)
                  and then A /= D
                  and then Min_Level (A) = Min_Level (D),
          Post => D > 3 and then Is_Ancestor (A, Grandparent (D));
   --  An ancestor on the same side as D is not its parent, so it is an
   --  ancestor of its grandparent

   procedure Lemma_Grandparent_Level (D : Index)
     with Ghost, Pre  => D > 3,
          Post => Min_Level (Grandparent (D)) = Min_Level (D)
                  and then Grandparent (D) >= 1;

end Heaps.Min_Max;
