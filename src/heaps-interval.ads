--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Interval heap stored implicitly in an array: a double-ended priority
--  queue.
--
--  Consecutive slots are paired into the nodes of a complete binary tree:
--  node N occupies the slots 2 * N - 1 and 2 * N, and its children are the
--  nodes 2 * N and 2 * N + 1. The two slots of a node are read as a closed
--  interval, and the interval of a node contains the intervals of all its
--  descendants. The smallest key of the heap is therefore the low end of the
--  root and the largest is its high end; both ends are available at once, and
--  each can be removed in logarithmic time.
--
--  When the number of keys is odd the deepest node holds a single key, which
--  then serves as both ends of a degenerate interval. Slot below is what
--  makes that case disappear from the rest of the unit: it maps a node and a
--  side to the slot holding that end, and for a lone key it maps both sides
--  to the same slot.
--
--  Compared with a min-max heap, which alternates the role of whole levels,
--  an interval heap keeps the two roles side by side in every node. A sift
--  then walks the tree one level at a time instead of two, and compares
--  against children rather than against children and grandchildren.
--
--  Verification level: silver, gold and platinum -- see README.md.

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
with Heaps.Models;

package Heaps.Interval with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). The slots beyond Last are
   --  irrelevant; they keep whatever value they last held.

   -------------------
   -- Shape of the tree
   -------------------

   function Node_Count (H : Heap) return Extended_Index is ((H.Last + 1) / 2);
   --  Number of nodes in use. The last one holds a single key when Last is
   --  odd, and two keys otherwise.

   function Parent (N : Index) return Extended_Index is (N / 2)
     with Post => Parent'Result < N;
   --  The node above N, or 0 when N is the root

   function Node_Of (P : Index) return Index is ((P + 1) / 2)
     with Post => 2 * Node_Of'Result - 1 <= P and then P <= 2 * Node_Of'Result;
   --  The node the slot P belongs to

   function Slot
     (Lst : Extended_Index; Min_Side : Boolean; N : Index) return Index
   is
     (if Min_Side or else 2 * N > Lst then 2 * N - 1 else 2 * N)
     with Pre  => N <= (Lst + 1) / 2,
          Post => Slot'Result <= Lst
                  and then 2 * N - 1 <= Slot'Result
                  and then Slot'Result <= 2 * N;
   --  Where the given end of node N is stored, in a heap holding Lst keys.
   --  A node that holds a single key has both of its ends in the same slot,
   --  and every property below then degenerates to something trivially true
   --  rather than to a case of its own.
   --
   --  The parameter is the number of keys rather than the heap because the
   --  lemmas of the body compare two states of the same heap, and stating
   --  that the slot layout is common to both is easier than deriving it.

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
   --  symmetric halves of an interval heap share one implementation and one
   --  proof instead of two mirror images of each.

   function Better (Min_Side : Boolean; A, B : Key_Type) return Boolean is
     (if Min_Side then A < B else B < A);
   --  A is strictly preferable to B on the given side

   function Is_Paired (H : Heap) return Boolean is
     (for all N in 1 .. Node_Count (H) =>
        H.Keys (Slot (H.Last, True, N)) <= H.Keys (Slot (H.Last, False, N)))
     with Ghost;
   --  Each node is a well-formed interval: its low end does not exceed its
   --  high end

   function Nested_On (H : Heap; Min_Side : Boolean) return Boolean is
     (for all A in 1 .. Node_Count (H) =>
        (for all D in 1 .. Node_Count (H) =>
           (if Is_Ancestor (A, D)
            then Ordered (Min_Side,
                          H.Keys (Slot (H.Last, Min_Side, A)),
                          H.Keys (Slot (H.Last, Min_Side, D))))))
     with Ghost;
   --  On the given side, every node dominates its whole subtree. The two
   --  sides are stated separately rather than as one property over both
   --  because a sift only ever disturbs one of them, and the proofs then name
   --  the side that is at stake.

   function Is_Nested (H : Heap) return Boolean is
     (Nested_On (H, True) and then Nested_On (H, False))
     with Ghost;
   --  The interval of a node contains the intervals of its descendants

   function Is_Heap (H : Heap) return Boolean is
     (Is_Paired (H) and then Is_Nested (H))
     with Ghost;

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
   --  The heap seen as what it really is: a bag of keys, shared with every
   --  other heap kind in the collection.

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
     (Slot (H.Last, False, 1))
     with Pre  => not Is_Empty (H),
          Post => Max_Index'Result <= H.Last;
   --  Where the maximum sits: the high end of the root, which is the second
   --  slot unless the root is the only node and holds a single key.

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
   --  Every slot belongs to a node the root dominates, and the low end of a
   --  node does not exceed its high end, so the low end of the root is below
   --  the whole array

   procedure Lemma_Root_Is_Maximum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Maximum (H, Peek_Max (H));
   --  The same argument on the other side

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
   --  keys of From and rebuilds the whole array bottom-up, which is O(n + m).
   --  Rebuilding an interval heap takes one pass more than rebuilding a
   --  binary one: the appended keys have to be paired into well-formed
   --  intervals before either end can be sifted at all.
   --
   --  Is_Heap (From) is required only for uniformity with the rest of the
   --  family. The rebuild does not depend on it.

   procedure Build (H : in out Heap)
     with Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old
                  and Model (H) = Model (H)'Old;
   --  Restore the interval-heap invariant after Keys (1 .. Last) have been
   --  filled in arbitrary order. This is the linear bottom-up construction
   --  used by Meld, exposed so adaptive proved queues can defer ordering
   --  without duplicating the heapification algorithm or its proof.

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

   --  Ancestry is a recursive predicate over the node indices, so the facts
   --  the operations need about it have to be established by induction rather
   --  than assumed.

   procedure Lemma_Root_Is_Ancestor (D : Index)
     with Ghost, Post => Is_Ancestor (1, D),
          Subprogram_Variant => (Decreases => D);

   procedure Lemma_Ancestor_Transitive (A, B, D : Index)
     with Ghost, Pre  => Is_Ancestor (A, B) and then Is_Ancestor (B, D),
          Post => Is_Ancestor (A, D),
          Subprogram_Variant => (Decreases => D);

end Heaps.Interval;
