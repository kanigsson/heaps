--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Binary min-heap stored implicitly in an array.
--
--  The tree structure is not materialized: the children of the node stored at
--  index I are stored at 2 * I and 2 * I + 1, and its parent at I / 2. The
--  array slice 1 .. Last is therefore always a complete binary tree, and the
--  only structural property to maintain is that every node is smaller than or
--  equal to its children.

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

package Heaps.Binary with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). The slots beyond Last are
   --  irrelevant; they keep whatever value they last held.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Parent (I : Index) return Extended_Index is (I / 2)
     with Post => Parent'Result < I;
   --  Index of the parent of I, or 0 when I is the root

   function Is_Heap (H : Heap) return Boolean is
     (for all I in 2 .. H.Last => H.Keys (Parent (I)) <= H.Keys (I))
     with Ghost;
   --  The heap ordering: no node is smaller than its parent

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => K <= H.Keys (I))
     with Ghost;
   --  K is a lower bound of every key currently stored in H

   -----------
   -- Model --
   -----------

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
     with Ghost;
   --  The heap seen as a bag of keys, which is what the contracts below pin
   --  the observable behaviour down in terms of.

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

   function Min_Of (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Minimum (H, Min_Of'Result)
                  and then (for some I in 1 .. H.Last =>
                              Min_Of'Result = H.Keys (I));
   --  The minimum of the stored keys, found by a linear scan and without
   --  assuming anything about the ordering. It is a proved oracle: a test can
   --  compare it against Peek_Min without the comparison itself being a
   --  restatement of the heap property.

   procedure Lemma_Root_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, Peek_Min (H));
   --  The heap ordering only relates a node to its parent; that the root is a
   --  lower bound of the whole array follows by induction along the paths to
   --  the root, which is what this lemma establishes once and for all.

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

end Heaps.Binary;
