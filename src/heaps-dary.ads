--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  d-ary min-heap stored implicitly in an array.
--
--  The generalization of the binary heap: every node has Arity children
--  instead of two. The children of the node stored at index I are stored at
--  Arity * (I - 1) + 2 .. Arity * I + 1, and its parent at
--  (I + Arity - 2) / Arity. For Arity = 2 those are the familiar 2 * I,
--  2 * I + 1 and I / 2.
--
--  The trade is depth against fan-out. The tree is log Arity times
--  shallower, so sift-up, which only compares a node with its parent, does
--  that many fewer comparisons and moves, while sift-down has to find the
--  smallest of Arity children at every level.
--
--  The arity is a discriminant rather than a generic parameter, so a single
--  proof covers every arity at once.

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

package Heaps.Dary with SPARK_Mode is

   use type Key_Multisets.Multiset;

   subtype Arity_Type is Positive range 2 .. 64;
   --  The number of children of a node. Bounded above so that the index of a
   --  child, which multiplies an index by the arity, stays in Integer range.

   subtype Child_Index is Positive range 2 .. Arity_Type'Last * Max_Capacity;
   --  Where the index of a first child lives. It is deliberately wider than
   --  Index: the first child of a node near the end of the array is a
   --  perfectly well defined number that simply does not name a slot.

   type Heap (Capacity : Extended_Index; Arity : Arity_Type) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). The slots beyond Last are
   --  irrelevant; they keep whatever value they last held.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Parent (Arity : Arity_Type; I : Index) return Extended_Index is
     ((I + Arity - 2) / Arity)
     with Post => Parent'Result < I and then (Parent'Result = 0) = (I = 1);
   --  Index of the parent of I, or 0 when I is the root

   function First_Child (Arity : Arity_Type; I : Index) return Child_Index is
     (Arity * (I - 1) + 2)
     with Post => First_Child'Result > I;
   --  Index of the leftmost child of I. The children of I are the Arity
   --  consecutive indices starting there.

   function Is_Heap (H : Heap) return Boolean is
     (for all I in 2 .. H.Last => H.Keys (Parent (H.Arity, I)) <= H.Keys (I))
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
   --  The heap seen as what it really is: a bag of keys. The array layout,
   --  the arity, the ordering and the traversal order are implementation
   --  detail; the contracts below pin down the observable behaviour entirely
   --  in terms of this multiset, and are word for word the ones the binary
   --  heap carries.

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

   procedure Lemma_Child_Range (Arity : Arity_Type; P, J : Index)
     with Ghost,
          Post => (Parent (Arity, J) = P)
                  = (J >= First_Child (Arity, P)
                     and then J - First_Child (Arity, P) < Arity);
   --  Being the parent and being one of the Arity consecutive slots starting
   --  at the first child are the same relation. This is the one place where
   --  the integer division hidden in Parent has to be unfolded; everything
   --  else in this unit reasons through this equivalence.

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
     with Pre  => Into.Arity = From.Arity
                  and then Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Destructive meld: Into receives every key of From, which is left empty.
   --  Word for word the binary heap's operation and, like it, an append
   --  followed by a bottom-up rebuild at O(n + m). The arities have to agree:
   --  two heaps of different arity have different tree shapes, so there is no
   --  meaning to give the result.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Dary;
