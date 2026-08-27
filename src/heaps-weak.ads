--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Weak heap stored implicitly in an array, with one extra bit per node.
--
--  A weak heap is a binary tree that has been relaxed in exactly one place:
--  a node dominates its right subtree only, and is unrelated to its left
--  subtree. The root of the whole structure is kept apart, at index 1: it has
--  no left subtree, so it dominates everything, and it is the minimum.
--
--  The relaxation buys the tree the freedom to exchange the two subtrees of a
--  node at no cost, which is what makes the structure worth having: a sift
--  step never has to look at two children and pick the smaller one, as a
--  binary heap does. It compares once, and if the comparison goes the wrong
--  way it swaps the two keys and swaps the two subtrees of the node -- which
--  turns the subtree it knows nothing about into the one it now dominates.
--  One comparison per level instead of two is the whole point of the
--  structure; the price is the bit that records, for each node, which of its
--  two array slots currently counts as the left one.
--
--  The children of the node at index I are the slots 2 * I - 1 and 2 * I, as
--  in a binary heap; the flip bit of I says which of the two is the left one.
--  The parent of I is therefore (I - 1) / 2 + 1 whatever the bits say, and the
--  shape of the tree is that of a binary heap. Only the labelling of the
--  children moves.
--
--  Because a node does not dominate its left subtree, the node a given node is
--  answerable to is not its parent but its distinguished ancestor: climb from
--  the node while it is a left child, then take one more step. That ancestor
--  is what Da computes, and the heap ordering is stated against it.
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

package Heaps.Weak with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Flip_Array is array (Index range <>) of Boolean
     with Default_Component_Value => False;
   --  One bit per node, saying whether its two children have been exchanged.
   --  Like the keys, the bits are default-initialized so that the slots past
   --  the end of the heap can be read without further ado.

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
      Flip : Flip_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). The slots beyond Last are
   --  irrelevant; they keep whatever value they last held.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Parent (I : Index) return Extended_Index is
     (if I = 1 then 0 else (I - 1) / 2 + 1)
     with Post => (if I = 1 then Parent'Result = 0
                   else Parent'Result in 1 .. I - 1);
   --  Index of the parent of I, or 0 at the root. The flip bits do not enter
   --  into it: they permute the children of a node, they do not move them.

   function Left_Child (H : Heap; I : Index) return Positive is
     (2 * I - 1 + (if H.Flip (I) then 1 else 0))
     with Pre  => I in 2 .. H.Capacity,
          Post => Left_Child'Result > I;
   --  The child of I that I does not dominate. The other child, 2 * I or
   --  2 * I - 1, is the right one. Index 1 is excluded because the root of the
   --  structure has a right subtree only.

   function Is_Left_Child (H : Heap; I : Index) return Boolean is
     (I > 2 and then I = Left_Child (H, Parent (I)))
     with Pre => I <= H.Capacity;
   --  Index 2 is the right child of index 1 by convention, which is what gives
   --  the root of the structure its special status.

   function Da (H : Heap; I : Index) return Extended_Index is
     (if I = 1 then 0
      elsif Is_Left_Child (H, I) then Da (H, Parent (I))
      else Parent (I))
     with Ghost,
          Pre  => I <= H.Capacity,
          Post => (if I = 1 then Da'Result = 0 else Da'Result in 1 .. I - 1),
          Subprogram_Variant => (Decreases => I);
   --  The distinguished ancestor of I: the lowest ancestor of I that has I in
   --  its right subtree. It is the node that answers for I, in the way that
   --  the parent answers for a node in a binary heap.

   function Is_Ancestor (X : Natural; I : Index) return Boolean is
     (X = I or else (X in 1 .. I - 1 and then Is_Ancestor (X, Parent (I))))
     with Ghost,
          Post => (if Is_Ancestor'Result then X <= I),
          Subprogram_Variant => (Decreases => I);
   --  Whether X is I or one of its ancestors. X ranges over Natural rather
   --  than Index so that a child index, which may fall past the end of the
   --  array, can be tested without a guard.

   function Is_Heap (H : Heap) return Boolean is
     (for all I in 2 .. H.Last => H.Keys (Da (H, I)) <= H.Keys (I))
     with Ghost;
   --  The weak heap ordering: no node is smaller than its distinguished
   --  ancestor. Stated per node, this is the same shape of invariant as a
   --  binary heap's; what differs is that the node it points at is further
   --  away, and that it moves when a flip bit does.

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
   --  The heap seen as what it really is: a bag of keys. The layout, the
   --  ordering and the flip bits are implementation detail; the contracts
   --  below pin down the observable behaviour entirely in terms of this
   --  multiset.

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
   --  The ordering only relates a node to its distinguished ancestor; that the
   --  first node is a lower bound of the whole array follows by induction
   --  along the chains of distinguished ancestors, which all end at it.

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Weak;
