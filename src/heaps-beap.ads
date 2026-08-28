--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Beap (bi-parental heap) stored implicitly in an array.
--
--  A beap is not a tree. Its nodes are laid out in triangular layers: layer 1
--  holds one node, layer 2 holds two, layer L holds L, so layer L occupies the
--  indices Tri (L - 1) + 1 .. Tri (L), where Tri is the triangular number
--  L * (L + 1) / 2. A node has up to two children -- the nodes directly below
--  it and below-right of it -- and, symmetrically, up to two parents. Interior
--  nodes therefore share their children with a neighbour, which is what makes
--  the structure a grid rather than a tree.
--
--  Writing the index of a node in layer L as Tri (L - 1) + P, the arithmetic
--  comes out remarkably plain: the children of I are I + L and I + L + 1, and
--  its parents are I - L and I - L + 1. Only the nodes at the ends of a layer
--  are special, and only because one of their two relatives falls outside the
--  layer.
--
--  A layer holds L nodes instead of 2 ** L, so a beap of N nodes is about
--  sqrt (2 * N) layers deep and both operations are O (sqrt N) rather than
--  O (log N). That is asymptotically worse than any of the tree heaps here;
--  the beap is included for the shape of its invariant, not for its speed.
--
--  Because the layer of an index cannot be recovered from the index by
--  shifting, as the depth of a node in a binary heap can, the heap carries the
--  layer and the starting offset of the slot that the next insertion will use.
--  Both are maintained in constant time by Insert and Extract_Min, which keeps
--  the operations free of any search for a layer boundary.
--
--  Verification level: silver, gold and platinum -- see README.md.

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every O(sqrt n) operation into a quadratic one. Since the
--  contracts are discharged by proof, run-time checking of them is redundant,
--  so assertions are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Beap with SPARK_Mode is

   use type Key_Multisets.Multiset;

   --  Layer numbers. The bound is chosen so that every index of a heap, and
   --  the one slot past its end, lies in a layer of this range: Tri (5_793)
   --  already exceeds Max_Capacity.

   Max_Layer : constant := 6_000;

   subtype Layer_Count is Natural range 0 .. Max_Layer;
   subtype Layer_Index is Layer_Count range 1 .. Max_Layer;

   function Tri (L : Layer_Count) return Natural
     with Ghost,
          Post => 2 * Tri'Result = L * (L + 1);
   --  The L-th triangular number: the number of nodes in layers 1 .. L. It is
   --  specified by an equation that avoids a division, so that the provers see
   --  a polynomial identity rather than a rounding question.

   type Heap (Capacity : Extended_Index) is record
      Last  : Extended_Index := 0;
      Layer : Layer_Index := 1;
      Base  : Extended_Index := 0;
      Keys  : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;
   --  A heap holds Last keys in Keys (1 .. Last). Layer and Base describe the
   --  slot Last + 1, the one an insertion will fill: it sits in layer Layer,
   --  which starts just after index Base.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Layer_Of (I : Index) return Layer_Index
     with Ghost,
          Post => Tri (Layer_Of'Result - 1) < I
                  and then I <= Tri (Layer_Of'Result);
   --  The layer holding index I

   function Position (I : Index) return Positive is
     (I - Tri (Layer_Of (I) - 1))
     with Ghost,
          Post => Position'Result <= Layer_Of (I);
   --  The rank of I within its layer, from 1 to the layer number

   function Low_Parent (I : Index) return Extended_Index is
     (if Position (I) >= 2 then I - Layer_Of (I) else 0)
     with Ghost,
          Post => Low_Parent'Result < I;
   --  The parent of I above and to the left, or 0 when I starts its layer

   function High_Parent (I : Index) return Extended_Index is
     (if Position (I) < Layer_Of (I) then I - Layer_Of (I) + 1 else 0)
     with Ghost,
          Post => High_Parent'Result < I;
   --  The parent of I directly above, or 0 when I ends its layer

   function Ordered (H : Heap) return Boolean is
     (for all I in 2 .. H.Last =>
        (if Low_Parent (I) > 0 then H.Keys (Low_Parent (I)) <= H.Keys (I))
        and then
        (if High_Parent (I) > 0 then H.Keys (High_Parent (I)) <= H.Keys (I)))
     with Ghost;
   --  The beap ordering: no node is smaller than either of its parents

   function Layers_Valid (H : Heap) return Boolean is
     (H.Base = Tri (H.Layer - 1)
      and then H.Base <= H.Last
      and then H.Last < H.Base + H.Layer)
     with Ghost;
   --  Layer and Base really do describe the layer of the slot Last + 1

   function Is_Heap (H : Heap) return Boolean is
     (Layers_Valid (H) and then Ordered (H))
     with Ghost;
   --  What the operations preserve: the ordering, and the bookkeeping that
   --  lets them find a layer boundary without looking for it

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
   --  ordering and the layer bookkeeping are implementation detail; the
   --  contracts below pin down the observable behaviour entirely in terms of
   --  this multiset.

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
          Pre  => not Is_Empty (H) and then Ordered (H),
          Post => Is_Minimum (H, Peek_Min (H));
   --  The ordering only relates a node to its parents; that the first node is
   --  a lower bound of the whole array follows by induction along the paths
   --  leading up to it, which is what this lemma establishes once and for all.

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
   --  Unlike the tree heaps, the beap does not append and rebuild. A bottom-up
   --  rebuild of a beap is not linear: a node in layer L sifts down through
   --  the sqrt (n) - L layers below it, which sums to O (n ** 1.5). Inserting
   --  the keys one at a time costs O (m sqrt (n)) instead, and that is smaller
   --  for every m. The beap sides with the block-min directory here rather
   --  than with the implicit trees, and for the same reason: when insertion is
   --  cheap enough, repeated insertion *is* the better meld.
   --
   --  Is_Heap (From) is required only for uniformity with the rest of the
   --  family. The insertions do not depend on it.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Beap;
