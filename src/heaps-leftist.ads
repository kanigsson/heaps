--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Leftist heap held in an array of nodes linked by indices.
--
--  This is the first heap in the collection whose tree is explicit. The
--  earlier ones derive the shape of the tree from the position of a key in
--  the array and are therefore always perfectly balanced; a leftist heap is
--  deliberately unbalanced, so it has to say where its children are.
--
--  Everything is built around one operation: merging two heaps. Insertion
--  merges a one-node heap into the heap, and extraction merges the two
--  subtrees of the root. Merging walks down the right spine of both heaps, so
--  what has to be kept small is that spine and nothing else. That is the
--  leftist invariant: writing Dist of a node for the number of steps from it
--  to the nearest empty slot, a node's left subtree has a Dist at least as
--  large as its right subtree's. A node of Dist d then has at least 2 ** d - 1
--  descendants, so the right spine of n nodes is at most log2 (n + 1) long,
--  and a merge is O(log n) whatever the tree looks like elsewhere.
--
--  Because there are no access types here, the nodes live in an array and
--  refer to each other by index, with 0 standing for the empty tree. Three
--  things make the pool tractable to reason about, and all three are stated
--  node by node rather than over the tree as a whole:
--
--    * every node carries the index of its parent, which makes it impossible
--      for two nodes to share a child -- a node has one parent, and the link
--      has to point back;
--    * every node carries the size of its subtree, which strictly decreases
--      from a node to either of its children and so rules out a cycle;
--    * the nodes in use are exactly the array slots 1 .. Count, which makes
--      allocation a bump of Count and leaves the multiset model of the heap
--      the same plain scan of a key prefix that the implicit heaps use.
--
--  Extraction removes the root, which is rarely the last slot, so the last
--  node is moved down into the hole it leaves and its three neighbours are
--  told about it. That is what keeps the used slots a prefix.
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

package Heaps.Leftist with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Link is record
      Left   : Extended_Index := 0;
      Right  : Extended_Index := 0;
      Parent : Extended_Index := 0;
      Size   : Extended_Index := 0;
      Dist   : Extended_Index := 0;
   end record;
   --  The tree structure of one node, kept apart from its key so that the
   --  keys stay a plain Key_Array and can be modelled like every other heap's

   type Link_Array is array (Index range <>) of Link;

   type Heap (Capacity : Extended_Index) is record
      Count : Extended_Index := 0;
      Root  : Extended_Index := 0;
      Keys  : Key_Array (1 .. Capacity);
      Links : Link_Array (1 .. Capacity);
   end record
     with Predicate => Count <= Capacity;
   --  A heap holds Count keys, in the slots 1 .. Count. Which slot holds
   --  which key is up to the structure; the slots beyond Count are free.

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Size_Of (H : Heap; I : Extended_Index) return Extended_Index is
     (if I = 0 then 0 else H.Links (I).Size)
     with Pre => I <= H.Capacity;
   --  Number of nodes in the subtree of I, and zero for the empty tree

   function Dist_Of (H : Heap; I : Extended_Index) return Extended_Index is
     (if I = 0 then 0 else H.Links (I).Dist)
     with Pre => I <= H.Capacity;
   --  Steps from I down to the nearest empty slot, and zero for the empty
   --  tree. A merge follows the smaller of these, which is what bounds it.

   function Well_Linked (H : Heap) return Boolean is
     (for all I in 1 .. H.Count =>
        H.Links (I).Left in 0 .. H.Count
        and then H.Links (I).Right in 0 .. H.Count
        and then H.Links (I).Parent in 0 .. H.Count
        and then H.Links (I).Size
                 = 1 + Size_Of (H, H.Links (I).Left)
                     + Size_Of (H, H.Links (I).Right)
        and then H.Links (I).Dist = 1 + Dist_Of (H, H.Links (I).Right)
        and then H.Links (I).Dist <= H.Links (I).Size
        and then Dist_Of (H, H.Links (I).Left)
                 >= Dist_Of (H, H.Links (I).Right)
        and then (if H.Links (I).Left /= 0
                  then H.Links (H.Links (I).Left).Parent = I
                       and then H.Keys (I) <= H.Keys (H.Links (I).Left)
                       and then H.Links (I).Left /= H.Links (I).Right)
        and then (if H.Links (I).Right /= 0
                  then H.Links (H.Links (I).Right).Parent = I
                       and then H.Keys (I) <= H.Keys (H.Links (I).Right))
        and then (if H.Links (I).Parent /= 0
                  then H.Links (H.Links (I).Parent).Left = I
                       or else H.Links (H.Links (I).Parent).Right = I))
     with Ghost;
   --  The pool holds a forest: every link points at a used node, a child
   --  points back at its parent and holds a larger key and a smaller subtree,
   --  and the leftist condition holds. Every clause is about one node and its
   --  immediate neighbours; nothing here is a statement about a subtree, and
   --  nothing says how many trees there are, which is what lets a merge take
   --  the forest apart and put it back together again.

   function Is_Heap (H : Heap) return Boolean is
     (Well_Linked (H)
      and then (if H.Count = 0 then H.Root = 0 else H.Root in 1 .. H.Count)
      and then (if H.Root /= 0
                then H.Links (H.Root).Parent = 0
                     and then H.Links (H.Root).Size = H.Count)
      and then (for all I in 1 .. H.Count =>
                  (if I /= H.Root then H.Links (I).Parent /= 0)))
     with Ghost;
   --  The forest is a single tree, rooted at Root: the only node without a
   --  parent is the root, and its subtree is the whole of the pool in use.

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Count => K <= H.Keys (I))
     with Ghost;
   --  K is a lower bound of every key currently stored in H

   -----------
   -- Model --
   -----------

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Count))
     with Ghost;
   --  The heap seen as what it really is: a bag of keys. Keeping the used
   --  slots a prefix of the array is what lets the model of a linked
   --  structure be the same scan the implicit heaps use.

   ----------------
   -- Operations --
   ----------------

   function Size (H : Heap) return Extended_Index is (H.Count);

   function Is_Empty (H : Heap) return Boolean is (H.Count = 0);

   function Is_Full (H : Heap) return Boolean is (H.Count = H.Capacity);

   procedure Clear (H : in out Heap)
     with Post => Is_Empty (H)
                  and Is_Heap (H)
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type is (H.Keys (H.Root))
     with Pre => not Is_Empty (H) and then Is_Heap (H);
   --  Unlike an implicit heap, this one has to be told where its root is, so
   --  the structural invariant is part of the precondition

   function Min_Of (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Minimum (H, Min_Of'Result)
                  and then (for some I in 1 .. H.Count =>
                              Min_Of'Result = H.Keys (I));
   --  The minimum of the stored keys, found by a linear scan and without
   --  assuming anything about the structure. It is a proved oracle: a test can
   --  compare it against Peek_Min without the comparison itself being a
   --  restatement of the heap property.

   procedure Lemma_Root_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, Peek_Min (H));
   --  The ordering only relates a node to its parent; that the root is a
   --  lower bound of the whole pool follows by induction along the chains of
   --  parent links, which all end at it.

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
   --  A heap here owns its pool, so the nodes of From are not where Into can
   --  reach them: they are copied into the free slots at the end of Into's
   --  pool, shifted by the number of slots already in use, and the two roots
   --  are then merged. The merge is the O(log n) splice a leftist heap exists
   --  for, but the copy in front of it is O(m), which is the whole cost of
   --  keeping the pool private. Heaps.Leftist_Arena is the same tree with the
   --  pool shared, where the copy disappears and the meld is the splice
   --  alone.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Leftist;
