--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Pairing heaps sharing one arena.
--
--  A pairing heap is a multiway tree in heap order with no rank, no balance
--  condition and no shape invariant. Merging two trees compares their roots
--  and hangs the loser on the winner as its first child, so insertion and
--  meld are O(1). Extraction pays for all of it: removing the root leaves its
--  children as a list of trees, which is folded back into one in two passes,
--  left to right merging disjoint pairs and then right to left folding the
--  results. A single left-to-right pass instead leaves one long spine for the
--  next extraction to walk again.
--
--  A node holds its first child and its next sibling, so the multiway tree is
--  stored as a binary one. Heap order is then a clause about a node and its
--  child link alone: a sibling is an equal, not an inferior.
--
--  A tree is named by the index of its root, and every operation takes that
--  name `in out`. `Heaps.Pairing_Pool` is the library-level instance.
--
--  The model of a tree is cached, one multiset per node, rather than defined
--  by recursion over the tree: a recursive model reads the whole pool, so
--  every mutation would owe a proof about the trees it does not touch. A node
--  caches the keys of itself, of its descendants and of everything to its
--  right along its sibling list. A root has no siblings, so the cache of a
--  root is the model of the tree.

--  The ghost model cannot reasonably be evaluated at run time, and the
--  contracts are discharged by proof, so assertions are disabled here.

--  Snap'Old appears inside the implications of the frame clauses, so it is
--  formally "potentially unevaluated", the case this pragma exists for.

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;

generic
   Capacity : Index;
   --  The number of nodes the arena holds, shared by every tree in it

package Heaps.Pairing with SPARK_Mode is

   use type Key_Multisets.Multiset;

   subtype Tree is Extended_Index range 0 .. Capacity;
   --  A tree of the arena, named by the index of its root. 0 is the empty
   --  tree, and is a valid value of every operation that takes one.

   subtype Slot is Tree range 1 .. Capacity;
   --  A node of the arena. The range is a subtype rather than a precondition
   --  because these predicates appear under an implication inside a
   --  quantifier, where an expression function guarded by a precondition does
   --  not unfold.

   ---------------------------
   -- Structural properties --
   ---------------------------

   --  The arena is package state, so a contract needs a name for "the arena
   --  before the call": every ghost property below reads a Snapshot, and Snap
   --  is the current one. 'Old may not be applied to an expression mentioning
   --  a quantified variable, so `Model (U)'Old` inside a `for all U` is
   --  illegal where `Model (Snap'Old, U)` is fine, and the frame clauses are
   --  all of that shape.

   type Snapshot is private with Ghost;

   function Snap return Snapshot with Ghost;

   function Valid (S : Snapshot) return Boolean with Ghost;
   --  S is well formed: every node in use is a well formed node of a
   --  heap-ordered multiway tree whose cached model agrees with its links',
   --  and every node not in use is on the free chain.

   function In_Use (S : Snapshot; I : Slot) return Boolean with Ghost;

   function Is_Root (S : Snapshot; T : Tree) return Boolean with Ghost;
   --  T names a tree: either the empty tree, or a node in use that hangs from
   --  nothing and has nothing beside it.

   function Model (S : Snapshot; T : Tree) return Key_Multisets.Multiset
     with Ghost;
   --  The multiset of the keys held in T: a lookup of the cache of T's root,
   --  not a scan.

   function Size_In (S : Snapshot; T : Tree) return Extended_Index with Ghost;
   --  The number of nodes in T

   function Room_In (S : Snapshot) return Extended_Index with Ghost;

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type) return Boolean
     with Ghost;
   --  K is a lower bound of every key held in T

   --  Shorthands for the current state

   function Valid return Boolean is (Valid (Snap)) with Ghost;
   function Is_Root (T : Tree) return Boolean is (Is_Root (Snap, T))
     with Ghost;
   function Model (T : Tree) return Key_Multisets.Multiset is
     (Model (Snap, T)) with Ghost;

   Nodes : constant Extended_Index := Capacity;
   --  How many nodes the arena holds altogether, free and in use. A generic
   --  formal object is not visible outside its instance, so a client needs
   --  this to compare Room against it.

   function Room return Extended_Index;
   --  How many more keys the arena can hold, over all its trees together

   function Size_Of (T : Tree) return Extended_Index
     with Pre  => Valid and then Is_Root (T),
          Post => (Size_Of'Result = 0) = (T = 0);

   function Is_Empty (T : Tree) return Boolean is (T = 0);

   ----------------
   -- Operations --
   ----------------

   procedure Clear
     with Post => Valid and Room = Capacity;
   --  Empty the arena. Every tree in it ceases to exist, so every name the
   --  caller holds becomes stale.

   function Peek_Min (T : Tree) return Key_Type
     with Pre => Valid and then Is_Root (T) and then T /= 0;

   procedure Insert (T : in out Tree; K : Key_Type)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Room >= 1
                  and then Size_Of (T) < Capacity,
          Post => Valid
                  and Is_Root (T)
                  and Room = Room'Old - 1
                  and Size_In (Snap, T) = Size_In (Snap'Old, T'Old) + 1
                  and Model (Snap, T)
                      = Key_Multisets.Add (Model (Snap'Old, T'Old), K)

                  --  The other trees are untouched: with a cached model
                  --  that is one equality per root.

                  and (for all U in Tree =>
                         (if U /= T'Old and then Is_Root (Snap'Old, U)
                          then Is_Root (Snap, U)
                               and then Model (Snap, U) = Model (Snap'Old, U)));

   procedure Extract_Min (T : in out Tree; K : out Key_Type)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then T /= 0
                  and then Room < Capacity,
          Post => Valid
                  and Is_Root (T)
                  and Room = Room'Old + 1
                  and K = Peek_Min (T)'Old
                  and Is_Minimum (Snap'Old, T'Old, K)
                  and Model (Snap'Old, T'Old)
                      = Key_Multisets.Add (Model (Snap, T), K)
                  and (for all U in Tree =>
                         (if U /= T'Old and then Is_Root (Snap'Old, U)
                          then Is_Root (Snap, U)
                               and then Model (Snap, U) = Model (Snap'Old, U)));

   --  Room < Capacity says the arena is not wholly empty. T /= 0 makes that
   --  obvious, but deriving it needs a counting argument over the free chain
   --  that the flat invariant is built to avoid, so it is asked of the
   --  caller.

   procedure Meld (T : in out Tree; U : in out Tree)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Is_Root (U)
                  and then (if T /= 0 and then U /= 0 then T /= U)
                  and then Size_Of (T) + Size_Of (U) <= Capacity,
          Post => Valid
                  and Is_Root (T)
                  and U = 0
                  and Room = Room'Old
                  and Model (Snap, T)
                      = Model (Snap'Old, T'Old) + Model (Snap'Old, U'Old)
                  and (for all W in Tree =>
                         (if W /= T'Old
                             and then W /= U'Old
                             and then Is_Root (Snap'Old, W)
                          then Is_Root (Snap, W)
                               and then Model (Snap, W) = Model (Snap'Old, W)));
   --  Destructive meld: T receives every key of U, which ceases to exist. No
   --  node is allocated, freed or copied, and the work is one comparison and
   --  four assignments for operands of any size.
   --
   --  The size bound is asked of the caller rather than derived: that two
   --  trees of an arena hold at most Capacity keys between them is a counting
   --  argument over disjoint nodes, and the invariant here is flat -- it
   --  relates a node to its immediate neighbours and says nothing about which
   --  nodes belong to which tree.

private

   type Link is record
      Child   : Extended_Index := 0;
      Sibling : Extended_Index := 0;
      Parent  : Extended_Index := 0;
      Size    : Extended_Index := 0;
   end record;
   --  The tree structure of one node, kept apart from its key. The children
   --  of a node are its Child and that node's Sibling chain. For a node on
   --  the free chain, Child is the next free node and the rest is irrelevant.
   --
   --  Parent is whichever node names this one: the parent of a first child,
   --  or the sibling before it in a child list. Under that reading the three
   --  links satisfy the same local clauses as a binary tree's.
   --
   --  Size rules out a cycle -- a node holds one more node than its two links
   --  do, so two nodes naming each other would have to hold more than they
   --  hold -- which is how the fold knows the nodes it relinks are distinct.
   --  No branch reads it.

   type Link_Array is array (Index range <>) of Link;

   type Model_Array is array (Index range <>) of Key_Multisets.Multiset
     with Ghost;

   type Chain_Array is array (Index range <>) of Extended_Index with Ghost;

   type Snapshot is record
      Keys       : Key_Array (1 .. Capacity);
      Links      : Link_Array (1 .. Capacity);
      Free       : Extended_Index := 0;
      Free_Count : Extended_Index := 0;
      Sub        : Model_Array (1 .. Capacity);
      Chain_Pos  : Chain_Array (1 .. Capacity);
      Chain_At   : Chain_Array (1 .. Capacity);
   end record;
   --  A whole arena as one value, for contracts to compare two states. SPARK
   --  has no ghost components, so the real state is kept as separate
   --  variables and Snap assembles them.

   --  Real state

   Keys       : Key_Array (1 .. Capacity);
   Links      : Link_Array (1 .. Capacity);
   Free       : Extended_Index := 0;
   Free_Count : Extended_Index := 0;

   --  Ghost state, erased at run time

   Sub : Model_Array (1 .. Capacity) with Ghost;
   --  Sub (I) is the multiset of the keys of I, of its descendants and of
   --  its siblings and theirs. At a root, whose sibling list is empty, it is
   --  the model of the tree.

   Chain_At : Chain_Array (1 .. Capacity) with Ghost;
   --  The inverse of Chain_Pos: Chain_At (K) is the node at position K. Two
   --  arrays that are inverses give injectivity in one step, where stating it
   --  directly needs a quantifier over pairs of nodes inside Valid.

   Chain_Pos : Chain_Array (1 .. Capacity) with Ghost;
   --  0 if the node is in use, otherwise its one-based position along the
   --  free chain counting from the far end, so the head holds Free_Count. As
   --  Size does for a tree, a value that strictly decreases from a node to
   --  the next rules out a cycle without recursion or induction.

   function Snap return Snapshot is
     ((Keys       => Keys,
       Links      => Links,
       Free       => Free,
       Free_Count => Free_Count,
       Sub        => Sub,
       Chain_Pos  => Chain_Pos,
       Chain_At   => Chain_At));

   function In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Chain_Pos (I) = 0);

   function Sub_Of (S : Snapshot; I : Tree)
                    return Key_Multisets.Multiset
   is
     (if I = 0 then Key_Multisets.Empty_Multiset else S.Sub (I))
     with Ghost;

   function Size_Of_Node (S : Snapshot; I : Tree)
                          return Extended_Index
   is
     (if I = 0 then 0 else S.Links (I).Size)
     with Ghost;

   --  Accessors for the current state. Size_Now is not ghost because the
   --  assignments keeping Size up to date are real code.

   function Size_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Size);

   function Sub_Now (I : Tree) return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else Sub (I))
     with Ghost;

   function Node_In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Child in 0 .. Capacity
      and then S.Links (I).Sibling in 0 .. Capacity
      and then S.Links (I).Parent in 0 .. Capacity
      and then (if S.Links (I).Child /= 0 then In_Use (S, S.Links (I).Child))
      and then (if S.Links (I).Sibling /= 0
                then In_Use (S, S.Links (I).Sibling))
      and then (if S.Links (I).Parent /= 0 then In_Use (S, S.Links (I).Parent))
      and then S.Links (I).Size
               = 1 + Size_Of_Node (S, S.Links (I).Child)
                   + Size_Of_Node (S, S.Links (I).Sibling)
      and then S.Links (I).Size <= Capacity

      --  The cached model of I is its two links' plus its own key.

      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum (Sub_Of (S, S.Links (I).Child),
                                       Sub_Of (S, S.Links (I).Sibling)),
                    S.Keys (I))

      --  Heap order is claimed against the child link only: a node is a
      --  lower bound of its descendants, which in the binary view is the
      --  sibling closure of its child, and claims nothing about the nodes
      --  beside it. A parent is ordered against its children and never one
      --  child against another, which is why a merge is four assignments.

      and then (for all E of Sub_Of (S, S.Links (I).Child) => S.Keys (I) <= E)

      --  Nothing compares a node's key with its child's: that follows from
      --  the clause above, and stating it would have to be re-derived every
      --  time a different node reaches the head of a child list.

      and then (if S.Links (I).Child /= 0
                then S.Links (S.Links (I).Child).Parent = I
                     and then S.Links (I).Child /= S.Links (I).Sibling)
      and then (if S.Links (I).Sibling /= 0
                then S.Links (S.Links (I).Sibling).Parent = I)
      and then (if S.Links (I).Parent /= 0
                then S.Links (S.Links (I).Parent).Child = I
                     or else S.Links (S.Links (I).Parent).Sibling = I))
     with Ghost;
   --  Everything asked of a node that holds a key. Every clause is about
   --  this node and its immediate neighbours, which is what lets an
   --  extraction take a child list apart and put it back together.

   function Node_Free (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Child in 0 .. Capacity
      and then S.Chain_Pos (I) in 1 .. Capacity
      and then S.Chain_Pos (I) <= S.Free_Count
      and then S.Chain_At (S.Chain_Pos (I)) = I
      and then (if S.Chain_Pos (I) = 1
                then S.Links (I).Child = 0
                else S.Links (I).Child /= 0
                     and then S.Chain_Pos (S.Links (I).Child)
                              = S.Chain_Pos (I) - 1))
     with Ghost;
   --  Everything asked of a node on the free chain: it is at some position
   --  along it, and the node it points at is one step nearer the far end.

   function Chain_Sound (S : Snapshot) return Boolean is
     (S.Free in 0 .. Capacity
      and then S.Free_Count <= Capacity
      and then (S.Free = 0) = (S.Free_Count = 0)
      and then (if S.Free /= 0 then S.Chain_Pos (S.Free) = S.Free_Count)

      --  Chain_At and Chain_Pos are inverses over the chain, so positions
      --  are unique: two free nodes at the same position are both Chain_At
      --  of it and so the same node.

      and then (for all K in 1 .. Capacity =>
                  (if K <= S.Free_Count
                   then S.Chain_At (K) in 1 .. Capacity
                        and then S.Chain_Pos (S.Chain_At (K)) = K)))
     with Ghost;

   function Nodes_Sound (S : Snapshot) return Boolean is
     (for all I in 1 .. Capacity =>
        (if In_Use (S, I) then Node_In_Use (S, I) else Node_Free (S, I)))
     with Ghost;

   function Valid (S : Snapshot) return Boolean is
     (Chain_Sound (S) and then Nodes_Sound (S));
   --  Split in two so that establishing it is two moderate goals rather
   --  than one large one. Neither half carries a precondition, since a
   --  guarded expression function does not unfold where the guard cannot be
   --  rederived; every bound they need is stated inside them.

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0
      or else (In_Use (S, T)
               and then S.Links (T).Parent = 0
               and then S.Links (T).Sibling = 0));
   --  A tree is a root when nothing hangs it below anything and nothing
   --  stands beside it. The second clause is what makes the cached model of
   --  a root the model of its tree alone, and it is what the head of a child
   --  list does not satisfy part way through an extraction.

   function Model (S : Snapshot; T : Tree) return Key_Multisets.Multiset is
     (Sub_Of (S, T));

   function Size_In (S : Snapshot; T : Tree) return Extended_Index is
     (Size_Of_Node (S, T));

   function Room_In (S : Snapshot) return Extended_Index is (S.Free_Count);

   function Room return Extended_Index is (Free_Count);

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type) return Boolean is
     (for all E of Sub_Of (S, T) => K <= E);
   --  Stated on the multiset rather than on the array: with several trees in
   --  one arena, "every key of T" is about T's model, not a range of slots.

end Heaps.Pairing;
