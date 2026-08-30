--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Pairing heaps sharing one arena.
--
--  A pairing heap is a single multiway tree kept in heap order and nothing
--  else: there is no rank, no balance condition and no shape invariant of any
--  kind. Two trees are merged by comparing their roots and hanging the loser
--  on the winner as its first child, which is a constant number of
--  assignments. Insertion is that merge against a one-node tree, and a meld
--  is that merge and nothing more, so all three are O(1) outright rather than
--  amortized.
--
--  Everything is therefore paid for at extraction. Removing the root leaves
--  its children as a list of trees, and how that list is folded back into one
--  is the whole algorithm. This unit does the standard two passes: left to
--  right merging the children in disjoint pairs, then right to left folding
--  the results into one. Doing it in one pass instead -- fold left to right
--  into an accumulator -- is a page shorter and is the classic way to make a
--  pairing heap slow, because the accumulator ends up as one long spine that
--  the next extraction has to walk again.
--
--  What a pairing heap is not is bounded in the worst case. A single
--  extraction can face n children and take linear time, exactly as a single
--  skew merge can walk a spine of n nodes. Its guarantee is amortized, and
--  the amortized bound on extraction is the one open question in the
--  structure: insertion, meld and peek are O(1) amortized and extraction is
--  known to be O(log n), but the tight bound on decrease-key -- the operation
--  this collection deliberately leaves out -- is still not settled.
--
--  The reason to have it here is that it is the first structure in the
--  catalogue whose tree is multiway, and the trick that makes it fit is the
--  child-sibling correspondence: a node keeps its first child and its next
--  sibling, so a multiway tree is stored as a binary one. That correspondence
--  is why this unit's node is the same record as the leftist and skew arenas'
--  and why the invariant below is very nearly the same predicate. It differs
--  in exactly one clause, and that clause is where the multiway tree is:
--  where the binary heaps order a node against both its links, this one
--  orders a node against its child link only. Its sibling is its equal, not
--  its inferior.
--
--  The arena shape -- pool as package state, a heap named by the index of its
--  root, every operation taking that name `in out` -- is the one the leftist
--  arena settled on, and the reasoning and the measurement behind it are
--  written up there. `Heaps.Pairing_Pool` is the library-level instance the
--  tests and benchmarks use.

--  The model of a tree is *cached*, one multiset per node, rather than
--  defined by recursion over the tree, for the reason the leftist arena
--  records: a recursive model reads the entire pool, so every mutation owes a
--  proof that the trees not being touched still have the model they had, and
--  stating that means saying which nodes belong to which tree. A cached model
--  is a field of a node, so a tree's model is a field of its root, and a
--  mutation that leaves a root alone leaves its model alone for free.
--
--  What is cached is the multiset of the binary view: the keys of a node, of
--  its descendants, and of everything to its right along its sibling list.
--  That is what makes the cache a clause about one node and its two links
--  again, and a root has no siblings, so at a root the two views agree and
--  the cache is the model of the tree.

--  The ghost model of these units -- a functional multiset -- cannot
--  reasonably be evaluated at run time. Since the contracts are discharged by
--  proof, run-time checking of them is redundant, so assertions are disabled
--  here whatever the compilation switches say.

--  Snap'Old appears inside the implications of the frame clauses, so it is
--  formally "potentially unevaluated". It is a pure function of the arena and
--  always well defined, which is exactly the case this pragma exists for.

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
   --  A node of the arena. Naming the range as a subtype rather than asking
   --  for it in a precondition is deliberate: these predicates appear as
   --  hypotheses under an implication inside a quantifier, and PROOF.md
   --  records that an expression function guarded by a precondition does not
   --  unfold there. A subtype carries the same information with nothing to
   --  discharge.

   ---------------------------
   -- Structural properties --
   ---------------------------

   --  The arena is package state, so a contract cannot pass "the arena before
   --  the call" to a ghost function the way a heap held in a record would pass
   --  H'Old. It needs a name for that state instead, and Snapshot is it: every
   --  ghost property below reads one, and Snap names the current one. This is
   --  not decoration -- 'Old may not be applied to an expression mentioning a
   --  quantified variable, so `Model (U)'Old` inside a `for all U` is illegal
   --  where `Model (Snap'Old, U)` is fine, and the frame clauses of this unit
   --  are all of that shape.

   type Snapshot is private with Ghost;

   function Snap return Snapshot with Ghost;
   --  The arena as it stands

   function Valid (S : Snapshot) return Boolean with Ghost;
   --  S is well formed: every node in use is a well formed node of a
   --  heap-ordered multiway tree whose cached model agrees with its links',
   --  and every node not in use is on the free chain.

   function In_Use (S : Snapshot; I : Slot) return Boolean with Ghost;
   --  I holds a node of some tree

   function Is_Root (S : Snapshot; T : Tree) return Boolean with Ghost;
   --  T names a tree: either the empty tree, or a node in use that hangs from
   --  nothing and has nothing beside it.

   function Model (S : Snapshot; T : Tree) return Key_Multisets.Multiset
     with Ghost;
   --  The multiset of the keys held in T. This is a *lookup*, not a scan or a
   --  recursion: the answer is the cache of T's root.

   function Size_In (S : Snapshot; T : Tree) return Extended_Index with Ghost;
   --  The number of nodes in T

   function Room_In (S : Snapshot) return Extended_Index with Ghost;

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type) return Boolean
     with Ghost;
   --  K is a lower bound of every key held in T

   --  Shorthands for the current state, which is what most contracts want

   function Valid return Boolean is (Valid (Snap)) with Ghost;
   function Is_Root (T : Tree) return Boolean is (Is_Root (Snap, T))
     with Ghost;
   function Model (T : Tree) return Key_Multisets.Multiset is
     (Model (Snap, T)) with Ghost;

   Nodes : constant Extended_Index := Capacity;
   --  How many nodes the arena holds altogether, free and in use. A generic
   --  formal object is not visible from outside its instance, so a client with
   --  no other way to name the arena's size cannot compare Room against it
   --  without this.

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
   --  caller holds becomes stale; this is the one operation that invalidates
   --  names it was not given.

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

                  --  The other trees of the arena are untouched. With a
                  --  cached model this is one equality per root rather than a
                  --  statement about which nodes belong to which tree.

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

   --  Room < Capacity says the arena is not wholly empty, which T /= 0 makes
   --  obvious and the flat invariant cannot show. Chain_At and Chain_Pos are
   --  inverses, so the free nodes are in bijection with 1 .. Room and a node
   --  in use leaves at most Capacity - 1 of them -- but that is pigeonhole,
   --  and counting the image of an injection is the argument this invariant
   --  is built to avoid. It is asked of the caller for the same reason the
   --  size bound on Meld is.

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
   --  The size bound is asked of the caller rather than derived, for the
   --  reason PROOF.md gives about this arithmetic: that two distinct trees of
   --  an arena of Capacity nodes hold at most Capacity keys between them is
   --  true, but it is a counting argument about their nodes being disjoint,
   --  and the invariant here is deliberately flat -- it relates a node to its
   --  immediate neighbours and says nothing about which nodes belong to which
   --  tree. A caller always knows how many keys it put in.
   --
   --  Destructive meld, and the point of the unit: T receives every key of U,
   --  which ceases to exist. No node is allocated, freed or copied -- Room is
   --  unchanged -- and unlike the two spine-walking arenas the work here is
   --  not a walk at all. One comparison and four assignments, worst case, for
   --  operands of any size.

private

   type Link is record
      Child   : Extended_Index := 0;
      Sibling : Extended_Index := 0;
      Parent  : Extended_Index := 0;
      Size    : Extended_Index := 0;
   end record;
   --  The tree structure of one node, kept apart from its key. A node names
   --  its first child and its next sibling, which is how a multiway tree fits
   --  in a fixed-size record: the children of a node are its Child and that
   --  node's Sibling chain. For a node on the free chain, Child is the next
   --  free node and the rest is irrelevant.
   --
   --  Parent is the node that names this one, whichever of the two ways it
   --  does so -- a first child's parent in the multiway tree, or the sibling
   --  before it in a child list. That is the only reading under which the
   --  three links satisfy the same local clauses as a binary tree's, and
   --  nothing in this unit needs to walk to the true multiway parent.
   --
   --  Size is here because the operations state their effect on it, because
   --  the first pass of a fold counts with it, and because it is what rules
   --  out a cycle: a node holds one more node than its two links do, so two
   --  nodes naming each other would have to hold more than they hold, and
   --  that is how the fold knows the handful of nodes it relinks are
   --  distinct. No branch in this unit reads it.

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
   --  A whole arena as one value, for contracts to compare two states. The
   --  type is ghost, so the real state cannot be an object of it -- SPARK has
   --  no ghost components, so a non-ghost record could not hold Sub and
   --  Chain_Pos without making them real. The state is therefore kept as
   --  separate variables and Snap assembles them.

   --  Real state

   Keys       : Key_Array (1 .. Capacity);
   Links      : Link_Array (1 .. Capacity);
   Free       : Extended_Index := 0;
   Free_Count : Extended_Index := 0;

   --  Ghost state, erased at run time

   Sub : Model_Array (1 .. Capacity) with Ghost;
   --  Sub (I) is the multiset of the keys of I, of its descendants, and of
   --  its siblings and theirs: the binary view of the child-sibling
   --  representation, which is the view in which the cache is maintained by a
   --  clause about one node and its two links. At a root, whose sibling list
   --  is empty, it is the model of the tree.

   Chain_At : Chain_Array (1 .. Capacity) with Ghost;
   --  The inverse of Chain_Pos: Chain_At (K) is the node at position K. Two
   --  arrays that are inverses of one another give injectivity in one step,
   --  where stating it directly needs a quantifier over pairs of nodes -- and
   --  Valid is the hypothesis of nearly every proof in the unit, so an O(n^2)
   --  clause in it is paid for everywhere.

   Chain_Pos : Chain_Array (1 .. Capacity) with Ghost;
   --  0 if the node is in use, otherwise its one-based position along the free
   --  chain counting from the far end, so that the head holds Free_Count. It
   --  plays for the free chain exactly the part Size plays for a tree: a value
   --  that strictly decreases from a node to the next rules out a cycle
   --  locally, with no recursive definition and no induction.

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

   --  Accessors for the current state. Size_Now is not ghost only because the
   --  assignments that keep a node's Size up to date are real code; the
   --  algorithm never branches on it.

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

      --  The cached model of I is its two links' plus its own key -- the same
      --  clause the binary arenas carry, because in the binary view this is
      --  the same shape of tree.

      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum (Sub_Of (S, S.Links (I).Child),
                                       Sub_Of (S, S.Links (I).Sibling)),
                    S.Keys (I))

      --  And here is the whole of the difference between this unit and the
      --  binary ones. Heap order is claimed against the child link only: a
      --  node is a lower bound of its own descendants, which in the binary
      --  view is the sibling closure of its child, and it claims nothing
      --  whatever about the nodes beside it. Its siblings are the other
      --  children of its parent, and the pairing heap orders a parent against
      --  its children and never one child against another -- which is exactly
      --  why a merge can be four assignments and why extraction is where the
      --  work is.

      and then (for all E of Sub_Of (S, S.Links (I).Child) => S.Keys (I) <= E)

      --  Nothing here compares a node's key with its child's. That would be
      --  a consequence of the clause above rather than an addition to it --
      --  a child's own key occurs in the child's cache -- and it is a
      --  consequence with a cost: an operation that puts a different node at
      --  the head of a child list has to re-derive it, where the quantified
      --  clause survives untouched because the list holds the same keys.

      and then (if S.Links (I).Child /= 0
                then S.Links (S.Links (I).Child).Parent = I
                     and then S.Links (I).Child /= S.Links (I).Sibling)
      and then (if S.Links (I).Sibling /= 0
                then S.Links (S.Links (I).Sibling).Parent = I)
      and then (if S.Links (I).Parent /= 0
                then S.Links (S.Links (I).Parent).Child = I
                     or else S.Links (S.Links (I).Parent).Sibling = I))
     with Ghost;
   --  Everything asked of a node that holds a key. Every clause is about this
   --  node and its immediate neighbours; nothing here is a statement about a
   --  subtree, and nothing says how many trees the arena holds, which is what
   --  lets an extraction take a child list apart and put it back together.

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

      --  Chain_At and Chain_Pos are inverses over the chain, which is what
      --  makes positions unique: two free nodes at the same position are both
      --  Chain_At of it, and so are the same node. The head is therefore the
      --  only node at the far end, and popping it leaves every other position
      --  in range.

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
   --  Split in two so that establishing it is two moderate goals rather than
   --  one large one. Neither half carries a precondition: PROOF.md records
   --  that factoring a predicate into named pieces *with* preconditions made
   --  a proof dramatically worse, because the defining axiom of a guarded
   --  expression function does not unfold where the guard cannot be
   --  rederived. Every bound these need is stated inside them.

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0
      or else (In_Use (S, T)
               and then S.Links (T).Parent = 0
               and then S.Links (T).Sibling = 0));
   --  Two clauses rather than the binary arenas' one. A tree is a root of the
   --  arena when nothing hangs it below anything and nothing stands beside
   --  it, and the second half is what makes the cached model of a root the
   --  model of its tree rather than of its tree and its neighbours'. It is
   --  also what an intermediate step of an extraction does *not* satisfy: the
   --  head of a child list has no parent but does have siblings, and it is a
   --  list rather than a tree until they are folded in.

   function Model (S : Snapshot; T : Tree) return Key_Multisets.Multiset is
     (Sub_Of (S, T));

   function Size_In (S : Snapshot; T : Tree) return Extended_Index is
     (Size_Of_Node (S, T));

   function Room_In (S : Snapshot) return Extended_Index is (S.Free_Count);

   function Room return Extended_Index is (Free_Count);

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type) return Boolean is
     (for all E of Sub_Of (S, T) => K <= E);
   --  Stated on the multiset rather than on the array: with several trees in
   --  one arena, "every key of T" is a statement about T's model and not
   --  about a range of slots.

end Heaps.Pairing;
