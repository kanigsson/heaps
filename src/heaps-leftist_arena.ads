--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Leftist heaps sharing one arena.
--
--  Heaps.Leftist exports a Heap that bundles a node pool together with the
--  assertion that the pool holds exactly one tree. That is what makes melding
--  two of them expensive: the two operands live in two disjoint arrays, so one
--  of them has to be copied into the other before its root can be spliced in,
--  and an O(m) copy throws away the O(log n) the structure exists for.
--
--  Here the pool is package state and a heap is a root inside it, so several
--  heaps share one array and a meld is the splice and nothing else. The price
--  is that a heap is no longer a first-class object: there is one arena per
--  instantiation, no array of arenas and no passing one to a subprogram. For a
--  collection of mergeable structures and a benchmark that is the right way
--  round, since the k operands of a k-way meld are k trees in one arena rather
--  than k arenas.
--
--  A tree is named by the index of its root, and a root changes whenever the
--  tree is operated on -- a merge returns one of its two operands as the new
--  root -- so every operation takes its tree as `in out` and the caller keeps
--  the updated name.

--  The model of a tree is *cached*, one multiset per node, rather than defined
--  by recursion over the tree. That is the whole reason this unit's invariant
--  can stay as flat as Heaps.Leftist's. A recursive model reads the entire
--  pool, so every mutation owes a proof that the trees not being touched still
--  have the model they had, and stating that means saying which nodes belong
--  to which tree -- exactly the subtree-level reasoning that PROOF.md reports
--  having avoided. A cached model is a field of a node, so a tree's model is a
--  field of its root, and a mutation that leaves a root alone leaves its model
--  alone for free.
--
--  The cache is maintained by one clause of Valid about one node and its two
--  immediate children, which is the same shape as the clause that maintains
--  Size, and it is maintained by the same three assignments. SPARK has no
--  ghost record components and no ghost parameters of non-ghost subprograms
--  (LRM 6.9(7)), so the cache cannot ride along inside the node or be passed
--  in; ghost package state is the one place it can live, and it is erased at
--  run time like every other ghost object here.

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

package Heaps.Leftist_Arena with SPARK_Mode is

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
   --  the call" to a ghost function the way Heaps.Leftist passes H'Old. It
   --  needs a name for that state instead, and Snapshot is it: every ghost
   --  property below reads one, and Snap names the current one. This is not
   --  decoration -- 'Old may not be applied to an expression mentioning a
   --  quantified variable, so `Model (U)'Old` inside a `for all U` is illegal
   --  where `Model (Snap'Old, U)` is fine, and the frame clauses of this unit
   --  are all of that shape.

   type Snapshot is private with Ghost;

   function Snap return Snapshot with Ghost;
   --  The arena as it stands

   function Valid (S : Snapshot) return Boolean with Ghost;
   --  S is well formed: every node in use is a well formed leftist node whose
   --  cached model agrees with its children's, and every node not in use is on
   --  the free chain.

   function In_Use (S : Snapshot; I : Slot) return Boolean with Ghost;
   --  I holds a node of some tree

   function Is_Root (S : Snapshot; T : Tree) return Boolean with Ghost;
   --  T names a tree: either the empty tree, or a node in use with no parent

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
   --  The size bound is asked of the caller rather than derived. That two
   --  distinct trees of an arena of Capacity nodes hold at most Capacity keys
   --  between them is true, but it is a counting argument about their nodes
   --  being disjoint, and the invariant here is deliberately flat: it relates
   --  a node to its immediate neighbours and says nothing about which nodes
   --  belong to which tree. PROOF.md reaches the same conclusion about the
   --  same arithmetic and gives the same answer -- carry the bound in the
   --  contract, where it is pure arithmetic, rather than derive it from the
   --  invariant. A caller always knows how many keys it put in.
   --
   --  Destructive meld, and the point of the unit: T receives every key of U,
   --  which ceases to exist. No node is allocated, freed or copied -- Room is
   --  unchanged -- and the work is a walk down the two right spines, so this
   --  is O(log n) rather than the O(m) a heap owning its own pool must pay.

private

   type Link is record
      Left   : Extended_Index := 0;
      Right  : Extended_Index := 0;
      Parent : Extended_Index := 0;
      Size   : Extended_Index := 0;
      Dist   : Extended_Index := 0;
   end record;
   --  The tree structure of one node, kept apart from its key. For a node on
   --  the free chain, Left is the next free node and the rest is irrelevant.

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
   --  Sub (I) is the multiset of the keys in the subtree rooted at I. It is
   --  the cache that lets a tree's model be a lookup, and it is maintained
   --  wherever Size is.

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

   function Dist_Of (S : Snapshot; I : Tree) return Extended_Index is
     (if I = 0 then 0 else S.Links (I).Dist)
     with Ghost;

   --  Accessors for the current state. The two structural ones are not ghost:
   --  a merge chooses which subtree to hang where by comparing Dist, so this
   --  is real code and not only a proof term.

   function Size_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Size);

   function Dist_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Dist);

   function Sub_Now (I : Tree) return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else Sub (I))
     with Ghost;

   function Node_In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Left in 0 .. Capacity
      and then S.Links (I).Right in 0 .. Capacity
      and then S.Links (I).Parent in 0 .. Capacity
      and then (if S.Links (I).Left /= 0 then In_Use (S, S.Links (I).Left))
      and then (if S.Links (I).Right /= 0 then In_Use (S, S.Links (I).Right))
      and then (if S.Links (I).Parent /= 0 then In_Use (S, S.Links (I).Parent))
      and then S.Links (I).Size
               = 1 + Size_Of_Node (S, S.Links (I).Left)
                   + Size_Of_Node (S, S.Links (I).Right)
      and then S.Links (I).Dist = 1 + Dist_Of (S, S.Links (I).Right)
      and then S.Links (I).Dist <= S.Links (I).Size
      and then S.Links (I).Size <= Capacity
      and then Dist_Of (S, S.Links (I).Left)
               >= Dist_Of (S, S.Links (I).Right)

      --  The cached model of I is its two children's plus its own key. One
      --  clause, one node, two children -- and it is what makes a tree's
      --  model a field of its root rather than a recursion over its nodes.

      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum (Sub_Of (S, S.Links (I).Left),
                                       Sub_Of (S, S.Links (I).Right)),
                    S.Keys (I))

      --  And every key of I's subtree is at least I's own. Because the model
      --  is cached this is a clause about one node, so "the root is the
      --  minimum" needs no walk up the parent links: it falls out of the
      --  invariant at the root itself.

      and then (for all E of S.Sub (I) => S.Keys (I) <= E)

      and then (if S.Links (I).Left /= 0
                then S.Links (S.Links (I).Left).Parent = I
                     and then S.Keys (I) <= S.Keys (S.Links (I).Left)
                     and then S.Links (I).Left /= S.Links (I).Right)
      and then (if S.Links (I).Right /= 0
                then S.Links (S.Links (I).Right).Parent = I
                     and then S.Keys (I) <= S.Keys (S.Links (I).Right))
      and then (if S.Links (I).Parent /= 0
                then S.Links (S.Links (I).Parent).Left = I
                     or else S.Links (S.Links (I).Parent).Right = I))
     with Ghost;
   --  Everything asked of a node that holds a key. Every clause is about this
   --  node and its immediate neighbours; nothing here is a statement about a
   --  subtree, and nothing says how many trees the arena holds, which is what
   --  lets a merge take the forest apart and put it back together.

   function Node_Free (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Left in 0 .. Capacity
      and then S.Chain_Pos (I) in 1 .. Capacity
      and then S.Chain_Pos (I) <= S.Free_Count
      and then S.Chain_At (S.Chain_Pos (I)) = I
      and then (if S.Chain_Pos (I) = 1
                then S.Links (I).Left = 0
                else S.Links (I).Left /= 0
                     and then S.Chain_Pos (S.Links (I).Left)
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

   --  Every bound a clause needs for its own indexing is stated in that
   --  clause. Free_Count <= Capacity is a separate conjunct and is not
   --  available inside one, so a position is bounded by Capacity there and
   --  compared with Free_Count separately.

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0 or else (In_Use (S, T) and then S.Links (T).Parent = 0));

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

end Heaps.Leftist_Arena;
