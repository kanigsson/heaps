# Proof notes

What the proofs in `src/` cost, and what made the difference. The collection's
first six heaps are implicit -- the array index *is* the tree -- and their
proofs are largely mechanical. The leftist heap is the first one with an
explicit tree in a node pool, and it took roughly as long as the other six
together. These are the lessons from it, written down while they were fresh.

The sections up to *What it added up to* are about `Heaps.Leftist`, the unit
whose `Heap` object owns its pool and holds one tree. The sections after it are
about `Heaps.Leftist_Arena`, which puts several trees in one shared pool so
that a meld can be a splice. The arena inherits the earlier lessons unchanged
-- it is the same tree, and its invariant is flat for the same reasons -- and
adds the ones that only come up once a pool holds more than one tree.

## Keep the invariant flat

The temptation with a linked structure is to describe it the way a textbook
does: "the pool holds a binary tree", "the keys in the subtree of I are all at
least Keys (I)". Both are recursive statements about a subtree, and both make
every step of a merge a frame problem about a set of nodes that is itself
defined by recursion.

None of that is necessary. The whole structural invariant of the leftist heap
is a conjunction of clauses about *one node and its immediate neighbours*:

```ada
   for all I in 1 .. H.Count =>
     (if H.Links (I).Left /= 0
      then H.Links (H.Links (I).Left).Parent = I
           and then H.Keys (I) <= H.Keys (H.Links (I).Left)
           and then H.Links (H.Links (I).Left).Size < H.Links (I).Size)
     ...
```

Three of those local clauses do the work that a recursive definition would:

- **A parent link rules out sharing.** A node has one `Parent` field, and a
  child has to point back at its parent. Two parents claiming the same child
  is then a contradiction between two field values, not a fact about sets.
  This is what makes a write to one node provably invisible to another.
- **A subtree size rules out cycles.** `Size` strictly decreases from a node to
  either child. A cycle would need a value smaller than itself. Well-foundedness
  is arithmetic rather than an inductive definition, and it is what makes a
  recursive ghost function terminate.
- **The used slots are the array prefix `1 .. Count`.** Allocation is a bump of
  `Count`; deallocation moves the last node into the hole. There is no free
  list, so there is no free-list invariant, and the multiset model is the same
  `Occurrences (Keys, Count)` scan the implicit heaps use. The model reasoning
  of the whole unit collapses to two calls to `Models.Lemma_Set` and
  `Models.Lemma_Same_Prefix`.

The one property that genuinely needs to reach beyond a node's neighbours is
"the root is the minimum". It is a walk up the parent links, which is a
recursive ghost procedure with `Subprogram_Variant => (Increases => ... Size)`
-- four lines, because the local clauses already say a parent holds a smaller
key and a larger subtree.

## Give a merge a contract about roots, not about subtrees

A recursive merge takes two trees apart and puts them back together, and in
between the pool is a forest. Rather than say which nodes belong to which
tree -- a subtree statement again -- `Merge` says only what it does to the set
of nodes that have no parent:

```ada
   (for all X in 1 .. H.Count =>
      (if H.Links (X).Parent = 0 and then X /= R
       then H'Old.Links (X).Parent = 0
            and then X /= A and then X /= B))
```

"I create no new roots except the one I return, and A and B are no longer
roots." Callers know their own pool has exactly two roots going in, so they
conclude it has one coming out. This composes through the recursion, which the
subtree formulation does not.

The companion clause is the frame: nodes that were roots and are not A or B
come back untouched. That is what lets the recursive step know that the node
it is holding on to -- detached, waiting for the call to return -- is still
there, and `Well_Linked` then supplies everything else about it locally. No
separate "merge only touches the subtrees of A and B" lemma is needed.

## Detach before recursing

The first version of the merge did what the textbook does: recurse, then hang
the result back on. That leaves the pool ill-formed across the call -- the node
being worked on points at a child that no longer points back -- so the
invariant could not be a precondition of the recursive call.

Cutting the right subtree loose *first*, and fixing up the node's own `Size`
and `Dist` before recursing, leaves two well-formed trees and costs three extra
assignments:

```ada
   Rest := H.Links (Top).Right;
   if Rest /= 0 then H.Links (Rest).Parent := 0; end if;
   H.Links (Top).Right := 0;
   H.Links (Top).Size  := 1 + Size_Of (H, H.Links (Top).Left);
   H.Links (Top).Dist  := 1;

   Merge (H, Rest, Other, Sub);
```

`Well_Linked` is then true at every program point in the unit except inside the
compaction, which is straight-line code. This was the single most useful
change in the whole proof.

## Bound the arithmetic through the contract, not the invariant

`Size` is a subtree count and `1 + Size (Left) + Size (Right)` has to fit in
its type. Proving `Size (I) <= Count` from the local clauses needs exactly the
counting argument the flat invariant was chosen to avoid.

The way out is to carry the bound in `Merge`'s contract instead:

```ada
   Pre  => ... Size_Of (H, A) + Size_Of (H, B) <= H.Count,
   Post => ... H.Links (R).Size = Size_Of (H'Old, A) + Size_Of (H'Old, B)
```

The postcondition is pure arithmetic through the recursion, the precondition
follows from it at every recursive call, and the range checks fall out. The
same trick bounds `Dist` via the local clause `Dist (I) <= Size (I)`.

## Expression functions with preconditions are opaque

This cost the most time for the least insight, so it is worth stating plainly.
Splitting the big `Well_Linked` predicate into named per-node pieces looked
like an obvious simplification:

```ada
   function Node_Shape (H : Heap; I : Index) return Boolean is (...)
     with Pre => I <= H.Count and then H.Links (I).Left <= H.Capacity ...;
```

It made the proof dramatically *worse* -- from four unproved checks to
thirty-one. GNATprove guards the defining axiom of an expression function by
its precondition, so `Node_Shape (H, I)` as a *hypothesis* no longer unfolds
unless the prover first re-derives the precondition, which inside a quantifier
it generally will not. Predicates that appear on both sides of an implication
should either have no precondition (push the guards into the body, behind
`and then`) or not be factored out at all.

The version that worked keeps one monolithic `Well_Linked` and does the
factoring in the *assertions* instead: prove each clause for the handful of
nodes a step touched, then for everything else, then for the whole range.

```ada
   pragma Assert (... for Last ...);
   pragma Assert (... for Gone ...);
   pragma Assert (if Up /= 0 then ... for Up ...);
   pragma Assert (for all I in 1 .. Last =>
                    (if I /= Gone and then I /= Last and then I /= Up
                     then ...));
   pragma Assert (for all I in 1 .. Last => ...);
```

Verbose, but each assertion is a small VC, and the last one is what the next
step needs. Splitting `Well_Linked` this way -- one clause group at a time,
one node group at a time -- is what took the compaction from unprovable to
routine.

## Snapshot the state a step changes

The compaction moves the last node into the hole the root leaves and tells its
three neighbours. Reasoning about it against the state *before* the move needs
that state to have a name:

```ada
   Mid : constant Heap := H with Ghost;
```

Every frame assertion is then a comparison with `Mid`, and the two facts that
make the compaction correct become one-liners: nothing but a node's parent and
its two children ever refers to it, and the moved node's own links are exactly
the ones it had. Ghost objects are erased by `Assertion_Policy (Ghost =>
Ignore)`, so a whole-heap snapshot costs nothing at run time.

## Proof level

`heaps.gpr` is proved with `--level=4`. Every implicit heap in the collection
goes through at `--level=2`; the leftist heap does not, and leaves seven checks
unproved there.

Two practical notes. GNATprove caches results, so a `--level=2` run straight
after a `--level=4` run reports success without proving anything -- the session
has to be cleaned first for the answer to mean anything. And a higher level is
useful during development even when the goal is a lower one: proving at
`--level=4` and reading which checks still fail says which assertions are
genuinely missing rather than merely slow, and several of the assertions above
were found that way and then turned out to be what a lower level needed too.

## What it added up to

`heaps-leftist.adb` is 570 lines: 154 of executable code, 229 of assertions,
43 of contract, and the rest comment and blank. Three assertion lines for every
two lines that do anything, and nearly all of them sit in two places -- the
step of `Merge` that reattaches a subtree, and the compaction in `Extract_Min`.
Neither is deep. Both are a case analysis over three or four nodes that the
prover will do only if it is told, one node at a time, which case it is in.

For comparison, the weak heap -- the last implicit one, and not a trivial
proof either -- is 440 lines and went through at `--level=2` on the first
attempt. The step up to an explicit tree is not a step up in the difficulty of
any single argument. It is a step up in how many of them there are.

## Cache the model instead of recursing over the tree

The arena holds several trees at once, and that changes what a model costs. In
`Heaps.Leftist` the model of the heap is a scan of the array prefix that holds
its nodes, because the pool holds exactly one tree and every slot in use
belongs to it. In an arena there is no such prefix: slot 7 and slot 900 may
belong to different trees, and which nodes belong to which is precisely the
subtree-level reasoning the flat invariant exists to avoid.

The obvious repair is to define a tree's model by recursion over its nodes.
That is a trap. A recursive model reads the whole pool, so every mutation owes
a proof that the trees *not* being touched still have the model they had -- and
stating that means saying which nodes belong to which tree, which is the thing
that was being avoided.

What works is to cache the model: one multiset per node, holding the keys of
the subtree rooted there, maintained by the same assignments that maintain
`Size`.

```ada
      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum (Sub_Of (S, S.Links (I).Left),
                                       Sub_Of (S, S.Links (I).Right)),
                    S.Keys (I))
```

One clause, one node, its two immediate children -- the same shape as the
clause that maintains `Size`, and maintained by the same three assignments. A
tree's model is then a *lookup*, the cache of its root, and the frame that a
recursive model could not state without a reachability relation becomes one
equality per root:

```ada
      and (for all U in Tree =>
             (if U /= T'Old and then Is_Root (Snap'Old, U)
              then Is_Root (Snap, U)
                   and then Model (Snap, U) = Model (Snap'Old, U)));
```

A mutation that leaves a root alone leaves its model alone for free. The second
dividend is that "the root is the minimum" needs no walk up the parent links:
`for all E of S.Sub (I) => S.Keys (I) <= E` is a clause about one node, so the
fact falls out of the invariant at the root itself.

SPARK has no ghost record components and no ghost parameters of non-ghost
subprograms (LRM 6.9(7)), so the cache can neither ride inside the node nor be
passed in. Ghost package state is the one place it can live.

## Name the state when the state is a package

`Heaps.Leftist` compares against `H'Old`. An arena has no `H`: the pool is
package state, and a contract cannot pass "the arena before the call" to a
ghost function. It needs a name for that state, and a private ghost record
holding all of it -- keys, links, free chain, and the ghost arrays -- is that
name.

This is not decoration. `'Old` may not be applied to an expression mentioning a
quantified variable, so inside a `for all U` the natural `Model (U)'Old` is
illegal where `Model (Snap'Old, U)` is fine -- and every frame clause in the
unit is of that shape. The snapshot type has to be ghost, which is also why the
real state cannot be an object of it: with no ghost components, a non-ghost
record could not hold the ghost arrays without making them real. So the state
stays as separate variables and one expression function assembles them.

The cost is that `Snap'Old` ends up inside the implications of the frame
clauses and is therefore formally *potentially unevaluated*, which needs
`pragma Unevaluated_Use_Of_Old (Allow)`. It is a pure function of the arena and
always well defined, which is the case that pragma exists for.

## Two inverse arrays beat a quantifier over pairs

The free chain needs two things: that it does not cycle, and that no node is on
it twice. The first is the same problem as `Size` on a tree and takes the same
answer -- a value that strictly decreases from a node to the next rules out a
cycle locally, with no recursive definition and no induction. Here that value
is the node's one-based position along the chain, counting from the far end.

Injectivity is the interesting half. Stated directly it is a quantifier over
*pairs* of nodes, and it would sit inside `Valid`, which is the hypothesis of
nearly every proof in the unit -- an O(n^2) clause paid for everywhere. Stated
as a pair of inverse arrays it is a quantifier over single nodes:

```ada
      and then (for all K in 1 .. Capacity =>
                  (if K <= S.Free_Count
                   then S.Chain_At (K) in 1 .. Capacity
                        and then S.Chain_Pos (S.Chain_At (K)) = K)))
```

Two free nodes at the same position are both `Chain_At` of it, so they are the
same node, in one step. The head is therefore the only node at the far end, and
popping it leaves every other position in range -- which is exactly what
`Allocate` needs and all it needs.

## Split a large predicate, but do not guard the halves

`Valid` is `Chain_Sound and then Nodes_Sound`. Establishing it after `Clear` as
a single goal sat on the prover's time limit: it passed when scoped to the unit
and failed in the whole-project run, from clean sessions either way, purely on
how loaded the machine was. Split in two it is two moderate goals and it is
stable.

Neither half carries a precondition, and that is deliberate -- it is the caveat
already recorded in *Expression functions with preconditions are opaque*.
Every bound a clause needs for its own indexing is stated inside that clause,
even where it duplicates a conjunct next to it: `Free_Count <= Capacity` is a
separate conjunct of `Chain_Sound` and is *not* available inside another one,
so a position is bounded by `Capacity` there and compared with `Free_Count`
separately.

## An aggregate is a proof convenience and a run-time cost

`Clear` threads every slot onto the free chain. Written as a loop it needed an
invariant, and its postcondition then rested on carrying that invariant out of
the loop -- one large goal, and the unstable one described above. Written as
iterated component associations it defines every element directly and there is
nothing to carry:

```ada
      Chain_Pos := [for J in 1 .. Capacity => J];
```

That is the right form for the three *ghost* arrays, which are erased at run
time and so cost nothing whatever shape they are in. It was the wrong form for
`Links`, and this took a run-time test to find rather than a proof: an array
aggregate is built as a whole-array temporary before being assigned, so at
`2 ** 20` nodes of twenty bytes `Clear` needed twenty megabytes of stack and
could not be called at all on a default one. Nothing had ever called it at run
time, and the proof had nothing to say about it -- stack usage is not among the
checks.

So `Links` is written slot by slot after all, and pays for one loop invariant.
The lesson is not that either form is better. It is that the proof and the
generated code want opposite things here, and that the choice can be made per
array: the arrays that only the prover reads are free to take the form the
prover likes.

## What the arena added

`heaps-leftist_arena.adb` is 482 lines against `heaps-leftist.adb`'s 570, and
its spec is 464 against 208. The weight moved from the body to the contracts,
and it moved further than those totals show: the body carries 26 `Assert` and
`Loop_Invariant` pragmas against the single-tree unit's 62, in a body five
sixths the size.

That is the trade the cached model buys, and it is a better one than expected.
The invariant clauses and the frames are longer to *write*, because they
quantify over the roots of a whole forest instead of naming one heap. But
nothing in the body has to reason about which node belongs to which tree, and
the compaction that needed the heaviest case analysis in the single-tree unit
-- moving the last node of the pool into the hole the root leaves -- does not
exist here at all, because a free chain has no hole to fill. Less than half the
assertions, for a structure that does strictly more.

At `--level=2`, from a clean session, the arena leaves exactly one check
unproved against the single-tree unit's seven -- and it is the postcondition of
`Clear`, the goal the two changes above were made for. Everything else in the
unit goes through at the level the implicit heaps use.

The two bugs the proof caught are both of one kind, and worth recording because
neither is an algorithm error. `Allocate` handed back a node before its key was
stored, and `Extract_Min` zeroed the departing root's `Size` while the node was
still in use. In both cases the algorithm was right and the arena was
momentarily *invalid* -- a node in use is required to carry a cached model
matching its key, and to have `Size` 1 when it has no children. With one heap
per pool such a window is invisible; with a shared pool the invariant has to
hold at every subprogram boundary because some other tree's operation may be
next, so the window is exactly what the proof reports.
