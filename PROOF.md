# Proof notes

What the proofs in `src/` cost, and what made the difference. The collection's
first six heaps are implicit -- the array index *is* the tree -- and their
proofs are largely mechanical. The leftist heap is the first one with an
explicit tree in a node pool, and it took roughly as long as the other six
together. These are the lessons from it, written down while they were fresh.

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
