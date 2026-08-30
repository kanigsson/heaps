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

Those two names were true when the sections were written. The private-pool unit
has since been dropped and the arena took its name, so `Heaps.Leftist` is today
what these notes call `Heaps.Leftist_Arena`. Nothing below is rewritten for it;
the last section says why the unit went.

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

# Melding the rest of the catalogue

The sections above are about the two leftist units. The ones below were written
afterwards, while filling in `Meld` for the six entries that did not have it:
the weak, min-max and interval heaps, the beap, the sorted array and
`Heaps.Leftist`. Four of the six needed nothing that was not already here. The
other two each needed one idea, and both ideas are about the shape of a
*precondition* rather than about the algorithm.

## Relativize the sift; do not write a second one

A meld on an implicit heap is an append and a bottom-up rebuild, so it needs a
sift that can be called on a node whose ancestors are not yet in order. The
binary heap already had one, because its ordering is local -- a node against
its parent -- and `Ordered_Below (H, I)` says "every subtree rooted at I or
later is a heap", which is exactly the invariant a bottom-up walk carries.

The min-max and interval heaps do not, and for a stated reason: their invariant
is domination of a *whole subtree*, because a min-max sift moves a key across
two levels and justifying the move needs bounds that the local form only yields
through the very constraint being repaired. The sift's precondition is then the
full heap property minus one node's claims -- which a half-built array does not
satisfy.

The fix is not a second sift. It is one extra parameter:

```ada
   function Heap_Except_Below
     (H : Heap; I : Extended_Index; N : Claim_Bound) return Boolean
   is
     (for all A in N .. H.Last =>
        (for all D in 1 .. H.Last =>
           (if Is_Ancestor (A, D) and then A /= I
            then Ordered (Min_Level (A), H.Keys (A), H.Keys (D)))));
```

`N` is the lowest index whose claims are in force. An extraction sifts with
`N = 1`, where the whole array claims its subtrees; a build sifts with
`N = Start`, and walks `N` down from `H.Last + 1`, where nothing claims
anything yet. `I = 0` suspends no claim at all, so `Heap_Except_Below (H, 0, 1)`
*is* `Is_Heap (H)` and the two ends of a build step are the same predicate.

What made this cheap is that the existing lemma bodies did not change. Each of
them proves its conclusion for a pair `(A, D)` out of hypotheses at that same
`A`, or at `A`'s own position in the descent -- never out of a hypothesis at
some smaller index. Restricting both the hypothesis and the conclusion to
`A >= N` is therefore sound clause by clause, and the edit is `for A in 1 ..`
becoming `for A in N ..` in three loops and two loop invariants. The min-max
heap went through on the first run after that change, meld and all.

The obvious alternative -- keep the strong invariant and rebuild by repeated
insertion -- would have been a five-line body and no proof work at all. It is
also O(m log n) instead of O(n + m), which is the comparison the whole meld
column exists to make, so it was not on offer.

## Make the bound a subtype, not a Natural

`N` above ranges over `1 .. Max_Capacity + 1`: one past the largest index, so
that a build can start from "no claim at all". Declaring it `Extended_Index`,
which starts at 0, cost three unprovable range checks -- `for A in N .. H.Last`
then admits `A = 0`, and `Is_Ancestor (A, D)` wants an `Index`. A named subtype
with the right lower bound removes them without a single assertion:

```ada
   subtype Claim_Bound is Positive range 1 .. Max_Capacity + 1;
```

Small, but it is the second time in this file that the fix for a cluster of
failed checks was a type rather than a proof.

## Two bounds, when the two halves are placed one after the other

The interval heap needs the same treatment twice over, and not with the same
value. Its invariant has two independent halves -- the low ends nest, and the
high ends nest -- and sifting one half requires the *other* half to be in
order, because a key coming down can land in the far end of a child and has to
be shown to still fit under everything above.

A bottom-up build places the low end of a node while the high end of that same
node is still unplaced. So the sift takes two bounds:

```ada
   procedure Sift_Down
     (H : in out Heap; Start : Index; Min_Side : Boolean;
      N : Claim_Bound := 1; NO : Claim_Bound := 1)
```

and the build calls it as `Sift_Down (H, M, True, M, M + 1)` -- the side being
sifted claims from `M` on, the side that is not claims only from `M + 1` on --
and then `Sift_Down (H, M, False, M, M)`, the high end sifted against a low
side that is now in order.

One hypothesis of the step lemma had to be weakened for that to hold. It said
that the far end of the child is no better than the end of the parent that did
not move, which is a fact about the other half's nesting at the node being
sifted -- exactly the claim the first call does not have. What is true instead
is a disjunction:

```ada
   After.Keys  (Slot (L, not Min_Side, C))
   = Before.Keys (Slot (L, not Min_Side, C))
   or else Ordered (not Min_Side,
                    Before.Keys (Slot (L, not Min_Side, I)),
                    After.Keys  (Slot (L, not Min_Side, C)))
```

Either the child's far end did not move, and the nodes above it bound it as
they did before; or it took the key that came down, which the parent bounded.
Splitting the lemma's case analysis along that disjunction is the whole change,
and it is one that would have been invisible without the build: for a sift that
starts at the root with both bounds at 1, the first disjunct is never needed.

## A merge needs a range model, and it needs to run backwards

The sorted array is the only entry whose meld is a merge of two runs, and the
note in README.md predicted what it would cost: the multiset model of this
collection is `Occurrences (A, Lst)`, a scan of an array *prefix*, and halfway
through a merge the array has live keys in two regions with a hole between
them. `Heaps.Models` gained a range model and four lemmas:

- `Occurrences_In (A, Fst, Lst)`, the model of a range;
- `Lemma_Range_Is_Prefix`, which ties it back to `Occurrences`;
- `Lemma_Range_Same`, the frame;
- `Lemma_Range_Peel`, which takes a range apart at its *low* end -- the one the
  prefix model has no analogue of, and the one every step of the merge needs,
  because the merged region grows downwards;
- `Lemma_Range_Split`, which turns the two regions back into the prefix the
  postcondition speaks.

Plus three multiset laws that had not come up before: `Sum` is symmetric, `Sum`
has a left identity, and an `Add` comes out of the *left* operand of a `Sum` as
well as the right. All three are `is null`.

Running the merge backwards -- taking the smaller of the two remaining minima
and writing it at the far end of what is left to fill, working towards the
front -- is
what keeps the array to two live regions rather than three. The output slot is
always `I + J`, which is above the part of `Into`'s own run still to be read,
so no key is ever copied out of the way and the "already consumed, not yet
overwritten" region of the prediction never exists. That is an algorithm choice
made for the proof, and it is also the faster of the two directions.

The model step itself is one `Add` travelling out of a three-way sum, and it is
worth recording how literally the proof has to be spelled. `A + B + C` is
`Sum (Sum (A, B), C)`, multiset equality is extensional rather than structural,
and so *every* rewrite under a `Sum` needs its own congruence call. The step
that worked is nine lemma calls and five assertions for what is, informally,
"one key moved from one bag to another". The pattern that found the gaps was to
assert the goal in each branch of the `if` rather than after it: an assertion
that fails inside one branch says which of the two cases is missing a lemma,
where the same assertion after the branch says only that something is.

## What did not need anything

Three of the six were routine, and it is worth saying which and why.

The **weak heap**'s ordering is local again -- a node against its distinguished
ancestor -- so its build carries the same shape of invariant the binary heap's
does, and the single exchange lemma the insertion already had is exactly the
step of the build. The whole meld is an append, a downward walk, and two
assertions naming which node answers to which ancestor after a join.

The **beap** does not rebuild at all. Its insertion is O(sqrt n) and a
bottom-up rebuild of a beap is O(n ** 1.5), so inserting the keys one at a time
is the better algorithm as well as the shorter proof: a loop around `Insert`,
four lemma calls for the model, and it went through on the first run.

`Heaps.Leftist`'s meld is a copy of one pool into another and then the merge it
already had. Every clause of `Well_Linked` is about a node and its immediate
neighbours -- the first lesson in this file -- so a copied node satisfies it
exactly because the original did, with each index shifted by the number of
slots already in use. There is no new invariant; there is only a lot of
instantiating.

## Split the subprogram when its two halves stop talking to each other

That last one is where the remaining time went, and the lesson is about proof
engineering rather than about heaps.

The copy and the merge share nothing. The copy is a claim about every slot in
the pool; the merge is a claim about two roots. Written as one procedure, every
verification condition in the copy carried the merge's context and every one in
the merge carried the copy's, and the effect was not linear: assertions that
had been discharged in a second started timing out, and adding a *ghost
snapshot of the key array* -- inert code, erased at run time -- was enough on
its own to push four checks that had passed back into failure.

Splitting the copy out into a `Graft` procedure with a contract of its own
fixed it. The contract is the interface between the two halves and is worth
reading as a summary of what a meld on a private pool actually is:

```ada
   procedure Graft
     (Into : in out Heap; From : Heap; B_Root : out Extended_Index)
     with Post => Well_Linked (Into)
                  and then Size_Of (Into, Into.Root)
                           + Size_Of (Into, B_Root) = Into.Count
                  and then (for all X in 1 .. Into.Count =>
                              (if Into.Links (X).Parent = 0
                               then X = Into.Root or else X = B_Root))
                  and then Model (Into) = Model (Into)'Old + Model (From);
```

"The pool holds a forest of exactly two trees, and here are their roots." That
is precisely `Merge`'s precondition, which was written for the merge inside
`Extract_Min` and needed no change. `Meld` is then four statements.

The general rule this is a case of: a large proof obligation is not the sum of
its parts, so the cheapest thing to try when assertions that used to pass stop
passing is not another assertion but a subprogram boundary.

# Dropping the private pool

The sections above are written against a catalogue that held two leftist units,
one with a pool per heap and one with a pool per instantiation, and they name
the first of them `Heaps.Leftist`. It is not in the catalogue any more: the
arena took its name, and the sections that discuss the private pool now discuss
a unit that was deleted. They are left as they were written, because what they
record is what those proofs cost, and that does not stop being true when the
code goes.

The reason for the deletion is measured rather than formal -- an O(m) copy in
the operation the structure exists for, priced in OBSERVATIONS.md -- but the
proof effort points the same way, and it is worth recording why.

## The obligations of a private pool are the obligations of a copy

A meld between two pools is a copy and a splice. The splice was free: every
clause of `Well_Linked` is about a node and its immediate neighbours, so a
copied node satisfies it exactly because the original did, and `Merge`'s
precondition -- the pool holds a forest of exactly two trees, and here are
their roots -- was already written for the merge inside `Extract_Min`. The copy
was the whole cost, in the proof as in the run time, and its last nine checks
never came down.

What made them expensive was stating the model of the pool on entry. The copy
loop's postcondition compares the new model against the old one, and there is
nowhere cheap to keep the old one:

- `Model (Into)'Old` applies an attribute to a function of the whole record, so
  a copy of the pool travels through every obligation of the loop;
- a ghost parameter carrying it in would keep the obligations small, and SPARK
  has no ghost formal of a non-ghost subprogram (LRM 6.9(7));
- ghost package state would work and is what the arena does -- but a heap that
  owns its pool has no package state to put it in, which is the point of the
  shape.

So the private pool ends up paying, in every obligation of its meld, for the
one thing the arena gets for nothing. That is the same trade the benchmark
measures, seen from the other side: what the arena buys with the loss of a
first-class object is a place to put the state that both the code and the proof
need.

## The rule

When a structure's defining operation spans two containers, the containers are
the wrong boundary. Put the storage where the operation is, and the proof
follows the algorithm rather than fighting it.

# The second arena

Everything above was written about one explicit-tree unit. `Heaps.Skew` is the
second, and it is the first chance to find out whether any of it was about
leftist heaps in particular or about arenas in general. The answer is the point
of this section, so it goes first: the skew heap needed **no new proof work at
all**. It was written by taking the leftist unit, deleting the rank field, and
replacing the conditional exchange of a node's two subtrees with an
unconditional one. It proved at `--level=4` on the first attempt, and not one
assertion was added, removed or moved.

Both bodies carry the same 26 `Assert` and `Loop_Invariant` pragmas. The skew
body is nine lines of code shorter and the spec ten, which is the rank field
and nothing else: the field itself, the two clauses of the node invariant that
maintained it, the accessor that read it, the two assignments that kept it up
to date, and the branch that consulted it.

## A weaker structure is not a harder proof

This is worth stating plainly because the opposite is the intuition. A skew
heap keeps a strictly weaker promise than a leftist heap -- its right spine is
bounded only in amortized terms, so no single merge has a worst-case bound --
and it is natural to expect a proof to get harder as the structure it describes
gets looser.

It gets easier, and the reason is what the contracts say. Not one of them
mentions the shape of the tree. They speak of a multiset of keys, a size, a set
of roots, and a free count; the deepest structural claim in the unit is that a
node's cached model is its two children's plus its own key. The leftist
condition never appears in a postcondition because no caller can observe it --
it is a claim about *cost*, and cost is not what these contracts are for. So
the clauses that maintain it are pure overhead as far as the proof is
concerned, and removing them removes obligations without removing anything that
another obligation depended on.

The corollary is the useful part. In this collection an asymptotic guarantee is
proved by construction and by measurement, not by contract: nothing in `src/`
states a bound on any operation's running time. A structure whose invariant
exists only to support such a bound therefore pays for it in every proof
obligation touching that invariant and is repaid in none. That is a reason to
expect the *pairing* heap and the *skew binomial* heap to be cheaper proofs
than their bounded siblings too, and a reason to be suspicious of the reverse
expectation.

## What the flat invariant was worth

The section *Keep the invariant flat* argued for a node-local invariant on the
grounds that it keeps each obligation small. Porting the unit shows a second
benefit that was not the reason for the choice: a flat invariant is
*editable*. Every clause of `Node_In_Use` is about one node and its immediate
neighbours, so deleting the two that mention the rank is a local edit with no
consequences elsewhere -- nothing else in the predicate is stated in terms of
them, and nothing in the body re-derives them.

A recursive invariant would not have behaved that way. "This is a leftist tree"
is a statement about a subtree, so weakening it to "this is a heap-ordered
tree" changes the induction that every proof over the structure runs, and every
obligation that unfolded the old definition has to be re-examined against the
new one. The flat version has no induction to change.

## Numbers

154 checks against the leftist unit's 165. The eleven that are gone are the
rank field's, and they are spread over the range check on the field, the two
invariant clauses, and the obligations of the branch that read it.

`--level=4` discharges all 154 in 30 seconds on this machine, from a clean
session. `--level=2` leaves exactly one: the postcondition of `Merge`, reported
as a prover timeout rather than as a missing argument. Measured the same way,
the leftist arena leaves 1 of 165, and it is the same check in the same place
-- its own `Merge` postcondition. That is why both arenas are proved at
`--level=4` while the implicit heaps are content with `--level=2`.

The section *What the arena added* reports that one check as the postcondition
of `Clear`, which is where it landed when that section was written. It moved
when `Clear`'s ghost arrays became aggregates, for the reason the section *An
aggregate is a proof convenience and a run-time cost* gives; the count is
unchanged and the level it needs is unchanged.

"Cleaned properly" is not a throwaway. `heaps.gpr` sets `Proof_Dir`, so the
why3 sessions live outside the object directory and `gnatprove --clean` does
not remove them. A `--level=2` run after a `--level=4` run therefore replays
the level-4 results and reports success at level 2 for checks level 2 cannot
prove. The section *Proof level* above records the caching caveat; this is the
sharper version of it, and it reported a false success twice before the proof
directory was removed by hand.

## What the pair is for

Two units that differ in one design decision and agree in everything else are
worth more than either alone, in two places outside the proof.

`heaps_test` drives both arenas through the same tests. Because they present
the same interface and claim the same contracts, the tests are written once as
a generic and instantiated twice; the formal subprograms bind to each arena's
operations directly, since a tree is a subtype of `Extended_Index` in both and
a generic formal subprogram asks only for mode conformance. The two then serve
as each other's oracle -- they build very different trees out of the same keys,
so an agreeing wrong answer would have to be a coincidence reproduced exactly.

And the benchmark can price the rank field, which is the one measurement in the
collection with everything else held fixed. OBSERVATIONS.md has it: a quarter
to a third faster wherever extraction dominates, and losing by up to a factor
of 1.8 wherever insertion into a large tree does.

# The third arena

`Heaps.Pairing` is the third explicit-tree unit and the first whose tree is
multiway. The section *A weaker structure is not a harder proof* above ends
with a prediction -- that a structure whose invariant exists only to support an
asymptotic bound pays for it in every obligation and is repaid in none, so the
*pairing* heap should be a cheaper proof than its bounded siblings. Half of
that came true and half of it did not, and the half that did not is the
interesting one.

## The invariant was cheaper, exactly as predicted

The node record is the leftist and skew node with two fields renamed: a node
names its first child and its next sibling instead of its left and right
subtree. That is the child-sibling correspondence, and under it a multiway tree
*is* a binary tree, so every clause of `Node_In_Use` carries over unchanged --
the size, the cached model, the parent agreement, the distinctness of the two
links.

One clause changes and it changes in the cheap direction. The binary arenas
require a node to dominate both of its links; this one requires it to dominate
its child link only, because a node's siblings are the other children of its
parent and a pairing heap never orders one child against another. Writing that
out:

```ada
--  skew
and then (for all E of S.Sub (I) => S.Keys (I) <= E)
--  pairing
and then (for all E of Sub_Of (S, S.Links (I).Child) => S.Keys (I) <= E)
```

A weaker hypothesis in the invariant is a weaker hypothesis everywhere it is
used, which normally costs something. It costs nothing here for the reason the
skew section gives: no postcondition in the unit mentions the shape of the
tree, and the one that comes closest -- the root is a lower bound of its
tree -- reads the *root's* clause, where the sibling list is empty and the two
readings coincide.

One clause also went away, and it is worth recording as a rule.
`S.Keys (I) <= S.Keys (S.Links (I).Child)` was in the invariant, copied from
the binary arenas. It is *implied* by the quantified clause above, because a
child's own key occurs in the child's cached multiset, so it added nothing --
and it cost a great deal, because an operation that puts a *different* node at
the head of a child list has to re-derive it from scratch, where the quantified
clause survives untouched on the grounds that the list still holds the same
keys. A redundant conjunct in an invariant is not free: it is an extra
obligation at every point that re-establishes the invariant, discharged from
whatever happens to be at hand.

## The algorithm was not cheaper, and the reason is the stack

The prediction was about the invariant, and the invariant is where it held. It
said nothing about the *operations*, and this is the unit where they cost more
than both predecessors put together.

The first version was the direct one. Extraction detached the root's children
as a free-standing list and handed it to a recursive `Merge_Pairs` with the
size of the list as its variant, in the shape the algorithm is always written
in: take two nodes off the front, merge them, recurse on the rest, merge the
two results. It proved at `--level=2`, which is *better* than either binary
arena manages, and it was worthless:

```
$ ./deep
filled, size 1048576
raised STORAGE_ERROR : stack overflow or erroneous memory access
```

A root that has taken n insertions has n children, because that is what O(1)
insertion means here, so the first extraction after a fill recurses n / 2 deep.
The skew arena's header carries a caveat about recursion depth that nothing in
the benchmark ever triggered; the pairing heap triggers it on the first
extraction of every workload in the suite. A proof of termination is not a
bound on the stack, and the difference is not academic.

## Fusing in place, so that nothing above has to be repaired

Turning the fold into two loops is where the work went, and the shape it
settled into is worth writing down, because the obvious shape does not work.

The obvious shape detaches the pair it is about to merge. That is what the skew
arena's merge does and what the recursive version here did, and it is fine at
the *head* of a list and nowhere else: a node in the middle of a child list has
a predecessor whose cached multiset covers it, so cutting it out leaves that
predecessor's cache stale, and its predecessor's, and so on up to the node the
list hangs from. Detaching costs O(depth) repair, which is the walk the cached
model exists to avoid.

So the fold's primitive does not detach. `Fuse` merges a list element with the
one after it and puts the winner back in the same place, and its postcondition
is the whole design:

```ada
and then Links (P).Parent  = Prev
and then Links (P).Sibling = Rest
and then Links (P).Size    = Snap'Old.Links (A).Size
and then Sub (P)           = Snap'Old.Sub (A)
```

The result stands exactly where its first operand stood and caches exactly what
it cached. A fusion is therefore invisible from anywhere above it, and two
consequences follow that between them pay for the whole rewrite. Nothing up the
list needs repairing, and neither loop carries a multiset of its own -- the
model of the fold is *nothing at all*, because the node the list hangs from is
above every pair the fold touches and its cache is preserved by every step.

That second consequence is why `Extract_Min` no longer detaches its root's
children before folding them. It folds them with the root still in place and
releases it afterwards, purely so that there is a node above the list for the
frame to be stated about. The multiset reasoning of the entire operation is
then one lemma call in `Extract_Min`, against the chain of eight in the version
that folded a free-standing list.

## The regress that a position array breaks

The second pass walks *back up* the list, fusing the last two elements over and
over, and that walk needs a fact the flat invariant cannot supply: that the
node above the one it is standing on is itself on the list and has a
predecessor. `Valid` says that a node with a parent is either that parent's
child or its sibling, which is exactly the ambiguity in question, and every
attempt to carry the fact as a loop invariant regresses by one level per step --
to know about `Parent (Cur)` you must already know about `Parent (Parent (Cur))`.

The device that breaks it is the one the free chain already uses. A ghost array
gives each node its position along the list, 0 for a node not on it, with one
quantified invariant:

```ada
(for all X in 1 .. Capacity =>
   (if Depth (X) /= 0
    then In_Use (Snap, X)
         and then Links (X).Parent /= 0
         and then (if Depth (X) = 1
                   then Links (X).Parent = Root
                        and then Links (Root).Child = X
                   else Links (Links (X).Parent).Sibling = X
                        and then Depth (Links (X).Parent) = Depth (X) - 1)))
```

A statement about *all* nodes has no regress to run: the node above one at
depth d is at depth d - 1, is on the list by the same clause, and the walk
stops at depth 1, where the predecessor is the node the list hangs from and
nowhere else. It is `Chain_Pos` for a child list, and it plays the same part --
a value that decreases by one from a node to its predecessor, ruling out both a
cycle and an exit into another tree, with no reachability relation and no
induction. The first pass builds it as it goes; being ghost, it costs nothing
at run time.

The second pass's variant is that same depth, decreasing. The first pass's is
the size of what is left of the list, which needs its own small argument: a
fusion puts one node back where two came off, so `2 * Rank + Size_Now (Cur)`
never exceeds the size of the list, which is what bounds the number of
positions the ghost array is asked to hold.

## Cycles are ruled out by the size field, and it takes four equations

`Fuse` touches five nodes -- the two fused, the one before, the one after, and
the child the loser is pushed in front of -- and every clause it re-establishes
needs them to be distinct. None of that distinctness is in the invariant. All
of it follows from the size field, because a node's size is one more than its
two links' and a cycle would make some node hold more nodes than it holds:

```ada
pragma Assert (Links (A).Size = 1 + Size_Now (Links (A).Child) + Links (B).Size);
pragma Assert (Links (B).Size = 1 + Size_Now (Links (B).Child) + Size_Now (Rest));
pragma Assert (Links (Prev).Size >= 1 + Links (A).Size);
```

Three facts, and every pair of the four is distinct by linear arithmetic. The
third is the one that took longest to find: it says only that A is one of the
predecessor's two links, and it is what closes the three-node cycles that the
first two leave open.

Two things about this were worth the time they cost. The first is that the size
field, which exists in these units so that the *contracts* can state their
effect on a tree's size, turns out to be what rules out cycles -- an
acyclicity argument for free, from a field that was added for another purpose,
where the alternative is a reachability predicate. The second is that three of
these assertions were false before they were true, because a `/=` between two
indices is vacuously false when both are 0 and the empty-list cases were not
guarded. GNATprove reported them as timeouts rather than as counterexamples,
which is the least helpful way to be told that what you asked for is not true;
the tell was that adding time did not help.

## Numbers

361 checks, against the skew unit's 154 and the leftist unit's 165. The
difference is not the structure, it is the fold: `Fuse` and `Fold_Children`
together carry 77 `Assert` and `Loop_Invariant` pragmas, and the body 109,
where each binary arena's whole body has 26.

`--level=4` discharges all 361 in a little under three minutes on this machine,
from a session cleaned by hand for the reason the section above records. That
is five times the skew arena's 30 seconds, and the same two subprograms are
where it goes. `--level=2` leaves
five, all of them the same clause of `Node_In_Use` -- the size equation -- in
`Fuse`. That puts the pairing arena where the other two are: proved at
`--level=4`, and the implicit heaps content with `--level=2`.

The recursive version of the fold, before the stack made it unusable, needed
206 checks and proved every one at `--level=2`. The 155 checks and two proof
levels between that version and this one are what an iterative fold over a
linked list costs, and none of them is about pairing heaps.

## What the prediction should have said

The skew section's rule was: a structure whose invariant exists only to support
an asymptotic bound pays for that invariant in every obligation and is repaid
in none. It is still right, and the pairing heap's invariant is the cheapest of
the three arenas for exactly that reason.

What it missed is that removing structure from the *invariant* can add
structure to the *algorithm*. A leftist heap's shape invariant bounds its
spine, and the bound is what lets its merge be a recursion of depth log n that
nothing in a proof has to say anything about. The pairing heap has no shape
invariant to bound anything, so the same recursion is of depth n, so the fold
must be iterative, so the walk up the list needs a position array and the loops
need a page of invariants apiece. The cost did not disappear when the invariant
did. It moved from the predicate to the program.

The sharper rule, then: an invariant that only supports an asymptotic bound is
not paid for in the proof, but the bound it supports may be. Where the
structure's guarantee is what keeps a recursion shallow, dropping it does not
buy a cheaper proof -- it buys a different program, and the proof follows the
program.
