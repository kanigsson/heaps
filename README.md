# Heaps in SPARK

Verified priority queues backed by arrays. No access types.

## Implementations

| Heap | Insert | Extract | Notes |
|------|--------|---------|-------|
| Binary heap | O(log n) | O(log n) min | Binary min-heap |
| d-ary heap | O(log\_d n) | O(d log\_d n) min | Configurable arity |
| Weak heap | O(log n) | O(log n) min | One flip bit per node, half the comparisons |
| Min-max heap | O(log n) | O(log n) min or max | Double-ended queue |
| Interval heap | O(log n) | O(log n) min or max | Double-ended, two keys per node |
| Beap | O(sqrt n) | O(sqrt n) min | Triangular layers, two parents per node |
| Leftist heap | O(log n) | O(log n) min | Mergeable, explicit tree in a node pool |
| Leftist arena | O(log n) | O(log n) min | Same tree, shared pool, O(log n) meld |
| Block-min directory | O(1) | O(n / B + B) min | One winner per block, B = 256 |
| Unsorted array | O(1) | O(n) min | Baseline |
| Sorted array | O(n) | O(1) min | Baseline |

The d-ary heap's arity is a type discriminant, so one proof covers all valid
arities. The weak heap relaxes the binary heap in a single place -- a node
dominates its right subtree only -- which lets a sift step exchange the two
subtrees of a node instead of choosing between them, and halves the number of
comparisons. The two double-ended queues take opposite sides of the same
trade-off. The beap is the one structure here that is not a tree: its nodes
form a triangular grid in which a node has two parents as well as two
children, which buys a much shallower invariant and costs a square root. See
[OBSERVATIONS.md](OBSERVATIONS.md).

The leftist heap is the first here whose tree is explicit rather than implied
by an array index. It is built entirely out of merging: insertion merges a
one-node heap, extraction merges the two subtrees of the root. Because a merge
walks only the right spine of each operand, what has to stay short is that
spine, and the leftist condition -- a node's left subtree is at least as deep
as its right one -- is what keeps it logarithmic.

It comes in two units, which hold the same tree and differ in who owns the
pool. `Heaps.Leftist` is a `Heap` object with a pool of its own, holding one
tree; melding two of them means copying one operand's nodes into the other's
pool before the splice, which is O(m). `Heaps.Leftist_Arena` makes the pool
package state and a heap a root inside it, so several trees share one array and
a meld is the splice and nothing else. The price is that a heap is no longer a
first-class object: one arena per instantiation, no array of arenas and none
passed to a subprogram. For a collection of mergeable structures that is the
right way round, since the k operands of a k-way meld are k trees in one arena
rather than k arenas. `Heaps.Leftist_Pool` is the library-level instance the
tests and benchmarks use.

Whether the copy matters depends entirely on the operand: it is the whole cost
when the operands are large, and it is unmeasurable when they are single keys,
where the two units are within a few percent of each other and four orders of
magnitude ahead of every rebuilding heap. See [OBSERVATIONS.md](OBSERVATIONS.md).

The block-min directory occupies the point between the unsorted baseline and
a tree. Keys remain unsorted, while a compact second array remembers the
winner of each 256-key block. Insertion touches one entry; extraction scans the
directory and repairs at most two blocks after filling the removed slot with
the last key.

### Open benchmark entry

`Heaps.Open` is an intentionally unverified Ada implementation rather than
another canonical heap. It obeys the same online API for arbitrary keys, but
may use extra memory and adapt to the operation history. It does not inspect
scenario names, generator state or future operations.

The entry buffers an insertion phase. After the first extraction it either
builds a binary min/max heap for mixed traffic or radix-sorts the integer keys
for a continuing drain; switching ends also selects the sorted representation.
It is workload-specialized: its adaptation policy was designed with the
benchmark's phased drains and alternating churn in mind. It is included to show
what an implementation optimized for those workloads can do, not as part of
the verified comparison set.

## Meld

Destructive `Meld (Into, From)`: `Into` receives every key of `From`, which is
left empty. This is the operation a mergeable heap exists for, and every entry
in the catalogue has it, so the benchmark can compare a splice against a
rebuild across the whole set.

| Heap | Cost | How |
|------|------|-----|
| Unsorted array | O(m) | a copy and nothing to repair |
| Binary heap | O(n + m) | append then rebuild bottom-up |
| d-ary heap | O(n + m) | as the binary heap |
| Weak heap | O(n + m) | append then join each node to its ancestor |
| Min-max heap | O(n + m) | append then trickle down, bottom-up |
| Interval heap | O(n + m) | append, pair the slots, then both ends |
| Sorted array | O(n + m) | the merge of two sorted runs |
| Beap | O(m sqrt n) | one insertion per key |
| Block-min directory | O(m) | one insertion per key |
| Leftist heap | O(m + log n) | copy into the other pool, then splice |
| Leftist arena | O(log n) | a splice of two right spines |

The implicit heaps rebuild rather than splice, which is asymptotically worse
and deliberately so: rebuilding by repeated insertion would be O(m log n) and
would flatter the mergeable structures instead of giving them a fair opponent.
Two entries are the exception that proves the rule. The block-min directory's
insertion is already O(1), so inserting the keys one at a time *is* the optimal
O(m) meld there. The beap's is O(sqrt n), and a bottom-up rebuild of a beap is
not linear -- a node in layer L sifts through the sqrt(n) - L layers below it,
which sums to O(n ** 1.5) -- so repeated insertion wins there too, for every
`m`. When insertion is cheap enough, repeated insertion *is* the better meld.

The rebuilds differ in what a bottom-up pass has to be told. A binary heap's
ordering is local, so a sift can be given the one subtree that is not yet in
order. A min-max heap's and an interval heap's are stated as domination of a
whole subtree, so the sift had to be relativized: it now carries the lowest
index whose claims are in force, and a build walks that bound down from one
past the last node. The interval heap needs two such bounds, because it places
the low end of a node while the high end of that same node is still unplaced.
The weak heap needs neither, because a join is local again -- but it does need
one pass more than it looks: nothing is sorted until every node has been joined
to its distinguished ancestor.

The sorted array is the one entry whose meld is neither an append and a rebuild
nor a splice, but a merge of two runs, and it needs something the others do
not. Halfway through a merge the array holds three regions -- the part of the
original run not yet consumed, the part already consumed and not yet
overwritten, and the merged output -- and the multiset model of this collection
is a scan of an array *prefix*, which cannot describe that. `Heaps.Models`
therefore also carries a range model, `Occurrences_In`, and the four lemmas
that relate it to the prefix one. Running the merge backwards is what keeps the
array to two live regions rather than three: the output slot is always above
the part of `Into`'s own run still to be read, so no key is ever copied out of
the way.

The two leftist units are the two sides of one API decision. `Heaps.Leftist`
owns its pool, so a meld has to copy `From`'s nodes into the free slots at the
end of `Into`'s pool, shifting every index, before the two roots can be
spliced. `Heaps.Leftist_Arena` puts several trees in one pool, so the copy
disappears and the meld is the splice alone; the price is that a heap stops
being a first-class object. The benchmark measures exactly what the copy costs:
on a workload that folds sixteen *one-key* heaps into a large accumulator the
two are indistinguishable -- 131 ns against 134 at `n = 1_000_000`, where every
rebuilding heap is four orders of magnitude behind -- and on one that folds
sixteen heaps of `n / 16` keys the copy is the whole cost, and the arena is 256
times faster. See [OBSERVATIONS.md](OBSERVATIONS.md).

## Planned

### Operations

The catalogue above varies the data structure while holding the operation set
fixed: `Insert`, `Extract_Min`, `Extract_Max` for the double-ended pair, and
`Meld`. One operation that priority queues are commonly asked for is not there.

**Decrease-key.** Deliberately out of scope. It needs handles that stay valid
as keys move, and every implicit heap here relocates keys on every sift, so it
would mean carrying a handle-to-index map through every swap in every unit:
a tax on the operations that are already measured, and roughly twice the
invariant to prove. It belongs with the structures it is actually for --
Fibonacci and rank-pairing heaps -- on a handle-based API from the start,
rather than retrofitted onto the array-backed ones.

### Array-backed selection structures

- Tournament (winner) tree
- Min-max tournament tree

### Array-backed node pools

- Skew heap
- Binomial heap
- Skew binomial heap
- Pairing heap
- Rank-pairing heap
- Fibonacci heap
- Sorted linked list
- AA tree
- AVL tree

### Integer-key queues

- Bucket queue
- Radix heap
- Bitmapped heap
- Hierarchical bitmap queue
- Binary trie
- Patricia trie
- Calendar queue

## Verification

GNATprove proves every canonical implementation in `src/`; `Heaps.Open` is the
explicit unverified exception. For the verified implementations GNATprove
checks:

- absence of run-time errors (Silver);
- preservation of ordering and correct minimum or maximum results (Gold);
- full functional correctness against a multiset model (Platinum).

### Current status

The catalogue is proved, `Meld` included, with one exception:
`Heaps.Leftist.Meld` is unfinished. Its body does not compile as it stands --
the model of the pool on entry is passed to `Graft` as a ghost parameter, which
is not a thing Ada has -- and the last complete run of the previous state left
thirteen checks unproved between `Graft` and `Meld`. Everything else in `src/`
goes through, so the tree as a whole does not build until that one body is
settled.

### Contracts

The contracts treat a heap as a multiset of keys. `Insert` adds one occurrence.
`Extract_Min` removes one occurrence of a minimum key. The min-max and interval
heaps provide the corresponding guarantee for `Extract_Max`. Each operation
states the new size and restores the heap invariant.

The multiset model is ghost code. Contracts and proof assertions are disabled
at run time.

## Build, test, and prove

```sh
gprbuild -P bench.gpr
./heaps_test
./open_heap_test
./bench_main
gnatprove -P heaps.gpr -j0 --level=4
```

`heaps_test` checks results against a proved linear-scan oracle. It also checks
extraction order and key preservation. The arena is checked differently on two
points, because with several trees in one array there is no range of slots
holding a given tree's keys and so no scan to compare against: its oracle is
kept by the test, and it additionally checks the arena's free count across
every operation, and that a tree an operation did not name comes back with the
keys it had.

Every implicit heap goes through at `--level=2`. The two leftist units, whose
tree is a pool of linked nodes rather than an array index, need `--level=4` --
`Heaps.Leftist` leaves seven checks unproved below it and the arena one; see
[PROOF.md](PROOF.md) for what those proofs took and what carried them. The
figures above are for everything but `Heaps.Leftist.Meld`; see the status note.

## Benchmarks

The benchmarks cover filling, draining, mixed extraction and insertion, and
ascending or descending input. The `replace-forward` workload keeps the queue
size fixed while replacing each extracted key with a strictly greater one, as
in event queues, recurring schedulers and merging sorted streams. Double-ended
tests also drain from the maximum end or alternate between both ends. The beap,
block-min directory and two array baselines have an operation that is worse
than logarithmic, so they run over fewer sizes than the rest.

Each implementation receives the same fixed-seed key sequence. Each scenario
runs five times; the fastest time is reported in nanoseconds per operation. See
[OBSERVATIONS.md](OBSERVATIONS.md) for results.

Two scenarios meld, over the whole catalogue. A single meld is
far too fast to time, so both are k-way accumulation -- build sixteen heaps and
fold them one after another into an accumulator -- which makes the timed phase
long enough to measure and sweeps the size ratio between the operands as the
accumulator grows. `meld-accumulate` starts from an empty accumulator and
sixteen operands of `n / 16` keys; `meld-into-full` prefills the accumulator
with `n` keys and folds in sixteen one-key heaps, which is where a structure
that rebuilds pays for the accumulator and one that splices does not.

## Layout

```text
src/            verified library
bench/          tests and benchmarks
heaps.gpr       proof project
bench.gpr       benchmark project
sparklib.gpr    local SPARKlib project file
```

[PROOF.md](PROOF.md) collects what the proofs cost and what made the
difference, written up after the first one that was genuinely hard.

## License

Apache License 2.0 with the LLVM exception. See [LICENSE](LICENSE).
