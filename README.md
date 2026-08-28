# Heaps in SPARK

Verified priority queues backed by arrays. No access types.

## Implementations

| Heap | Insert | Extract | Proved | Notes |
|------|--------|---------|:------:|-------|
| Binary heap | O(log n) | O(log n) min | yes | Binary min-heap |
| d-ary heap | O(log\_d n) | O(d log\_d n) min | yes | Configurable arity |
| Weak heap | O(log n) | O(log n) min | yes | One flip bit per node, half the comparisons |
| Min-max heap | O(log n) | O(log n) min or max | yes | Double-ended queue |
| Interval heap | O(log n) | O(log n) min or max | yes | Double-ended, two keys per node |
| Beap | O(sqrt n) | O(sqrt n) min | yes | Triangular layers, two parents per node |
| Leftist heap | O(log n) | O(log n) min | yes | Mergeable, explicit tree in a shared node arena |
| Skew heap | O(log n)* | O(log n)* min | yes | As the leftist heap with no rank field; * amortized |
| Block-min directory | O(1) | O(n / B + B) min | yes | One winner per block, B = 256 |
| Unsorted array | O(1) | O(n) min | yes | Baseline |
| Sorted array | O(n) | O(1) min | yes | Baseline |

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

Being the first explicit tree, it is also where the shape of the interface had
to be settled, and it was settled twice. The obvious shape is a `Heap` object
with a node pool of its own, holding one tree. That shape makes a meld O(m):
the two operands live in two disjoint arrays, so one has to be copied into the
other before its root can be spliced in, and the copy is the whole cost of the
operation the structure exists for. `Heaps.Leftist` therefore makes the pool
package state and a heap a root inside it, so several trees share one array and
a meld is the splice and nothing else. The price is that a heap is not a
first-class object: one arena per instantiation, no array of arenas and none
passed to a subprogram. For a collection of mergeable structures that is the
right way round, since the k operands of a k-way meld are k trees in one arena
rather than k arenas. `Heaps.Leftist_Pool` is the library-level instance the
tests and benchmarks use.

Both shapes were built and measured before the object one was dropped, and what
the measurement says is that the copy costs nothing when the operands are single
keys and costs everything when they are not -- a factor of about three hundred
at `n = 1_000_000`. It is the arena that goes on, and it is the shape the other
mergeable explicit-tree heaps below should take. See
[OBSERVATIONS.md](OBSERVATIONS.md).

The skew heap is the same tree with the bookkeeping removed. A merge walks the
right spines of its two operands either way; the leftist heap then decides, at
each node on the way back up, whether to exchange that node's two subtrees, and
it keeps a rank per node to decide with. The skew heap exchanges them every
time and asks nothing, which costs the worst-case bound -- a single merge can
walk a spine of n nodes and only a *sequence* of operations is logarithmic --
and saves a field per node, a comparison per step of every merge, and the one
invariant clause that relates a node's two subtrees to one another. The two
units are otherwise the same code and the same contracts, so the pair is the
cleanest measurement in the collection of what a worst-case guarantee costs
when nothing else differs. It divides cleanly: on every workload dominated by
extraction the skew heap is 18 to 33 per cent faster at `n = 1_000_000`, and on
the two dominated by insertion into a large tree it is slower -- 27 per cent on
random fill and 82 per cent on ascending input -- because the right spine an
insertion walks is the very thing the rank field is there to bound. See
[OBSERVATIONS.md](OBSERVATIONS.md).

The block-min directory occupies the point between the unsorted baseline and
a tree. Keys remain unsorted, while a compact second array remembers the
winner of each 256-key block. Insertion touches one entry; extraction scans the
directory and repairs at most two blocks after filling the removed slot with
the last key.

### Open benchmark entry

`Heaps.Open` is an intentionally unverified Ada implementation rather than
another canonical heap. It obeys the same online API for arbitrary keys, but
may use programming techniques outside SPARK and the array-only restrictions
of the canonical entries.

The current entry is a buffered interval heap. It keeps small queues in an
unsorted array, delays construction of the main heap until an extraction is
actually requested, and thereafter collects insertions in a small interval
heap. A size-based cost rule either inserts that batch into the main heap or
melds it by a linear rebuild. The implementation does not recognize benchmark
scenarios, generator state, key patterns or future operations.

Meld follows the same rule. Two heaps that have not yet needed ordering remain
lazy and concatenate their staged keys. Once an ordered representation exists,
a small source uses buffered insertion and a comparable source uses the
interval heap's linear rebuild.

An adaptive open entry is still admissible when its policy is a documented,
general online strategy chosen independently of this benchmark. Recognizing a
known scenario from its operation sequence, fixed seeds or key construction is
outside the intended comparison.

## Meld

Destructive `Meld (Into, From)`: `Into` receives every key of `From`, which is
left empty. This is the operation a mergeable heap exists for, and every entry
in the catalogue has it, so the benchmark can compare a splice against a
rebuild across the whole set.

| Heap | Cost | Proved | How |
|------|------|:------:|-----|
| Unsorted array | O(m) | yes | a copy and nothing to repair |
| Binary heap | O(n + m) | yes | append then rebuild bottom-up |
| d-ary heap | O(n + m) | yes | as the binary heap |
| Weak heap | O(n + m) | yes | append then join each node to its ancestor |
| Min-max heap | O(n + m) | yes | append then trickle down, bottom-up |
| Interval heap | O(n + m) | yes | append, pair the slots, then both ends |
| Open buffered heap | O(m), O(m log n), or O(n + m) | no | concatenate, insert, or rebuild according to representation and size |
| Sorted array | O(n + m) | yes | the merge of two sorted runs |
| Beap | O(m sqrt n) | yes | one insertion per key |
| Block-min directory | O(m) | yes | one insertion per key |
| Leftist heap | O(log n) | yes | a splice of two right spines |
| Skew heap | O(log n)* | yes | as the leftist heap, swapping unconditionally |

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

The leftist heap is the only entry whose meld is a splice, and it is the reason
its pool is shared rather than private. Both shapes were measured before the
private one was dropped: on a workload that folds sixteen *one-key* heaps into
a large accumulator the two are indistinguishable, and every rebuilding heap is
four orders of magnitude behind both; on one that folds sixteen heaps of
`n / 16` keys the copy is the entire cost and the shared pool is some three
hundred times faster. See [OBSERVATIONS.md](OBSERVATIONS.md).

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

- Binomial heap
- Skew binomial heap
- Pairing heap
- Rank-pairing heap
- Fibonacci heap
- Sorted linked list
- AA tree
- AVL tree

The mergeable ones down to the Fibonacci heap should take the shape the leftist
heap settled on: the pool is package state, a heap is the index of its root,
and every operation takes that name `in out` because a meld returns one of its
two operands as the new root. That is what keeps a meld a splice, and it is the
whole reason the object-shaped leftist heap is not in the catalogue. The last
three do not meld, so the arena would cost them a first-class object and buy
them nothing; those stay objects with pools of their own.

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

A `--level=4` run discharges all 4 150 checks, which is every entry in the
tables above and every `Meld` in them. `heaps_test` passes on the whole
catalogue.

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
extraction order and key preservation. The two arenas are checked differently
on two points, because with several trees in one array there is no range of
slots holding a given tree's keys and so no scan to compare against: their
oracle is kept by the test, and it additionally checks an arena's free count
across every operation, and that a tree an operation did not name comes back
with the keys it had. Those checks are written once and run once per arena,
since the two present the same interface and claim the same contracts.

Every implicit heap goes through at `--level=2`. The two arenas, whose trees
are linked nodes rather than array indices, need `--level=4`; each leaves one
check unproved below that. See [PROOF.md](PROOF.md) for what those proofs took
and what carried them.

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
