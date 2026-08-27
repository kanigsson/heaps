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

## Planned

### Operations

The catalogue above varies the data structure while holding the operation set
fixed: `Insert`, `Extract_Min`, and `Extract_Max` for the double-ended pair.
Two operations that priority queues are commonly asked for are missing, for
different reasons.

**Meld.** Destructive `Meld (Into, From)`: `Into` receives every key of
`From`, which is left empty. This is the operation a mergeable heap exists for,
and until every entry has it the benchmark cannot show the one column in which
the leftist heap is asymptotically better than everything it is compared
against. Implemented and proved so far:

| Heap | Meld | Cost |
|------|:----:|------|
| Unsorted array | yes | O(m), a copy and nothing to repair |
| Binary heap | yes | O(n + m), append then rebuild bottom-up |
| d-ary heap | yes | O(n + m), as the binary heap |
| Sorted array | no | O(n + m), the merge of two sorted runs |
| Weak heap | no | append then rebuild |
| Min-max heap | no | append then rebuild |
| Interval heap | no | append then rebuild |
| Beap | no | append then rebuild |
| Block-min directory | yes | O(m), its insertion is already O(1) |
| Leftist heap | no | O(log n) in principle, and the reason to have the operation at all -- but only once the pool is shared, see below |

The implicit heaps rebuild rather than splice, which is asymptotically worse
and deliberately so: rebuilding by repeated insertion would be O(m log n) and
would flatter the mergeable structures instead of giving them a fair opponent.
The block-min directory is the exception that proves the rule -- its insertion
is already O(1), so inserting the keys one at a time *is* the optimal O(m) meld
there, and no rebuild is needed.

The sorted array is the one entry whose meld is not an append and a rebuild but
a merge of two runs, and it needs something the others do not. Halfway through a
merge the array holds three regions -- the part of the original run not yet
consumed, the part already consumed and not yet overwritten, and the merged
output -- and the multiset model of this collection is a scan of an array
*prefix*, which cannot describe that. Giving it one means adding a range-model
to `Heaps.Models` and the lemmas to go with it, which is shared machinery none
of the other melds need.

The leftist heap is the open question. Its internal merge already takes two
roots inside one pool, but the exported `Heap` bundles the pool with the
assertion that it holds a single tree, so melding two `Heap` objects has to
copy one operand's nodes into the other's pool -- O(m), which throws away the
point of the structure. A genuine O(log n) meld needs several trees to live in
one pool, and that is an API decision affecting every mergeable heap in the
list below, so it is being taken before the next one is written rather than
after.

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
extraction order and key preservation.

Every implicit heap goes through at `--level=2`. The leftist heap, whose tree
is a pool of linked nodes rather than an array index, needs `--level=4`; see
[PROOF.md](PROOF.md) for what its proof took and what carried it.

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

No scenario melds two heaps yet; see [Planned operations](#operations) for why,
and for what that leaves unmeasured. A single meld is far too fast to time, so
the workload will be k-way accumulation -- build k heaps and meld them all into
one -- which makes the timed phase long enough to measure and sweeps the size
ratio between the operands as the accumulator grows.

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
