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

### Array-backed selection structures

- Tournament (winner) tree
- Min-max tournament tree

### Array-backed node pools

- Leftist heap
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
gnatprove -P heaps.gpr -j0 --level=2
```

`heaps_test` checks results against a proved linear-scan oracle. It also checks
extraction order and key preservation.

## Benchmarks

The benchmarks cover filling, draining, mixed extraction and insertion, and
ascending or descending input. Double-ended tests also drain from the maximum
end or alternate between both ends. The beap, block-min directory and two array
baselines have an operation that is worse than logarithmic, so they run over
fewer sizes than the rest.

Each implementation receives the same fixed-seed key sequence. Each scenario
runs five times; the fastest time is reported in nanoseconds per operation. See
[OBSERVATIONS.md](OBSERVATIONS.md) for results.

## Layout

```text
src/            verified library
bench/          tests and benchmarks
heaps.gpr       proof project
bench.gpr       benchmark project
sparklib.gpr    local SPARKlib project file
```

## License

Apache License 2.0 with the LLVM exception. See [LICENSE](LICENSE).
