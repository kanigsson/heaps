# Heaps in SPARK

Verified priority queues backed by arrays.

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
| Pairing heap | O(1) | O(log n)* min | yes | Multiway tree, child and sibling links; * amortized |
| Block-min directory | O(1) | O(n / B + B) min | yes | One winner per block, B = 256 |
| Unsorted array | O(1) | O(n) min | yes | Baseline |
| Sorted array | O(n) | O(1) min | yes | Baseline |

## Build, test, and prove

```sh
gprbuild -P bench.gpr
./heaps_test
./open_heap_test
./bench_main --machine="an AMD Ryzen 9 3950X with GNAT Pro 27.0w at -O2" \
  --summary --markdown=OBSERVATIONS.md --json=docs/results.js
gnatprove -P heaps.gpr -j0 --level=4
```

## Performance

From an AMD Ryzen 9 3950X, GNAT Pro 27.0w at `-O2`:

```
Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

open-proved     0.74  ██████
open-buffered   0.89  ███████
binary          1.00  ████████
4-ary           1.62  █████████████
8-ary           1.63  █████████████
16-ary          1.73  ██████████████
pairing         1.85  ███████████████
min-max         2.12  █████████████████
weak            2.28  ██████████████████
interval        2.64  █████████████████████
skew            6.72  ██████████████████████████████████████████████████████
leftist         6.96  ████████████████████████████████████████████████████████
```

Per-scenario charts are in [OBSERVATIONS.md](OBSERVATIONS.md), and
[docs/index.html](docs/index.html) plots the same run with the metric,
the sizes and the entries selectable.

## What is proved

The priority queue is modeled as a multiset of keys. All heaps have operations
`Insert`, `Extract_Min` and `Meld` (merge), with full platinum-level contracts:

```
   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);
```


## Planned

### Array-backed selection structures

- Tournament (winner) tree
- Min-max tournament tree

### Array-backed node pools

- Binomial heap
- Skew binomial heap
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


## Open benchmark entries

Two benchmark entries have been devised for comparison purposes. Both are allowed
to use any technique, or combination of techniques. Cheating the benchmark (e.g.
exploiting the order of operations the benchmark performs) is not allowed.
One entry is fully proved as well, while the other one is not proved at all.

## License

Apache License 2.0 with the LLVM exception. See [LICENSE](LICENSE).
