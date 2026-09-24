# Heaps in SPARK

Verified priority queues backed by arrays.

## Implementations

| Heap                | Notes                                           | Insert       | Extract        |
|---------------------|-------------------------------------------------|:------------:|:--------------:|
| Binary heap         | Binary min-heap                                 | `O(log n)`   | `O(log n)`     |
| Tournament tree     | Cached winner at every internal node            | `O(log n)`   | `O(log n)`     |
| d-ary heap          | Configurable arity                              | `O(log_d n)` | `O(d log_d n)` |
| Weak heap           | One flip bit per node, half the comparisons     | `O(log n)`   | `O(log n)`     |
| Min-max heap        | Double-ended queue                              | `O(log n)`   | `O(log n)`     |
| Min-max tournament  | Cached extrema at every internal node           | `O(log n)`   | `O(log n)`     |
| Interval heap       | Double-ended, two keys per node                 | `O(log n)`   | `O(log n)`     |
| Beap                | Triangular layers, two parents per node         | `O(√n)`      | `O(√n)`        |
| Leftist heap        | Mergeable, explicit tree in a shared node arena | `O(log n)`   | `O(log n)`     |
| Skew heap           | As the leftist heap with no rank field          | `O(log n)`†  | `O(log n)`†    |
| Pairing heap        | Multiway tree, child and sibling links          | `O(1)`       | `O(log n)`†    |
| Binomial heap       | Ranked forest in a shared node arena            | `O(log n)`   | `O(log n)`     |
| Skew binomial heap  | Skew-linked forest, worst-case constant insert  | `O(1)`       | `O(log n)`     |
| Fibonacci heap      | Lazy binomial forest, no decrease-key           | `O(1)`       | `O(log n)`†    |
| Block-min directory | One winner per block, B = 256                   | `O(1)`       | `O(n / B + B)` |
| Bucket queue        | Bounded integer priorities, one chain per key   | `O(1)`       | `O(U)`         |
| Radix heap          | Monotone keys, one array run per bucket         | `O(log U)`   | `O(log² U)`†   |
| Unsorted array      | Baseline                                        | `O(1)`       | `O(n)`         |
| Sorted array        | Baseline                                        | `O(n)`       | `O(1)`         |
| Sorted linked list  | Doubly linked nodes in an array-backed pool     | `O(n)`       | `O(1)`         |

Every implementation is proved. Extraction is of the minimum, except
for the double-ended heaps, which extract either end. † amortized.

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

open-proved     0.72  ██████
open-buffered   0.87  ███████
binary          1.00  ████████
8-ary           1.56  ████████████
4-ary           1.56  ████████████
16-ary          1.70  ██████████████
min-max         2.05  ████████████████
pairing         2.16  █████████████████
fibonacci       2.19  ██████████████████
weak            2.21  ██████████████████
interval        2.60  █████████████████████
skew binomial   5.10  █████████████████████████████████████████
skew            6.57  █████████████████████████████████████████████████████
leftist         7.16  █████████████████████████████████████████████████████████
tournament      9.05  ████████████████████████████████████████████████████████████████+
binomial        9.94  ████████████████████████████████████████████████████████████████+
min-max tourn.  14.28 ████████████████████████████████████████████████████████████████+
```

Per-scenario charts are in [OBSERVATIONS.md](OBSERVATIONS.md), and
the [interactive charts](https://kanigsson.github.io/heaps/) plot the same
run with the metric, the sizes and the entries selectable.

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

### Array-backed node pools

- Rank-pairing heap
- AA tree
- AVL tree

### Integer-key queues

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
