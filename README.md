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

The three binomial forests put the work in different places. The binomial
heap links eagerly on insertion, so an insertion costs 47 to 99 ns and grows
with the carry chain. The Fibonacci heap defers every link to the next
extraction: an insertion costs 4.1 to 4.9 ns at every size and a meld at most
52 ns, where the binomial heap's meld grows to 613 ns. Its first extraction
after a fill then links the million singleton roots, and a drain at
n = 1 000 000 costs 684 ns against the binomial heap's 604 ns.

The skew binomial heap sits between them, and it is the only one of the three
whose insertion is bounded in the worst case rather than on average. A skew
link touches at most three nodes, and an insertion costs 14 to 19 ns at every
size, from n = 1 000 to n = 1 000 000. Folding one-key heaps into a full one
costs 41 to 51 ns a meld, against the binomial heap's 76 to 99 ns. Extraction
is where it pays: rank-0 children are reinserted one at a time and both lists
are normalized before the merge, so a drain at n = 1 000 000 costs 963 ns,
1.6 times the binomial heap's. On balance its aggregate is half the binomial
heap's -- 5.10 against 9.94 -- because three of the six scenarios are
insertion alone, and there it is five to seven times faster.

The radix heap is not in that aggregate: unconstrained churn can insert below
its last extracted key, so it runs only the monotone scenarios. Its cost per
operation is bounded by the key range and not by `n`, which the measurements
bear out — over three decades of size a drained key goes from 181.31 ns to
237.52 ns, and an inserted one from 17.60 ns to 17.76 ns.

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
