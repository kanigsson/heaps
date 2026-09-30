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
| Rank-pairing heap   | Half-trees linked in one pass, no decrease-key  | `O(1)`       | `O(log n)`†    |
| AVL tree            | Search tree balanced by rotations, leftmost min | `O(log n)`   | `O(log n)`     |
| Block-min directory | One winner per block, B = 256                   | `O(1)`       | `O(n / B + B)` |
| Bucket queue        | Bounded integer priorities, one chain per key   | `O(1)`       | `O(U)`         |
| Radix heap          | Monotone keys, one array run per bucket         | `O(log U)`   | `O(log² U)`†   |
| Bitmap queue        | Bounded integer keys, four summary levels       | `O(1)`‡      | `O(1)`‡        |
| Unsorted array      | Baseline                                        | `O(1)`       | `O(n)`         |
| Sorted array        | Baseline                                        | `O(n)`       | `O(1)`         |
| Sorted linked list  | Doubly linked nodes in an array-backed pool     | `O(n)`       | `O(1)`         |

Every implementation is proved. Extraction is of the minimum, except
for the double-ended heaps, which extract either end. † amortized.
‡ one word per level on four fixed levels, covering keys below 2²⁴.

## Build, test, and prove

```sh
gprbuild -P bench.gpr
./heaps_test
./open_heap_test
./bench_main --machine="an AMD Ryzen 9 3950X with GNAT Pro 28.0w at -O2" \
  --summary --markdown=OBSERVATIONS.md --json=docs/results.js
gnatprove -P heaps.gpr -j0 --level=4
```

Everything was built and proved with GNAT Pro and SPARK Pro 28.0w. Other
versions may need proof adjustments. In the final full run, 4 of 16,348
checks needed more than the level-4 limits (see the end of
[PROOF.md](PROOF.md)).

## Performance

From an AMD Ryzen 9 3950X, GNAT Pro 28.0w at `-O2`:

```
Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

open-proved     0.75  ██████
open-buffered   0.90  ███████
binary          1.00  ████████
4-ary           1.61  █████████████
8-ary           1.62  █████████████
16-ary          1.75  ██████████████
pairing         1.95  ████████████████
min-max         2.13  █████████████████
fibonacci       2.22  ██████████████████
weak            2.28  ██████████████████
rank-pairing    2.33  ███████████████████
interval        2.66  █████████████████████
skew binomial   4.85  ███████████████████████████████████████
skew            6.95  ████████████████████████████████████████████████████████
leftist         7.16  █████████████████████████████████████████████████████████
tournament      9.26  ████████████████████████████████████████████████████████████████+
binomial       10.71  ████████████████████████████████████████████████████████████████+
min-max tourn. 15.03  ████████████████████████████████████████████████████████████████+
avl            16.90  ████████████████████████████████████████████████████████████████+
```

The bitmap queue keeps a count for every possible key, so it runs the same
scenarios over keys below 2²⁰ instead of 2³⁰, against a few general heaps on
those same keys:

```
Relative cost, geometric mean of the 6 bounded-key scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

bitmap          0.39  ███
open-proved     0.74  ██████
binary          1.00  ████████
4-ary           1.59  █████████████
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


## Not done

- Decrease-key. No heap supports it, so the benchmarks show what the
  Fibonacci, pairing and rank-pairing heaps cost but not the operation they
  are designed for.
- AA tree
- Binary trie, Patricia trie, calendar queue


## Open benchmark entries

Two benchmark entries have been devised for comparison purposes. Both are allowed
to use any technique, or combination of techniques. Cheating the benchmark (e.g.
exploiting the order of operations the benchmark performs) is not allowed.
One entry is fully proved as well, while the other one is not proved at all.

## License

Apache License 2.0 with the LLVM exception. See [LICENSE](LICENSE).
