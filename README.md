# SPARK heaps in arrays

Formally verified priority-queue (heap) data structures in SPARK, all of them
laid out inside arrays — no access types anywhere.

Two layout families are represented:

* **Implicit heaps.** The array index *is* the tree structure: the children of
  node `I` sit at `2*I` and `2*I+1` (or `d*I-d+2 .. d*I+1` for a `d`-ary heap).
  Nothing is stored but the keys.
* **Explicit heaps over a node pool.** Trees that are genuinely pointer-shaped
  (leftist, binomial, pairing, Fibonacci …) are realized with a fixed array of
  nodes whose links are `Node_Index` values instead of pointers, plus a free
  list. This keeps the whole collection inside the pointer-free SPARK subset
  while still exercising the interesting algorithms.

## Catalogue

Ordered roughly by how hard they are to verify.

### Implicit array heaps

| # | Heap | Notes | Verification |
|---|------|-------|--------------|
| 1 | **Binary heap** (Williams) | The classic. Sift-up on insert, sift-down on extract. | see table below |
| 2 | **d-ary heap** | Shallower tree, fewer sift-up moves, more comparisons per sift-down level. Generalizes #1. | see table below |
| 3a | **Unsorted array** | Not a heap: O(1) insert, O(n) extract. The baseline the real heaps have to beat. | see table below |
| 3b | **Sorted array** | The opposite corner: O(n) insert, O(1) extract. Kept in decreasing order so removal needs no shifting. | see table below |
| 4 | **Min-max heap** | Alternating min and max levels: a double-ended queue in one array. | planned |
| 5 | **Interval heap** (twin heap) | Double-ended too, but each node holds a `[min, max]` interval. | planned |
| 6 | **Beap** (bi-parental heap) | Nodes have two parents and two children; O(√n) operations. | planned |
| 7 | **Weak heap** | Relaxed ordering plus a bit array of "reverse" flags; near-optimal comparison count. | planned |

### Explicit heaps over a node pool

| # | Heap | Notes | Verification |
|---|------|-------|--------------|
| 8 | **Leftist heap** | Meldable; maintains the null-path-length invariant. First one needing a node pool. | planned |
| 9 | **Skew heap** | Self-adjusting leftist heap, no stored rank. Amortized bounds. | planned |
| 10 | **Binomial heap** | Forest of binomial trees, O(log n) meld. | planned |
| 11 | **Skew binomial heap** | Binomial heap with O(1) insert. | planned |
| 12 | **Pairing heap** | Simple, fast in practice, hard to analyze. | planned |
| 13 | **Rank-pairing heap** | Fibonacci-like bounds with a simpler structure. | planned |
| 14 | **Fibonacci heap** | Lazy meld, O(1) amortized decrease-key. Circular sibling lists in the pool. | planned |

### Key-restricted heaps (integer keys, non-comparison)

| # | Heap | Notes | Verification |
|---|------|-------|--------------|
| 15 | **Bucket queue** | One list per priority; O(1) operations for small key ranges. | planned |
| 16 | **Radix heap** | Monotone priority queues (Dijkstra). | planned |
| 17 | **Bitmapped heap** | Priorities as a hierarchical bitmap, `Count_Trailing_Zeros` for the min. | planned |

## Verification levels

Each heap is taken through the SPARK assurance levels in order:

* **Silver** — no run-time errors: every index, every arithmetic operation is
  proved in range.
* **Gold (key properties)** — the heap ordering is an invariant of every
  operation, and `Peek_Min` / `Extract_Min` really return the minimum of the
  stored keys.
* **Platinum** — full functional correctness against a model of the heap as a
  *multiset* of keys: insert adds one occurrence, extract removes one
  occurrence of the minimum, and nothing else changes.

| Heap | Silver | Gold | Platinum |
|------|:------:|:----:|:--------:|
| Binary heap | ✅ | ✅ | ✅ |
| d-ary heap | ✅ | ✅ | ✅ |
| Unsorted array | ✅ | ✅ | ✅ |
| Sorted array | ✅ | ✅ | ✅ |

`gnatprove -P heaps.gpr -j0 --level=2 -f` currently reports
**`Success: all checks proved (656 checks)`** — that covers `src/` and the part
of SPARKlib the project uses.

The d-ary heap takes the arity as a *discriminant* of the heap type rather
than as a generic parameter. A generic would only ever be verified through its
instances, one proof per arity; with a discriminant the arity is a universally
quantified variable and the single proof covers every arity at once. The price
is paid at run time — see the benchmark discussion below — and it is the only
place in the collection where verifiability and speed pull in opposite
directions.

For the two baselines "gold" means different things, which is the point of
having them. The sorted array has a real structural invariant, `Is_Sorted`,
preserved by both operations, and `Lemma_Last_Is_Minimum` plays exactly the
role `Lemma_Root_Is_Minimum` plays for the binary heap. The unsorted array has
*no* invariant — every array value is a valid state — so its specification is
nothing but the multiset equations plus `Is_Minimum`. It is the smallest
complete example of what platinum actually asserts.

### What the contracts actually say

For the binary heap, `Extract_Min` carries the whole story:

```ada
procedure Extract_Min (H : in out Heap; K : out Key_Type)
  with Pre  => not Is_Empty (H) and then Is_Heap (H),
       Post => Is_Heap (H)                                    --  gold
               and Size (H) = Size (H)'Old - 1
               and K = Peek_Min (H)'Old
               and Is_Minimum (H'Old, K)                      --  gold
               and Model (H)'Old = Key_Multisets.Add (Model (H), K);
                                                              --  platinum
```

`Model (H)` is the multiset of `H.Keys (1 .. H.Last)`. The last conjunct says
that the heap before the call is exactly the heap after the call plus one
occurrence of `K` — nothing lost, nothing invented, nothing duplicated — and
`Is_Minimum (H'Old, K)` says that `K` was a smallest element of that multiset.
Together they are full functional correctness of extraction; the array, the
sift-down and the ordering invariant are then pure implementation detail.

The model machinery lives in `Heaps.Models` and is shared by every heap in the
collection, so later heap kinds only have to relate their own layout to
`Occurrences`.

The d-ary heap carries those contracts word for word: the multiset model does
not mention the array, so generalizing the layout from two children to `Arity`
children changes the implementation and the invariants but not one character
of the specification. What it does change is that the parent relation is no
longer a shift. `Parent (D, I) = (I + D - 2) / D` and
`First_Child (D, I) = D * (I - 1) + 2` are inverse to each other, and unfolding
that integer division once — `Lemma_Child_Range`, the only nonlinear step in
the unit — is what lets every other proof in `Heaps.Dary` reason about
"the children of the hole" as a contiguous slice.

### Run-time cost of the ghost code

None. The model is a recursive functional multiset and evaluating it would make
every operation quadratic, so the verified units set

```ada
pragma Assertion_Policy (Ghost => Ignore, Pre => Ignore, Post => Ignore,
                         Assert => Ignore, Loop_Invariant => Ignore);
```

The benchmark timings and checksums are bit-identical before and after the
platinum contracts were added.

## Layout

```
src/            the verified library (SPARK)
bench/          the micro-benchmark suite (plain Ada, not verified)
heaps.gpr       library project — this is what gnatprove analyzes
bench.gpr       benchmark project
sparklib.gpr    local copy of the SPARKlib project file
```

## Building and running

```sh
gprbuild -P bench.gpr && ./bench_main      # benchmarks
gprbuild -P bench.gpr && ./heaps_test      # run-time sanity checks
gnatprove -P heaps.gpr -j0 --level=2       # proof
```

`heaps_test` cross-checks `Peek_Min` against `Min_Of`, a proved linear-scan
oracle, and checks that a drained heap yields its keys in non-decreasing order
and that nothing is lost on the way.

## Benchmark scenarios

All heaps see the same key sequence, produced by a fixed-seed xorshift
generator, so timings are comparable and the printed checksum can be used to
cross-check two implementations against each other.

| Scenario | Measured phase |
|----------|----------------|
| `fill` | `n` inserts of pseudo-random keys into an empty heap |
| `drain` | `n` extractions from a heap pre-filled with `n` random keys (the fill is not timed) |
| `churn` | `n` × (extract-min followed by insert) on a heap of size `n` |
| `insert-asc` | `n` inserts in increasing key order — best case for sift-up |
| `insert-desc` | `n` inserts in decreasing key order — worst case for sift-up |

Each scenario is run 5 times and the fastest run is reported, in nanoseconds
per operation. `insert-asc` and `insert-desc` swap roles between the binary
heap and the sorted array: ascending keys are the cheap case for a min-heap
(the new key stays at the leaf) and the worst case for a descending sorted
array (every insert shifts the whole array).

The two array baselines have a linear operation each, so their scenarios are
quadratic; `bench_main` runs them only up to `n = 10_000`.

Because every heap kind sees the same key stream, the checksum column is a
cross-implementation oracle: the binary heap, the three d-ary arities, the
sorted array and the unsorted array all print the same checksum for the same
scenario and size, including the rank-weighted `drain` checksum that depends on
the order keys come out.

The findings the benchmark has produced so far — which heap kind wins which
scenario, and why — are collected in [OBSERVATIONS.md](OBSERVATIONS.md).

## License

Apache License 2.0 with the LLVM exception, the same terms SPARKlib is
distributed under. See `LICENSE`; each source file carries the corresponding
`SPDX-License-Identifier`.
