# Observations

What the benchmark suite has actually shown, heap kind by heap kind. The
README describes what is measured and how; this file is where the numbers are
interpreted. A new section goes in here whenever a heap kind is added and turns
out to have something to say.

Numbers are nanoseconds per operation, best of five runs, produced by

```sh
gprbuild -P bench.gpr && ./bench_main
```

on an AMD Ryzen 9 3950X with GNAT Pro 27.0w at `-O2`. The absolute values are
machine-specific and not worth much; the comparisons between rows of the same
table are the point, since every heap kind sees the identical key sequence.

## d-ary heap: does a larger arity pay?

`bench_main` measures arities 4, 8 and 16 next to the binary heap. At
`n = 1_000_000`:

| arity | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|------:|-------:|--------:|--------:|-------------:|--------------:|
| 2 | 10.19 | 100.04 | 53.69 | 1.93 | 11.15 |
| 4 | 11.12 | 93.25 | 60.33 | 5.18 | 40.42 |
| 8 | 8.21 | 125.26 | 71.25 | 5.15 | 27.96 |
| 16 | 6.69 | 172.49 | 91.65 | 5.06 | 20.37 |

The textbook story is that a wider tree helps insertion and hurts extraction,
and the extraction half of it holds: `drain` degrades steadily with the arity,
because sift-down inspects `Arity` children at every one of its `log_Arity n`
levels, and `Arity / log Arity` grows. The exception is 4-ary at a million
keys, which overtakes the binary heap on `drain` even though it does more
comparisons — the working set of a sift-down step is a handful of adjacent
slots instead of two slots a cache line apart, and at that size the cache wins
the argument. `fill` shows the same effect without the comparison penalty:
16-ary inserts a third faster than the binary heap.

The two ordered-insert scenarios are where the discriminant shows up.
`insert-asc` stops at the first parent comparison whatever the arity, so the
binary heap's 1.93 ns against a flat ~5 ns for every d-ary arity is not a
property of d-ary heaps at all: it is one integer division by a value the
compiler cannot see. `insert-desc` walks the whole path to the root, so the
d-ary heaps get their shallower tree back and improve monotonically with the
arity — 40.42 at arity 4 down to 20.37 at arity 16 — while still not catching
the binary heap, which divides by a literal 2. A generic instantiated per arity
would close that gap, at the cost of one proof per arity.

The short version: prefer a wide d-ary heap for insert-dominated workloads
large enough to miss cache, and a binary heap whenever extraction is on the
hot path.

## Min-max heap: what does a second end cost?

The min-max heap is the first double-ended structure in the collection, so
there are two separate questions to ask of it: what it gives up on the
single-ended workload the other heaps are measured on, and what the two ends
cost relative to each other. At `n = 1_000_000`:

| heap | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|------|-------:|--------:|--------:|-------------:|--------------:|
| binary | 9.99 | 92.19 | 50.29 | 1.93 | 11.21 |
| min-max | 13.31 | 176.28 | 88.73 | 12.63 | 13.70 |

Extraction costs about twice as much as on a binary heap, which is roughly the
comparison count: a min-max sift-down descends two levels per step but has to
pick the best of up to six nodes — two children and four grandchildren — to do
it, so it spends about three comparisons per level against the binary heap's
two, and the grandchildren of a deep node are four cache lines apart where a
binary heap's two children share one.

The ordered-insert pair is the more interesting row. The binary heap spreads
across a factor of six between its best case and its worst — 1.93 against
11.21 — while the min-max heap is flat, 12.63 against 13.70. This is not an
artefact: a double-ended heap has no cheap direction. Every key of an
ascending stream is a new minimum and every key of a descending stream is a new
maximum, so either way the new key climbs to the top of *its own* side and both
monotone streams are worst cases. The binary heap's cheap case is cheap
precisely because it is blind to the maximum: an ascending key is worse than
its parent and stops at the first comparison.

The second end is not the expensive one:

| scenario | ns/op |
|----------|------:|
| `drain` (min end) | 176.28 |
| `drain-max` | 188.35 |
| `drain-both` | 202.44 |
| `trim` | 96.63 |

Extracting maxima costs seven per cent more than extracting minima, and
alternating between the ends — which defeats any locality either pure drain
gets — costs about ten per cent more than either. There is no cheap end and no
hidden asymmetry, which is the run-time counterpart of the fact that one piece
of code, parameterized by the side, serves both directions.

`trim` is the workload the structure exists for: a bounded "best `n` so far"
queue, where every insertion is paid for by evicting the current worst. At
96.63 ns per operation it is very close to the binary heap's `churn` (50.29)
doubled, which is what one would expect, and it needs one array and one
implementation rather than two heaps kept in step with each other.

### The cost of knowing which level you are on

A min-max heap has to know the parity of the depth of the node it starts from,
which is something no other heap in the collection needs. Walking up one level
at a time costs up to 24 halvings per insertion and was plainly visible in the
measurements. Climbing two levels at a time instead — the side is unchanged
across a grandparent step, so the walk can stop as soon as it reaches the top
three nodes, of which only the root is a min node — halves that:

| | `fill` | `insert-asc` | `insert-desc` |
|---|-------:|-------------:|--------------:|
| one level at a time | 16.10 | 15.30 | 16.38 |
| two levels at a time | 13.31 | 12.63 | 13.70 |

About seventeen per cent of the insertion path, for a routine that computes
nothing the algorithm proper uses. What is left of it is still visible in
`insert-asc`: 12.63 against the binary heap's 1.93, where the sift itself is
short and the level computation is most of the work.
