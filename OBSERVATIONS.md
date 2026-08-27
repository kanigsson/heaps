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
