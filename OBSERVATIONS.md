# Benchmark observations

Results from an AMD Ryzen 9 3950X using GNAT Pro 27.0w at `-O2`:

```sh
gprbuild -P bench.gpr
./bench_main
```

Times are nanoseconds per operation, using the fastest of five runs. Absolute
times are machine-specific; comparisons within a table are more useful.

## Main workloads

Results at `n = 1_000_000`:

| heap | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|------|-------:|--------:|--------:|-------------:|--------------:|
| binary | 9.83 | 98.35 | 51.81 | 1.90 | 11.02 |
| 4-ary | 10.92 | 91.06 | 58.84 | 5.20 | 40.81 |
| 8-ary | 8.25 | 124.40 | 69.96 | 5.07 | 27.49 |
| 16-ary | 6.58 | 171.30 | 89.67 | 4.97 | 20.06 |
| min-max | 13.04 | 174.84 | 88.13 | 12.66 | 13.66 |
| interval | 17.75 | 108.53 | 65.40 | 53.44 | 36.05 |

### d-ary heaps

Larger arities improve insertion by reducing tree depth. The 16-ary heap has
the fastest `fill`, but its `drain` is almost twice as slow as the binary heap
because each sift-down examines more children.

The binary heap remains fastest for `drain` and `churn`. The 4-ary heap comes
closest on extraction, at 91.06 ns/op against 98.35 for binary.

The d-ary implementations also pay for division by a run-time arity. This is
most visible in `insert-asc`, where insertion stops after one comparison:
about 5 ns/op for each d-ary heap against 1.90 for binary. Larger arities
reduce the full-path cost in `insert-desc`, but none catches the binary heap.

Use binary for mixed or extraction-heavy workloads. The 8- and 16-ary heaps
are useful when insertion dominates.

### Min-max heap

The min-max heap provides both minimum and maximum extraction. Against the
binary heap, `fill` is 33% slower, `drain` takes about 78% longer, and `churn`
is 70% slower.

Ascending and descending insertion cost nearly the same. Each ordered stream
repeatedly introduces a new extreme, so neither direction is a cheap case.

### Interval heap

The interval heap is the other double-ended queue in the collection, and it
splits the difference the opposite way: much better at extraction, much worse
at insertion.

Against the min-max heap, `drain` is 38% faster and `churn` 26% faster. The
reason is how far one step of a sift travels for what it costs. A min-max
sift-down step crosses two levels and has to look at up to six nodes -- two
children and four grandchildren -- whereas an interval-heap step crosses one
level and looks at two children plus one comparison to repair the node it
lands in. Over a whole descent the interval heap makes fewer comparisons.

The comparison against the binary heap is the interesting one: `drain` is only
10% slower than a queue that has no maximum at all, where the min-max heap
pays 78%. On extraction-heavy work, this is close to a free second end.

Insertion is where it loses. A min-max sift-up compares a key only against its
same-side ancestors, so it climbs two levels per step; an interval-heap sift-up
climbs one. Its tree is one level shallower, holding two keys per node, which
recovers part of that but not all of it, and `insert-asc` ends up at 53.44
ns/op against 12.66 for the min-max heap.

Ascending and descending insertion also differ by 48%, which the min-max heap
does not show. Every key of an ascending stream is a new maximum and travels
up the high ends of the nodes; every key of a descending stream is a new
minimum and travels up the low ends. The low end of a node is always the first
of its two slots, but the high end is the second one only when the node holds
two keys, so each step along the high side carries an extra test against the
size of the heap. The cost of making a lone key behave like an interval is
paid on one side only.

Double-ended results at `n = 1_000_000`:

| scenario | min-max | interval |
|----------|--------:|---------:|
| `drain` | 174.84 | 108.53 |
| `drain-max` | 192.53 | 116.53 |
| `drain-both` | 204.66 | 114.00 |
| `trim` | 99.77 | 72.86 |

Both heaps are slightly slower at the high end than at the low end -- 7% for
the interval heap, 10% for the min-max heap. Alternating between the two ends
costs the min-max heap 17% more than draining from the low end alone and lands
it outside the range spanned by its two single-ended figures; the interval
heap stays inside that range, its two ends living in the same pair of slots,
so a step of either sift brings the other end into cache as well.

`trim` measures an insert followed by `extract-max`, as used by a bounded
top-n queue. The interval heap wins it despite its slower insertion: the keys
it inserts are random rather than ordered, so most of those insertions stop
after a step or two and the extractions dominate.

Use the interval heap when both ends are read more often than the queue is
filled, and the min-max heap when insertion dominates.

## Array baselines

The linear baselines run only through `n = 10_000`:

| heap | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|------|-------:|--------:|--------:|-------------:|--------------:|
| sorted | 1218.07 | 2.28 | 878.20 | 2504.12 | 2.33 |
| unsorted | 2.38 | 10704.37 | 10648.95 | 1.95 | 1.94 |

The sorted array makes extraction constant-time but shifts keys during
insertion. Descending input is already in storage order and needs no shifting.
The unsorted array has constant-time insertion and scans the array for every
extraction.

## Checksums

The implementations produce matching checksums for every shared scenario and
size. This checks that they process the same key stream and return the same
results while taking different internal paths.
