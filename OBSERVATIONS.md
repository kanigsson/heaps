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
| weak | 18.15 | 170.71 | 86.46 | 3.68 | 22.75 |
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

### Weak heap

The weak heap is the one implementation here whose selling point is a count
rather than a shape. Its extraction performs one key comparison per node of
the left spine and no others: 19 comparisons at `n = 1_000_000`, against the
39 or so a classic binary sift-down performs, which spends one comparison per
level choosing the smaller child and a second testing it against the key being
moved down. Halving the comparisons is what the flip bits are for.

It does not pay off here:

| n | `fill` | `drain` | binary `drain` | ratio |
|---|-------:|--------:|---------------:|------:|
| 1_000 | 7.61 | 70.60 | 21.91 | 3.22 |
| 10_000 | 17.90 | 102.48 | 34.48 | 2.97 |
| 100_000 | 18.21 | 133.87 | 50.18 | 2.67 |
| 1_000_000 | 18.15 | 170.71 | 97.41 | 1.75 |

Half the comparisons and still between two and three times the wall clock over
most of the range: a level of a weak-heap sift costs several times what a level
of a binary one costs. Four things make up the difference. There are two arrays
instead of one, so a sift runs two dependent load streams rather than one.
Extraction walks the spine twice -- down to find its last node, then back up
joining -- where a binary sift-down walks its path once. About half the levels
write a flip bit back. And a join exchanges two keys, so it writes two slots
per level, where the hole technique the binary and d-ary heaps use writes one.

What the last column shows is that the gap is closing, and closing for a reason
that has nothing to do with comparisons. Over the last decade the binary heap's
`drain` almost doubles, from 50.18 to 97.41, while the weak heap's grows by a
quarter. Both heaps have the same tree and follow a root-to-leaf path of the
same length, so both take the same number of cache misses on the key array once
the array stops fitting in cache; the weak heap's per-level surcharge is
instructions and stores, and those stop mattering when the machine is waiting
on memory. The two curves do not meet inside the range this collection is
bounded to -- the last decade closes about a third of the gap, and the
capacity limit leaves barely a decade of headroom above `n = 1_000_000` -- but
the direction is clear
enough to say that the weak heap is at its least bad where a priority queue is
usually at its most expensive.

The second array costs a byte a node, a megabyte at `n = 1_000_000`. Packing
it, one bit a node rather than one byte, was measured and made things worse
everywhere: `fill` at `n = 100_000` goes from 18.21 to 19.72 and `insert-desc`
from 19.04 to 24.34. The shifting and masking cost more than the eightfold
reduction in the size of the second array saves.

`insert-asc` is the sharpest illustration of the constant factor, at 3.68
ns/op against 1.90 for the binary heap. An ascending stream makes every new key
the largest in the heap, so insertion stops after a single comparison in both
implementations -- but the weak heap has to find the node to compare against
first. The climb is short, since a node is a left child about half the time and
the expected walk is about one step, yet it is a dependent load into the second
array before the one comparison can happen, and it doubles the cost of the
cheapest insertion there is.

The conclusion is not that the structure is a poor one. It is that it optimizes
the resource that is not scarce here: comparing two `Integer`s is free, and the
weak heap spends memory traffic to save it. With a key whose comparison is
expensive -- a long string, a record with a comparator -- the count in the first
paragraph is the number that decides, and the ranking would invert.

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

## Beap

The beap runs only through `n = 100_000`: its operations are O(sqrt n), so a
decade of size costs it a factor of about three rather than the fifteen percent
it costs a tree heap.

| n | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|---|-------:|--------:|--------:|-------------:|--------------:|
| 1_000 | 32.31 | 93.61 | 92.79 | 2.85 | 58.85 |
| 10_000 | 110.24 | 295.83 | 220.68 | 2.68 | 167.72 |
| 100_000 | 319.35 | 1008.24 | 943.64 | 2.58 | 520.98 |

For comparison, the binary heap at `n = 100_000` does `fill` in 9.60 and
`drain` in 48.66.

Each decade multiplies `fill`, `drain` and `insert-desc` by about three, which
is the sqrt(10) the layer count predicts: a beap of n nodes is sqrt(2 n) layers
deep, 447 of them at `n = 100_000`.

The interesting number is `fill`, not `drain`. Draining is 21 times slower than
the binary heap, which is what an O(sqrt n) descent against an O(log n) one
buys. Filling is 33 times slower, and that gap comes from somewhere else: a
binary heap inserts in constant expected time, and a beap does not. Half the
nodes of a binary tree sit in its last layer, so a random key stops after a
step or two. The last layer of a beap holds sqrt(2 n) of its n nodes -- a
vanishing fraction -- so a random key has to climb until it meets a layer whose
keys are as large as it is, which is on average a third of the way to the top.
The measurements bear the fraction out: `fill` is close to a third of `drain`
at all three sizes.

`insert-asc` is the case where a beap costs nothing at all. An ascending stream
makes every new key the largest in the heap, so it stays where it lands and the
sift stops after one comparison, at 2.58 ns/op against 1.88 for the binary
heap. `insert-desc` is the opposite: every key is a new minimum and travels the
full height, at 520.98.

The beap is not a competitive priority queue and is not meant to be. What it
offers is the smallest structural invariant in the collection -- no tree, just
a triangular grid where the children of the node at index I in layer L are at
I + L and I + L + 1 and its parents at I - L and I - L + 1 -- and a heap whose
depth can be traded against its width.

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
