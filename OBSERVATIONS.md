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
| leftist | 98.39 | 428.02 | 285.98 | 168.67 | 7.67 |
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

## Leftist heap

The leftist heap is the first structure here whose tree is a pool of linked
nodes rather than an array index, and the first whose costs are dominated by
something other than the number of comparisons. Against the binary heap, in
the same run:

| n | `fill` | `drain` | `churn` | `replace-forward` | `insert-asc` | `insert-desc` |
|---|-------:|--------:|--------:|------------------:|-------------:|--------------:|
| 1_000 | 43.32 | 146.30 | 82.33 | 12.55 | 69.22 | 6.97 |
| 10_000 | 63.86 | 214.11 | 113.97 | 43.18 | 98.29 | 6.99 |
| 100_000 | 81.68 | 294.09 | 158.63 | 84.14 | 130.12 | 7.53 |
| 1_000_000 | 98.39 | 428.02 | 285.98 | 131.97 | 168.67 | 7.67 |
| binary at 1_000_000 | 10.09 | 93.17 | 47.91 | 24.55 | 1.96 | 11.47 |

The two ordered-input columns are the interesting ones, because they disagree
by a factor of twenty-two with each other and the reason is one comparison.
Inserting means merging a one-node heap into the heap, and a merge starts by
asking which of the two roots is smaller.

`insert-desc` gives the answer "the new one" every time. The new node becomes
the root, the old heap becomes its right subtree, and the merge is over: one
comparison, three writes, no walk at all. It is the only genuinely constant
insertion in the collection, and the numbers say so -- 6.97, 6.99, 7.53, 7.67
across three decades of size, flat to within a nanosecond, against a binary
heap that climbs from 6.80 to 11.47 as its sift-up path lengthens. This is the
one column the leftist heap wins, and it wins it by more the larger the heap
gets.

`insert-asc` gives the opposite answer every time, and the merge then has to
walk the entire right spine to find where the new largest key belongs:
168.67 ns/op against 1.96 for the binary heap, a factor of eighty-six. The
spine is short -- the leftist condition holds it to at most log2 (n + 1), about
twenty nodes at `n = 1_000_000` -- so twenty is also roughly the number of
cache misses, because each step is a dependent load of a node the previous
step named. Eight nanoseconds a step is what a miss to main memory costs. The
structure is doing the asymptotically right thing and paying full price for
every level of it.

That is the general shape of the rest of the table. A node here carries a key,
two children, a parent and two counters: twenty-four bytes against the four an
implicit heap spends, so the pool is six times the size and a root-to-leaf walk
is six times as likely to leave cache at every step. `drain` is 4.6 times the
binary heap's and `churn` 6 times, and extraction pays twice over -- it merges
the two subtrees of the root, walking both spines, and then moves the last node
of the pool into the hole to keep the used slots a prefix, which touches three
more nodes scattered anywhere in the array.

`replace-forward` shows the same thing from the other end. At `n = 1_000` the
leftist heap is the *faster* of the two, 12.55 against 16.12: the replacement
key is only slightly above the minimum, so it settles near the top of the tree
and the walk is short. Three decades later the walk is no longer the cost --
the memory it walks over is -- and the same workload runs 5.4 times slower than
the binary heap.

None of this is an argument against the structure, because the benchmark cannot
measure the thing it is for. A leftist heap melds two heaps of any size in
O(log n); every implicit heap in this collection would have to rebuild, at
O(n). The API here has no meld operation, so the one column where the leftist
heap is asymptotically better than everything else it is being compared against
is not in the table. What the table does show is the price of buying that
ability: outside `insert-desc`, an explicit tree in a pool is between four and
eighty-six times slower than the same tree implied by an array index.

## Forward replacement

`replace-forward` models queues whose priorities advance: it extracts the
minimum and replaces it with that key plus a positive pseudo-random increment.
The size stays fixed, as in merging sorted streams, recurring scheduling and
event queues that schedule a successor for each event. Unlike `churn`, the
replacement is always later than the item it replaces.

Results for the verified logarithmic structures at `n = 1_000_000`:

| heap | ns/op |
|------|------:|
| binary | 27.44 |
| 4-ary | 40.24 |
| 8-ary | 50.68 |
| 16-ary | 76.96 |
| weak | 98.98 |
| leftist | 131.97 |
| min-max | 61.57 |
| interval | 36.33 |

The binary heap is the fastest general-purpose structure for this pattern. The
sorted-array baseline is faster over its limited range, at 4.10 ns/op for
`n = 1_000` and 7.01 for `n = 10_000`: replacements remain near the minimum
end of the array, so this workload avoids its expensive general insertion
case. The block-min directory reaches 1278.86 ns/op at `n = 100_000`, against
28.39 for binary; cheap forward insertion does not offset directory scans and
block repairs on every extraction.

## Block-min directory

The block-min directory runs through `n = 100_000`, like the beap. Its fixed
block size is 256 keys.

| n | `fill` | `drain` | `churn` | `insert-asc` | `insert-desc` |
|---|-------:|--------:|--------:|-------------:|--------------:|
| 1_000 | 3.02 | 589.42 | 395.88 | 2.20 | 2.22 |
| 10_000 | 3.07 | 826.44 | 276.44 | 2.20 | 3.58 |
| 100_000 | 3.04 | 1572.07 | 1142.19 | 2.20 | 3.58 |

Insertion stays near three nanoseconds per key because it appends to the
unsorted key array and compares against one block winner. It is more than
three times faster than binary-heap filling at `n = 100_000`, and descending
input is the only ordered case that repeatedly replaces a winner.

Extraction pays for both sides of the directory trade-off. It scans `n / 256`
winner indices to choose a block, then scans up to 256 keys for each affected
block after the last key fills the removed slot. At `n = 10_000`, that reduces
`drain` from the unsorted baseline's 10745.01 ns/op to 826.44 and `churn` from
10710.01 to 276.44. The directory is already thirteen times better than a full
array scan there.

Against trees, the same numbers show the cost of refusing to maintain a
global shape. At `n = 100_000`, the binary heap drains in 50.70 ns/op and the
beap in 1011.11, versus 1572.07 for the directory. The directory is therefore
useful as a small, very cheap insertion index over an otherwise unsorted
buffer, not as a replacement for a logarithmic heap under sustained removal.

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

## Meld

Six entries have the operation so far: the binary heap and the three d-ary
instances, which append and rebuild; the unsorted array, which appends and
repairs nothing; and the block-min directory, which inserts the keys one at a
time because its insertion is already O(1). See the Planned operations section of README.md for the rest,
and for why the leftist heap, the structure the column exists for, is not here
yet.

A single meld is too fast to time against the cost of building its operands, so
both scenarios meld sixteen heaps into one accumulator and time the sixteen
melds. The figure is therefore nanoseconds per *meld*, not per key.
`meld-accumulate` starts from an empty accumulator and sixteen operands of
`n / 16` keys each, so the accumulator grows from `n / 16` to `n`.
`meld-into-full` prefills the accumulator with `n` keys and melds sixteen
one-key heaps into it.

| heap | n | `meld-accumulate` | `meld-into-full` |
|------|--:|------------------:|-----------------:|
| binary | 1 000 | 1 037.56 | 985.69 |
| binary | 10 000 | 13 705.19 | 13 682.69 |
| binary | 100 000 | 144 479.44 | 174 584.88 |
| binary | 1 000 000 | 1 422 271.68 | 1 728 768.96 |
| 4-ary | 1 000 | 719.38 | 1 075.63 |
| 4-ary | 10 000 | 7 010.69 | 10 498.25 |
| 4-ary | 100 000 | 69 139.06 | 104 180.19 |
| 4-ary | 1 000 000 | 711 929.60 | 1 076 158.40 |
| 8-ary | 1 000 | 697.50 | 1 143.75 |
| 8-ary | 10 000 | 6 751.94 | 11 228.25 |
| 8-ary | 100 000 | 70 214.13 | 122 621.62 |
| 8-ary | 1 000 000 | 734 911.12 | 1 268 246.48 |
| 16-ary | 1 000 | 800.06 | 1 353.13 |
| 16-ary | 10 000 | 7 786.94 | 13 349.56 |
| 16-ary | 100 000 | 77 491.06 | 133 191.81 |
| 16-ary | 1 000 000 | 775 543.04 | 1 340 156.88 |
| block-min | 1 000 | 143.75 | 5.63 |
| block-min | 10 000 | 1 441.25 | 5.63 |
| block-min | 100 000 | 14 302.69 | 9.38 |
| unsorted | 1 000 | 46.25 | 3.13 |
| unsorted | 10 000 | 443.75 | 3.13 |

### The cost is set by the accumulator, not by the operand

Every rebuilding heap spends about the same time on the two scenarios, and that
is the finding. `meld-accumulate` melds operands of `n / 16` keys;
`meld-into-full` melds operands of *one* key. At `n = 1_000_000` the work
differs by a factor of sixty thousand and the time does not differ at all --
`meld-into-full` is consistently the *slower* of the two, by 20% for the binary
heap and 50% for the d-ary ones. An implicit heap cannot splice, so it appends
and rebuilds, and the rebuild is over the accumulator. What arrives is
irrelevant; what is already there is what gets paid for. The reason
`meld-into-full` is worse rather than merely equal is that its accumulator is
the full `n` from the first meld onwards, while `meld-accumulate` grows into it.

The unsorted array is the other side of it. Appending one key to a
million-key array is a store, so `meld-into-full` is 3.13 ns and flat in `n` --
the same number at `n = 1_000` and at `n = 10_000`, and it would be the same at
`n = 1_000_000`. Against the binary heap's 1.73 million nanoseconds per meld at
that size this is a factor of half a million, and none of it is constant
factor: it is O(1) against O(n).

### The block-min directory is the interesting one

The unsorted array's flat meld comes at the price of a linear `Extract_Min`, so
it wins this column and loses every other one. The block-min directory does not
make that trade. Its meld is flat in the same way -- 5.63 ns at `n = 1_000` and
`n = 10_000`, 9.38 at `n = 100_000` -- because its insertion is a store and at
most one directory entry, so melding is O(m) with no repair. But its extraction
is O(n / B + B) rather than O(n), which is 14 302 ns/meld on `meld-accumulate`
at `n = 100_000` against the binary heap's 144 479.

That makes it the first structure here with a flat meld *and* a sub-linear
extraction, which is much closer to a mergeable heap's profile than the
unsorted baseline is. It gets there by a different route -- keeping the keys
unsorted and paying at extraction, rather than keeping a tree and paying at the
merge -- but for a workload that melds far more often than it extracts, it is
the entry to beat rather than the binary heap.

That is the shape a mergeable heap would show, which is what makes the
degenerate baseline worth having in this column before the real thing arrives.
The leftist heap would sit between the two -- O(log n) rather than the unsorted
array's O(1) for a one-key operand, but O(log n) rather than O(n + m) for a
large one, which is the case the unsorted array cannot win because its
`Extract_Min` is linear. Until it is there, the column shows that the price of a
meld on an implicit heap is set by the accumulator and not by the operand, and
that this is not a small effect.

### Arity reverses

The main table has higher arity costing more: extraction scans all `d` children
at every level, and `16-ary` pays 76.96 ns/op on `replace-forward` against the
binary heap's 27.44. Meld reverses it. Every d-ary instance melds faster than
the binary heap, by a factor of two on `meld-accumulate` at `n = 1_000_000`:
711 929 ns for `4-ary` against 1 422 271 for `binary`.

The reason is that a bottom-up rebuild sifts once per *internal* node, and a
d-ary heap has `n / d` of them against the binary heap's `n / 2`. Fewer sifts,
each over a tree of depth `log_d n` rather than `log_2 n`. Both effects favour
higher arity, and the child scan that makes arity expensive for extraction is
paid on far fewer nodes here.

It does not go on reversing: `4-ary` and `8-ary` are close, and `16-ary` is
slower than both, because the scan of sixteen children eventually outweighs
having a sixteenth as many nodes to scan from. The optimum for this workload is
somewhere around eight, which is roughly where the main table's `fill` column
puts it too -- filling and rebuilding are the two operations here whose cost is
dominated by sift-downs that mostly terminate early.

## Checksums

The implementations produce matching checksums for every shared scenario and
size. This checks that they process the same key stream and return the same
results while taking different internal paths.

The meld scenarios are checksummed the same way, over a drain of the melded
accumulator outside the timed phase, and all five entries agree at every size.
Implementations whose melds are a bottom-up rebuild at four different arities
and a block copy have very little in common beyond the multiset they are
supposed to produce, so the agreement is worth something.
