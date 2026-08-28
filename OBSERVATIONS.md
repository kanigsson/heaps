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
| leftist | 102.39 | 508.04 | 288.81 | 165.35 | 9.55 |
| skew | 130.42 | 376.45 | 238.22 | 301.17 | 7.64 |
| min-max | 13.04 | 174.84 | 88.13 | 12.66 | 13.66 |
| interval | 17.75 | 108.53 | 65.40 | 53.44 | 36.05 |

The two arena rows are from the later run that added the skew heap, so that the
pair can be compared against each other; the rest are as first measured. The
binary heap was re-measured in both and reproduces within 5% on every column,
which is what makes the two sets comparable at all.

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
something other than the number of comparisons. Its nodes live in an arena
shared by every tree of the instance, which is what makes its meld a splice;
the figures below are from the run made after the arena replaced the unit that
owned its pool. Against the binary heap, in the same run:

| n | `fill` | `drain` | `churn` | `replace-forward` | `insert-asc` | `insert-desc` |
|---|-------:|--------:|--------:|------------------:|-------------:|--------------:|
| 1_000 | 49.41 | 114.19 | 72.24 | 13.06 | 79.82 | 9.56 |
| 10_000 | 71.54 | 177.48 | 100.55 | 41.14 | 105.87 | 9.50 |
| 100_000 | 88.32 | 289.73 | 155.10 | 78.70 | 136.38 | 9.68 |
| 1_000_000 | 105.58 | 619.97 | 320.15 | 126.07 | 166.11 | 9.96 |
| binary at 1_000_000 | 10.01 | 92.69 | 50.76 | 24.30 | 1.93 | 11.06 |

The two ordered-input columns are the interesting ones, because they disagree
by a factor of twenty-two with each other and the reason is one comparison.
Inserting means merging a one-node heap into the heap, and a merge starts by
asking which of the two roots is smaller.

`insert-desc` gives the answer "the new one" every time. The new node becomes
the root, the old heap becomes its right subtree, and the merge is over: one
comparison, three writes, no walk at all. It is the only genuinely constant
insertion in the collection, and the numbers say so -- 9.56, 9.50, 9.68, 9.96
across three decades of size, flat to within half a nanosecond, against a
binary heap that climbs from 5.34 to 11.06 as its sift-up path lengthens. This is the
one column the leftist heap wins, and it wins it by more the larger the heap
gets.

`insert-asc` gives the opposite answer every time, and the merge then has to
walk the entire right spine to find where the new largest key belongs:
166.11 ns/op against 1.93 for the binary heap, a factor of eighty-six. The
spine is short -- the leftist condition holds it to at most log2 (n + 1), about
twenty nodes at `n = 1_000_000` -- so twenty is also roughly the number of
cache misses, because each step is a dependent load of a node the previous
step named. Eight nanoseconds a step is what a miss to main memory costs. The
structure is doing the asymptotically right thing and paying full price for
every level of it.

That is the general shape of the rest of the table. A node here carries a key,
two children, a parent and two counters: twenty-four bytes against the four an
implicit heap spends, so the pool is six times the size and a root-to-leaf walk
is six times as likely to leave cache at every step. `drain` is 6.7 times the
binary heap's and `churn` 6.3 times, and extraction pays twice over -- it
merges the two subtrees of the root, walking both spines, and then puts the
node it removed back on the free chain, from which the next insertion takes it
again. Slots are recycled rather than kept a prefix, so a long-lived tree ends
up scattered across the arena in an order the traversal has no reason to
follow.

`replace-forward` shows the same thing from the other end. At `n = 1_000` the
leftist heap is the *faster* of the two, 13.06 against 15.85: the replacement
key is only slightly above the minimum, so it settles near the top of the tree
and the walk is short. Three decades later the walk is no longer the cost --
the memory it walks over is -- and the same workload runs 5.2 times slower than
the binary heap.

None of this is an argument against the structure, because *this table* cannot
measure the thing it is for. A leftist heap melds two heaps of any size in
O(log n); every implicit heap in this collection has to rebuild, at O(n). That
column is the Meld section below, where it beats the binary heap by four orders
of magnitude on the workload the structure is for. What this table shows is the
price of buying that ability: outside `insert-desc`, an explicit tree in a pool
is between five and eighty-six times slower than the same tree implied by an
array index.

## Skew heap

The skew heap is the leftist heap with the rank field removed and the
conditional exchange of a node's two subtrees made unconditional. Nothing else
differs -- same arena, same free chain, same cached model, same contracts, and
a merge that is the same walk down the same two right spines -- so the pair
prices one design decision with everything else held fixed. What the rank field
buys is a worst-case bound: it holds a right spine to log2 (n + 1). What it
costs is a field per node and a comparison per step.

All figures below are from one run, and the leftist column is that run's:

| n | scenario | `leftist` | `skew` | ratio |
|---|----------|----------:|-------:|------:|
| 1 000 000 | `fill` | 102.39 | 130.42 | 1.27 |
| 1 000 000 | `drain` | 508.04 | 376.45 | 0.74 |
| 1 000 000 | `churn` | 288.81 | 238.22 | 0.82 |
| 1 000 000 | `replace-forward` | 115.14 | 77.29 | 0.67 |
| 1 000 000 | `insert-asc` | 165.35 | 301.17 | 1.82 |
| 1 000 000 | `insert-desc` | 9.55 | 7.64 | 0.80 |

The table divides in two, and the line it divides on is which operation the
workload spends its time in.

Everything dominated by *extraction* is faster without the rank field: at
`n = 1_000_000`, `drain` at 0.74, `churn` at 0.82 and `replace-forward` at
0.67. The advantage holds at every size measured and is largest at the small
end, where the pool still fits in cache and the saved comparison is the whole
of the difference: `drain` runs 0.62 at `n = 1_000` and rises to 0.74 by a
million. Two things pay for it and both are constants. A node is 16 bytes of
links plus a 4-byte key against the leftist node's 20 plus 4, so the pool is a
sixth smaller and a pointer walk takes a sixth fewer cache lines; and each step
of a merge no longer reads two ranks, compares them and writes one back. Neither is an asymptotic gain, and
the leftist section above is the reason they show up at all: what an explicit
tree costs is the memory it walks over, so a structure that walks over less of
it wins by more than the instruction count suggests.

Everything dominated by *insertion into a large tree* is slower, and that is
the rank field earning its keep. Insertion merges a one-node heap, so it walks
the right spine of the accumulator from the top until the new key finds its
place; the leftist condition is precisely the promise that this spine is short,
and the skew heap does not make it. `insert-asc` is the adversarial order --
every key is the new largest, so every insertion walks the whole spine -- and
it is where the two diverge:

| n | `leftist` | `skew` | ratio |
|---|----------:|-------:|------:|
| 1 000 | 74.44 | 49.68 | 0.67 |
| 10 000 | 101.62 | 81.25 | 0.80 |
| 100 000 | 132.98 | 133.33 | 1.00 |
| 1 000 000 | 165.35 | 301.17 | 1.82 |

That is the shape of an amortized bound losing to a worst-case one. Up to
`n = 10_000` the cheaper node and the absent comparison win outright; at
100 000 the two are level to the third digit; past that the spine the skew heap
declines to bound is longer than the constant factors can pay for, and the gap
widens with `n` rather than settling. The leftist column grows by 2.2 over three
decades, which is a spine growing like log n; the skew column grows by 6.1.
`fill` is the same effect on random input -- an insertion there walks until it
meets a larger key rather than to the end, so the penalty is 1.27 instead of
1.82, and it only appears above `n = 100_000`.

The amortized bound does hold. `insert-asc` at `n = 1_000_000` is a million
insertions in the worst order the structure has, and it completes in 301 ns
each; if the spine were growing linearly this column would be minutes rather
than 0.3 seconds. What the theory does not promise is any single merge, and
this unit merges recursively, so the depth of the recursion is the length of a
spine. Nothing here overflowed the default stack, `insert-asc` at a million
keys included, but that is a measurement and not a guarantee -- an arena of
this shape run at sizes well past this table, or on input chosen against it,
wants an iterative merge or a stack sized for the arena.

On `Meld` the two are the same structure doing the same thing.
`meld-accumulate` at `n = 1_000_000` is 1 198.75 against 1 185.69, within one
per cent, because the operands there are large and the spines of two large
trees are what both walk. `meld-into-full` folds sixteen *one-key* heaps into a
full accumulator, which is the insertion case again, and the skew heap pays the
same way: 171.25 against 130.00. Both remain four orders of magnitude ahead of
every heap that has to rebuild.

The proof came out the same way round: the skew unit is 154 checks against the
leftist unit's 165, and the eleven that are gone are the rank field's. See
PROOF.md.

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
| leftist | 126.07 |
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

Every entry in the catalogue has the operation. Five append and rebuild -- the
binary heap, the three d-ary instances, the weak heap, the min-max heap and the
interval heap; three insert the keys one at a time, because their insertion is
cheap enough that this is the better algorithm -- the unsorted array, the
block-min directory and the beap; the sorted array merges two runs; and the two
arenas splice.

`leftist` is `Heaps.Leftist_Pool`, an instance of the arena. The catalogue used
to carry a second unit holding the same tree in a pool of its own, and this
column is what decided which of the two to keep; the subsection at the end of
this chapter has that comparison and the figures it rested on.

A single meld is too fast to time against the cost of building its operands, so
both scenarios meld sixteen heaps into one accumulator and time the sixteen
melds. The figure is therefore nanoseconds per *meld*, not per key.
`meld-accumulate` starts from an empty accumulator and sixteen operands of
`n / 16` keys each, so the accumulator grows from `n / 16` to `n`.
`meld-into-full` prefills the accumulator with `n` keys and melds sixteen
one-key heaps into it.

| heap | n | `meld-accumulate` | `meld-into-full` |
|------|--:|------------------:|-----------------:|
| binary | 1 000 | 970.00 | 956.88 |
| binary | 10 000 | 13 549.56 | 12 842.69 |
| binary | 100 000 | 143 946.38 | 161 752.88 |
| binary | 1 000 000 | 1 392 644.32 | 1 641 240.96 |
| 4-ary | 1 000 | 742.50 | 1 082.50 |
| 4-ary | 10 000 | 8 062.56 | 10 498.31 |
| 4-ary | 100 000 | 73 352.31 | 104 929.56 |
| 4-ary | 1 000 000 | 719 375.04 | 1 093 493.28 |
| 8-ary | 1 000 | 716.31 | 1 131.25 |
| 8-ary | 10 000 | 6 882.00 | 11 172.00 |
| 8-ary | 100 000 | 70 309.69 | 118 977.88 |
| 8-ary | 1 000 000 | 751 359.84 | 1 258 669.36 |
| 16-ary | 1 000 | 788.75 | 1 337.50 |
| 16-ary | 10 000 | 7 710.75 | 13 095.81 |
| 16-ary | 100 000 | 75 912.31 | 130 571.20 |
| 16-ary | 1 000 000 | 760 984.32 | 1 314 302.64 |
| weak | 1 000 | 2 844.38 | 3 547.50 |
| weak | 10 000 | 38 361.19 | 67 444.69 |
| weak | 100 000 | 400 143.08 | 746 236.08 |
| weak | 1 000 000 | 3 952 742.08 | 7 343 960.32 |
| min-max | 1 000 | 4 915.06 | 7 944.50 |
| min-max | 10 000 | 58 031.44 | 115 096.62 |
| min-max | 100 000 | 584 549.36 | 1 075 603.12 |
| min-max | 1 000 000 | 5 835 120.00 | 10 539 224.96 |
| interval | 1 000 | 2 328.75 | 3 492.56 |
| interval | 10 000 | 23 182.81 | 33 804.19 |
| interval | 100 000 | 225 052.50 | 345 356.68 |
| interval | 1 000 000 | 2 240 038.72 | 3 435 181.12 |
| block-min | 1 000 | 148.13 | 5.00 |
| block-min | 10 000 | 1 466.25 | 5.63 |
| block-min | 100 000 | 14 754.00 | 6.25 |
| beap | 1 000 | 2 323.13 | 85.00 |
| beap | 10 000 | 44 623.75 | 73.13 |
| beap | 100 000 | 1 072 223.60 | 377.50 |
| unsorted | 1 000 | 50.00 | 3.75 |
| unsorted | 10 000 | 461.88 | 3.13 |
| sorted | 1 000 | 776.88 | 465.63 |
| sorted | 10 000 | 9 917.63 | 5 166.94 |
| leftist | 1 000 | 93.13 | 65.00 |
| leftist | 10 000 | 152.50 | 103.75 |
| leftist | 100 000 | 281.25 | 83.75 |
| leftist | 1 000 000 | 1 439.38 | 127.50 |
| skew | 1 000 | 47.50 | 53.13 |
| skew | 10 000 | 115.63 | 78.13 |
| skew | 100 000 | 246.25 | 103.75 |
| skew | 1 000 000 | 1 198.75 | 171.25 |

This table is from a later run than the main table above, re-measured in full
when the remaining six melds were added so that every figure in it comes from
one run. The machine and the switches are the same, and the entries that were
already there reproduce their earlier figures within about 15%. The `leftist`
row is later still: it was measured again when the arena became the only
leftist unit, and it replaces two rows, one per unit.

The single- and double-digit entries deserve a caveat the rest do not. A
measurement here is sixteen melds, so at those magnitudes the figure is a few
hundred nanoseconds of wall clock and the run-to-run spread is a factor of
several. What they establish is the absence of growth in `n`, not their own
second digit.

### The cost is set by the accumulator, not by the operand

Every rebuilding heap spends about the same time on the two scenarios, and that
is the finding. `meld-accumulate` melds operands of `n / 16` keys;
`meld-into-full` melds operands of *one* key. At `n = 1_000_000` the work
differs by a factor of sixty thousand and the time differs by less than a
factor of two, in favour of the scenario with the *larger* operands. An
implicit heap cannot splice, so it appends and rebuilds, and the rebuild is
over the accumulator. What arrives is irrelevant; what is already there is what
gets paid for.

The ratio between the two columns has a predicted value. `meld-accumulate`
rebuilds arrays of `n / 16`, `2n / 16`, ... `n`, which is 8.5 `n` of array
altogether; `meld-into-full` rebuilds `n` sixteen times over. A rebuild whose
cost is linear in the accumulator should therefore show `meld-into-full` at
1.88 times `meld-accumulate`. The three heaps added last are close to it at
`n = 1_000_000` -- 1.86 for the weak heap, 1.81 for the min-max heap, 1.53 for
the interval heap -- and the binary and d-ary heaps fall well short, at 1.18
and 1.5 to 1.7. The heaps whose rebuild does the most work per node are the
ones that behave like their own cost model; the cheaper ones spend enough of
their time on memory traffic that the two scenarios share to blur it.

### What a rebuild costs is what the rebuild does

The four rebuilding shapes separate cleanly, and the order is the order of how
much a single sift touches. At `n = 1_000_000` on `meld-accumulate`, against
the binary heap's 1 392 644:

- the **interval heap** is 2 240 039, 1.6 times. It pays one pass to make every
  pair of slots a well-formed interval, then sifts both ends of every node --
  two sifts per node against the binary heap's one -- but each sift compares
  against children only, one level at a time.
- the **weak heap** is 3 952 742, 2.8 times. Its build is one comparison per
  node, which is *half* the binary heap's, and it is still slower: what it
  spends instead is the climb that finds each node's distinguished ancestor,
  and the flip bit that a join has to write. Fewer comparisons, more pointer
  chasing.
- the **min-max heap** is 5 835 120, 4.2 times, and it is the slowest thing in
  the column. A trickle-down there examines children *and* grandchildren -- up
  to six keys to choose one -- and moves two levels at a time, so it touches
  three times the array per level descended.

The d-ary instances go the other way and beat the binary heap: 719 375 for
`4-ary` against 1 392 644. A bottom-up rebuild sifts once per *internal* node,
and a d-ary heap has `n / d` of them against the binary heap's `n / 2`. The
child scan that makes arity expensive for extraction is paid on far fewer nodes
here. It does not go on reversing -- `8-ary` and `16-ary` are level with
`4-ary` or slightly behind -- because the scan eventually outweighs having
fewer nodes to scan from.

The main table has higher arity costing *more*: `16-ary` pays 76.96 ns/op on
`replace-forward` against the binary heap's 27.44. Meld reverses it, for
exactly that reason.

### The block-min directory and the beap: when insertion is the better meld

Two entries do not rebuild at all, because their insertion is cheap enough that
inserting the keys one at a time is the better algorithm. They are the two ends
of how well that works.

The block-min directory's meld does not grow at all on `meld-into-full` -- 5.00,
5.63, 6.25 over three decades of `n` -- because its insertion is a store and at
most one directory entry. It is O(m) with no repair, and its extraction is
O(n / B + B) rather than the unsorted array's O(n), which makes it the one
structure here with a flat meld *and* a sub-linear extraction. The unsorted
array gets the same flat meld only by paying a linear extraction for it.

The beap is the interesting case, because its meld is the only figure in this
table that grows *faster* than linearly: 2 323, 44 624, 1 072 224 over three
decades, which is between a factor of 19 and a factor of 24 per decade against
the 10 a linear cost would give and the 31.6 of `n ** 1.5`. That is `m sqrt(n)`
with `m = n / 16`. It is still the right algorithm, and that is the point: a
bottom-up rebuild of a beap is *also* super-linear -- a node in layer L sifts
through the sqrt(n) - L layers below it, which sums to about 0.47 `n ** 1.5`
against repeated insertion's 0.088 -- so the structure that cannot rebuild
linearly is exactly the one for which the naive meld is best. `meld-into-full`
confirms it from the other side: 85.00, 73.13, 377.50, which is one O(sqrt n)
insertion and no rebuild at all.

### The sorted array merges, and a merge is a scan

The sorted array is the only entry whose meld is neither an append nor a
splice. Both its columns are linear in `n` and neither is flat, because a merge
of two runs rewrites the whole array however small the second run is: 465.63 to
5 166.94 on `meld-into-full` for a *one-key* operand.

What it buys for that is the best constant in the table. 5 166.94 ns to merge a
ten-thousand-key run is 0.5 ns per key, and the binary heap's rebuild of the
same array costs 12 842.69 -- two and a half times more for an operation with
the same asymptotic cost. A merge run backwards is two sequential reads and one
sequential write, which is the friendliest memory pattern here; a bottom-up
rebuild jumps between a node and its children.

### Who owns the pool, which is what the column was for

The catalogue carried two leftist units for a while. Both held the same tree
and differed only in who owned the node pool: `Heaps.Leftist` as it is now
shares one arena between every tree of the instance, and the unit that has
since been dropped gave each `Heap` object a pool of its own, so a meld had to
copy `From`'s nodes into the free slots at the end of `Into`'s pool, shifting
every index, before the splice. The two columns priced that copy exactly, and
the figures below are the measurement the decision was made on. They are from
the run in which both units still existed.

On `meld-into-full` the copy is one node, and the two were indistinguishable:
76.25, 120.00, 95.63, 131.25 for the private pool against 66.25, 107.50, 89.38,
134.38 for the arena. Both are flat in `n` -- three decades cost a factor under
two, which is what O(log n) looks like on a log scale of sizes -- and against
the binary heap's 1 641 241 at `n = 1_000_000` that is a factor of twelve
thousand. **The private pool cost nothing at all when the operand was small**,
which was not obvious before the measurement and is the more useful half of the
result: the API concession the arena demands buys nothing on this workload.

On `meld-accumulate` the copy is the whole operation: 436 532 against the
arena's 1 704 at `n = 1_000_000`, a factor of 256, and the private pool's
figure grows linearly in `n` -- 499, 4 527, 43 408, 436 532, a clean factor of
ten per decade -- while the arena's does not. That is O(m) against O(log n) laid
out over four decades, and it is why only one of the two units is still here.

Even so, the copying unit beat every rebuilding heap on that scenario too:
436 532 against the binary heap's 1 392 644 and the min-max heap's 5 835 120.
Copying `n / 16` nodes is less work than rebuilding `n` of them, so a leftist
heap that has to copy is still ahead of an implicit heap that has to rebuild --
by a factor of three against the best of them and thirteen against the worst.
The arena is a further two orders of magnitude beyond that.

`meld-accumulate` on the arena is worth a second look, because it is *not*
flat: in the current table 93.13, 152.50, 281.25, 1 439.38. That is not the
algorithm. The operands grow with `n`, so the two right spines the merge walks
grow from about six nodes to about sixteen -- a factor under three, against the
factor of fifteen measured. The rest is the pool. A node is 24 bytes, so the
live nodes are 240 KB at `n = 10_000` and 24 MB at `n = 1_000_000`, and the
jump between the last two rows is where the arena stops fitting in cache. A
merge is a pointer walk, and the main table's `leftist` row reports the same
effect on the same structure: what an explicit tree costs is not the
instruction count but the memory it walks over.

The one thing the table cannot show is that a meld in the arena moves nothing.
The arena's free count is unchanged across a meld -- no node is allocated,
freed or copied, the operation is a splice of two spines and nothing else --
which is checked at run time in `heaps_test` rather than timed here.

## Checksums

The implementations produce matching checksums for every shared scenario and
size. This checks that they process the same key stream and return the same
results while taking different internal paths.

The meld scenarios are checksummed the same way, over a drain of the melded
accumulator outside the timed phase, and all fourteen entries agree at every
size. Between them these melds are a bottom-up rebuild at four different
arities, a bottom-up build over distinguished ancestors, a two-level
trickle-down, a paired double-ended build, a block copy, three runs of single
insertions, a backwards merge of two sorted runs, a shifted copy of a node pool
and a splice of two right spines. They have very little in common beyond the
multiset they are supposed to produce, so the agreement is worth something. The
arenas are the useful ones to have in that set: they are the only entries that
never move a key, so they share no code path with any of the others beyond the
key stream itself. The two of them agree with each other on every scenario and
size as well, which is a check the pair gives for free -- they build very
different trees out of the same keys, and a wrong answer from either would have
to be a wrong answer that the other reproduced exactly.
