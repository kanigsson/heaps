# Benchmark results

Nanoseconds per operation, the fastest of five runs, from one
run of the whole suite on an AMD Ryzen 9 3950X with GNAT Pro 27.0w at -O2.

This file is generated. To remake it:

```sh
gprbuild -P bench.gpr
./bench_main --machine="an AMD Ryzen 9 3950X with GNAT Pro 27.0w at -O2" \
  --markdown=OBSERVATIONS.md --json=docs/results.js
```

For a view whose metric, sizes and entries can be chosen, open
[docs/index.html](docs/index.html) from a checkout, or the same
page over GitHub Pages where the repository has it enabled.

## How to read the charts

Each row is one heap, placed on an axis of nanoseconds per
operation that runs left to right, low to high. The axis is
logarithmic and shared by every row of its chart, so distance
along it is a ratio: eight cells is a factor of ten.

A digit is a size.
- `1` is n = 1 000
- `2` is n = 10 000
- `3` is n = 100 000
- `4` is n = 1 000 000

A `*` is two or more sizes landing on the same cell, which is
a scenario whose cost does not grow over that stretch. The
spread of the digits is therefore the growth: eight cells per
decade of `n` is linear, four is `sqrt n`, one or two is
logarithmic, and none at all is constant. Rows are ordered by
the figure at the largest size the entry was run at, which the
last column names, since not every entry runs at every size.

A meld figure is nanoseconds per *meld* rather than per key,
and one measurement is sixteen melds.

## Overall

Cost relative to the binary heap, as the geometric mean of the
ratio on each single-heap scenario.

```

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000, binary heap = 1.00. Lower is better.

binary          1.00  ████████
open-buffered   1.06  ████████
open-proved     1.66  █████████████
4-ary           1.78  ██████████████
pairing         1.85  ███████████████
8-ary           1.89  ███████████████
min-max         1.98  ████████████████
16-ary          2.09  █████████████████
weak            2.20  ██████████████████
interval        2.58  █████████████████████
sorted          2.72  ██████████████████████
skew            3.38  ███████████████████████████
block-min       3.68  █████████████████████████████
leftist         4.67  █████████████████████████████████████
beap            4.76  ██████████████████████████████████████
unsorted        5.52  ████████████████████████████████████████████
tournament     15.38  ████████████████████████████████████████████████████████████████+
min-max tournam45.51  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 10 000, binary heap = 1.00. Lower is better.

open-buffered   0.90  ███████
open-proved     0.90  ███████
binary          1.00  ████████
pairing         1.64  █████████████
8-ary           1.66  █████████████
4-ary           1.67  █████████████
16-ary          1.85  ███████████████
min-max         1.90  ███████████████
weak            2.15  █████████████████
interval        2.51  ████████████████████
block-min       2.86  ███████████████████████
skew            3.53  ████████████████████████████
leftist         4.97  ████████████████████████████████████████
sorted          6.61  █████████████████████████████████████████████████████
beap            8.06  ████████████████████████████████████████████████████████████████
tournament     10.94  ████████████████████████████████████████████████████████████████+
unsorted       11.85  ████████████████████████████████████████████████████████████████+
min-max tournam18.51  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 100 000, binary heap = 1.00. Lower is better.

open-proved     0.80  ██████
open-buffered   0.89  ███████
binary          1.00  ████████
8-ary           1.72  ██████████████
4-ary           1.73  ██████████████
pairing         1.80  ██████████████
16-ary          1.89  ███████████████
min-max         2.03  ████████████████
weak            2.33  ███████████████████
interval        2.60  █████████████████████
block-min       4.38  ███████████████████████████████████
skew            5.01  ████████████████████████████████████████
leftist         6.09  █████████████████████████████████████████████████
tournament     10.38  ████████████████████████████████████████████████████████████████+
min-max tournam15.32  ████████████████████████████████████████████████████████████████+
beap           19.10  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

open-proved     0.73  ██████
open-buffered   0.90  ███████
binary          1.00  ████████
8-ary           1.63  █████████████
4-ary           1.64  █████████████
16-ary          1.73  ██████████████
min-max         2.09  █████████████████
pairing         2.19  ██████████████████
weak            2.23  ██████████████████
interval        2.67  █████████████████████
skew            7.00  ████████████████████████████████████████████████████████
leftist         7.42  ███████████████████████████████████████████████████████████
tournament      9.07  ████████████████████████████████████████████████████████████████+
min-max tournam14.33  ████████████████████████████████████████████████████████████████+
```

## Scenarios

### fill

```
fill -- ns/op on a log axis, 8 cells to a decade

unsorted       *·······················          2.13  at n = 10000
open-proved    *·······················          2.35  at n = 1000000
block-min      ·*······················          3.08  at n = 100000
open-buffered  ··*·····················          3.81  at n = 1000000
16-ary         ···**···················          6.73  at n = 1000000
8-ary          ···12*··················          8.35  at n = 1000000
pairing        ····*4··················          8.66  at n = 1000000
binary         ···1·*··················         10.19  at n = 1000000
4-ary          ····12*·················         11.27  at n = 1000000
min-max        ····1·*·················         13.25  at n = 1000000
interval       ·····1·*················         17.59  at n = 1000000
weak           ······1·*···············         20.73  at n = 1000000
leftist        ···········1234·········        105.78  at n = 1000000
tournament     ··············*·········        122.34  at n = 1000000
skew           ···········123·4········        151.25  at n = 1000000
min-max tournam···············*·1······        180.57  at n = 1000000
beap           ··········1···2···3·····        339.95  at n = 100000
sorted         ················1······2       1801.15  at n = 10000
```

### drain

```
drain -- ns/op on a log axis, 8 cells to a decade

sorted         *·····························          2.29  at n = 10000
binary         ········12·3·4················         96.18  at n = 1000000
4-ary          ··········1234················        103.32  at n = 1000000
interval       ··········123·4···············        116.06  at n = 1000000
8-ary          ···········1234···············        124.94  at n = 1000000
open-buffered  ···········1234···············        127.67  at n = 1000000
open-proved    ············23*···············        129.85  at n = 1000000
16-ary         ············1234··············        172.96  at n = 1000000
weak           ············1234··············        173.20  at n = 1000000
min-max        ············1234··············        173.22  at n = 1000000
tournament     ················1*············        309.60  at n = 1000000
pairing        ·············12·3·4···········        436.20  at n = 1000000
skew           ············12··3··4··········        512.85  at n = 1000000
min-max tournam··················3*1·········        553.12  at n = 1000000
leftist        ·············1·2·3··4·········        637.30  at n = 1000000
beap           ·············1···2···3········       1075.84  at n = 100000
block-min      ···················1·2·3······       1584.11  at n = 100000
unsorted       ·····················1·······2      10649.18  at n = 10000
```

### churn

```
churn -- ns/op on a log axis, 8 cells to a decade

binary         1·234···················         51.63  at n = 1000000
4-ary          ··1234··················         60.83  at n = 1000000
interval       ··1234··················         69.32  at n = 1000000
open-buffered  ···1*4··················         70.33  at n = 1000000
8-ary          ···12*··················         73.26  at n = 1000000
open-proved    ····**··················         77.15  at n = 1000000
weak           ····1*4·················         89.16  at n = 1000000
min-max        ···1234·················         91.48  at n = 1000000
16-ary         ····12*·················         91.89  at n = 1000000
tournament     ········*···············        179.73  at n = 1000000
pairing        ····12·3·4··············        208.53  at n = 1000000
min-max tournam·········2*1············        320.29  at n = 1000000
leftist        ·····12·3··4············        327.34  at n = 1000000
skew           ····12·3···4············        341.09  at n = 1000000
beap           ······1··2····3·········        983.52  at n = 100000
block-min      ··········21···3········       1157.47  at n = 100000
sorted         ·······1·······2········       1248.27  at n = 10000
unsorted       ···············1·······2      10649.07  at n = 10000
```

### replace-forward

```
replace-forward -- ns/op on a log axis, 8 cells to a decade

sorted         1··2·························          6.85  at n = 10000
binary         ······1*·····················         24.60  at n = 1000000
4-ary          ········1*···················         35.34  at n = 1000000
interval       ········1*···················         35.68  at n = 1000000
open-proved    ·········*21·················         43.29  at n = 1000000
8-ary          ·········*4··················         47.20  at n = 1000000
open-buffered  ····1··23·4··················         54.95  at n = 1000000
min-max        ·······123·4·················         61.58  at n = 1000000
16-ary         ·········1·*·················         69.02  at n = 1000000
weak           ······1·2·3·4················         83.83  at n = 1000000
pairing        ·····1··2·3·4················         85.82  at n = 1000000
skew           ····1··2··3·4················         88.40  at n = 1000000
leftist        ·····1···2·3·4···············        128.84  at n = 1000000
tournament     ·············**··············        176.12  at n = 1000000
min-max tournam···············*41···········        314.13  at n = 1000000
beap           ···········1···2···3·········        780.62  at n = 100000
block-min      ···············1·2···3·······       1232.30  at n = 100000
unsorted       ····················1·······2      10645.17  at n = 10000
```

### insert-asc

```
insert-asc -- ns/op on a log axis, 8 cells to a decade

unsorted       *··························          1.95  at n = 10000
open-proved    *··························          1.97  at n = 1000000
binary         *··························          1.98  at n = 1000000
block-min      *··························          2.23  at n = 100000
open-buffered  ·*·························          2.60  at n = 1000000
beap           ·*·························          2.63  at n = 100000
weak           ···*·······················          4.92  at n = 1000000
16-ary         ··1*·······················          5.07  at n = 1000000
8-ary          ··1*·······················          5.22  at n = 1000000
4-ary          ···*·······················          5.24  at n = 1000000
pairing        ····*······················          5.84  at n = 1000000
min-max        ····1234···················         12.83  at n = 1000000
interval       ········123·4··············         56.34  at n = 1000000
tournament     ··············*············        120.53  at n = 1000000
min-max tournam···············*·1·········        148.59  at n = 1000000
leftist        ·············12*···········        168.15  at n = 1000000
skew           ···········1·23·4··········        175.41  at n = 1000000
sorted         ··················1·······2       3600.90  at n = 10000
```

### insert-desc

```
insert-desc -- ns/op on a log axis, 8 cells to a decade

unsorted       *···················          1.94  at n = 10000
open-proved    *···················          2.05  at n = 1000000
sorted         ·*··················          2.31  at n = 10000
open-buffered  ·2*·················          3.03  at n = 1000000
block-min      1·*·················          3.63  at n = 100000
pairing        ····*4··············          7.77  at n = 1000000
skew           ·····*··············          8.02  at n = 1000000
leftist        ······*·············          9.71  at n = 1000000
binary         ····12*·············         11.33  at n = 1000000
min-max        ·····*34············         13.87  at n = 1000000
16-ary         ······12*···········         20.15  at n = 1000000
weak           ·······1*4··········         25.83  at n = 1000000
8-ary          ······1·2*··········         28.06  at n = 1000000
interval       ·······1234·········         35.81  at n = 1000000
4-ary          ········1234········         41.08  at n = 1000000
tournament     ··············*·····        107.60  at n = 1000000
min-max tournam···············*·1··        161.82  at n = 1000000
beap           ············1··2···3        523.84  at n = 100000
```

### meld-accumulate

```
meld-accumulate -- ns/op on a log axis, 8 cells to a decade

pairing        12·3····4·········································         61.25  at n = 1000000
unsorted       ·······1·······2··································        450.06  at n = 10000
skew           ·······1··2··3·····4······························       1308.19  at n = 1000000
leftist        ··········12·3·····4······························       1543.81  at n = 1000000
sorted         ················1········2························       8511.38  at n = 10000
block-min      ···········1·······2·······3······················      14920.19  at n = 100000
open-proved    ·······1·······2·······3·······4··················      45883.13  at n = 1000000
open-buffered  ···········1·······2·······3········4·············     183060.00  at n = 1000000
4-ary          ················1·······2·······3·······4·········     714973.38  at n = 1000000
8-ary          ·················1······2·······3········4········     743736.25  at n = 1000000
16-ary         ·················1·······2·······3·······4········     767075.94  at n = 1000000
beap           ····················1··········2··········3·······    1037745.19  at n = 100000
binary         ··················1········2·······3·······4······    1407492.06  at n = 1000000
interval       ····················1········2······3·······4·····    2244513.38  at n = 1000000
weak           ·····················1········2·······3·······4···    3839629.75  at n = 1000000
tournament     ·············································2*·4·    5526486.88  at n = 1000000
min-max        ·······················1········2·······3·······4·    5783111.56  at n = 1000000
min-max tournam················································*4    9380175.56  at n = 1000000
```

### meld-into-full

```
meld-into-full -- ns/op on a log axis, 8 cells to a decade

unsorted       *····················································          3.75  at n = 10000
open-proved    ·*4··················································          6.25  at n = 1000000
pairing        ··*··················································          7.50  at n = 1000000
block-min      ·*·3·················································          8.13  at n = 100000
open-buffered  ··2*·················································          9.38  at n = 1000000
leftist        ··········13*········································        131.25  at n = 1000000
skew           ·········1·23·4······································        201.25  at n = 1000000
beap           ··········21····3····································        356.88  at n = 100000
sorted         ·················1·······2···························       5043.81  at n = 10000
4-ary          ····················1·······2·······3·······4········    1107320.50  at n = 1000000
8-ary          ····················1·······2·······3·······4········    1249968.13  at n = 1000000
16-ary         ····················1·······2·······3·······4········    1318840.25  at n = 1000000
binary         ·····················1·······2·······3·······4·······    1656577.94  at n = 1000000
interval       ························1·······2·······3·······4····    3400418.25  at n = 1000000
weak           ························1·········2·······3·······4··    7516959.94  at n = 1000000
tournament     ···············································*3··4·    7873841.56  at n = 1000000
min-max        ··························1········2·······3········4   10429734.75  at n = 1000000
min-max tournam··················································*·4   12690205.19  at n = 1000000
```

### drain-max

```
drain-max -- ns/op on a log axis, 8 cells to a decade

interval       123·4······        128.51  at n = 1000000
open-buffered  ·1234······        133.94  at n = 1000000
open-proved    ··23*······        141.75  at n = 1000000
min-max        ··1234·····        193.43  at n = 1000000
min-max tournam········3*1        541.79  at n = 1000000
```

### drain-both

```
drain-both -- ns/op on a log axis, 8 cells to a decade

interval       123·4······        122.25  at n = 1000000
open-buffered  ·1234······        133.86  at n = 1000000
open-proved    ··23*······        135.35  at n = 1000000
min-max        ··1·*4·····        198.91  at n = 1000000
min-max tournam········3*1        554.75  at n = 1000000
```

### trim

```
trim -- ns/op on a log axis, 8 cells to a decade

open-buffered  ·1*4······         72.98  at n = 1000000
interval       1234······         78.19  at n = 1000000
open-proved    ··**······         84.44  at n = 1000000
min-max        ·1234·····         99.63  at n = 1000000
min-max tournam·······*41        291.04  at n = 1000000
```

## Checksums

Every entry accumulates a checksum over the keys a scenario makes
it see, so entries taking different internal paths over one key
stream owe the same answer.

Groups compared (one per scenario and size): 44.
Disagreements: none.
