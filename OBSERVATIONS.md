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
open-buffered   1.10  █████████
open-proved     1.70  ██████████████
4-ary           1.79  ██████████████
pairing         1.89  ███████████████
8-ary           1.93  ███████████████
16-ary          2.12  █████████████████
min-max         2.13  █████████████████
weak            2.28  ██████████████████
interval        2.72  ██████████████████████
sorted          2.82  ███████████████████████
skew            3.38  ███████████████████████████
block-min       3.77  ██████████████████████████████
leftist         4.76  ██████████████████████████████████████
beap            4.83  ███████████████████████████████████████
unsorted        5.72  ██████████████████████████████████████████████

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 10 000, binary heap = 1.00. Lower is better.

open-proved     0.92  ███████
open-buffered   0.92  ███████
binary          1.00  ████████
pairing         1.65  █████████████
4-ary           1.67  █████████████
8-ary           1.68  █████████████
16-ary          1.87  ███████████████
min-max         2.02  ████████████████
weak            2.20  ██████████████████
interval        2.65  █████████████████████
block-min       2.86  ███████████████████████
skew            3.55  ████████████████████████████
leftist         5.06  ████████████████████████████████████████
sorted          6.81  ██████████████████████████████████████████████████████
beap            8.10  ████████████████████████████████████████████████████████████████+
unsorted       12.32  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 100 000, binary heap = 1.00. Lower is better.

open-proved     0.81  ██████
open-buffered   0.90  ███████
binary          1.00  ████████
4-ary           1.68  █████████████
8-ary           1.70  ██████████████
pairing         1.77  ██████████████
16-ary          1.86  ███████████████
min-max         2.11  █████████████████
weak            2.33  ███████████████████
interval        2.66  █████████████████████
block-min       4.31  ██████████████████████████████████
skew            4.95  ████████████████████████████████████████
leftist         5.96  ████████████████████████████████████████████████
beap           19.14  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

open-proved     0.74  ██████
open-buffered   0.89  ███████
binary          1.00  ████████
4-ary           1.62  █████████████
8-ary           1.63  █████████████
16-ary          1.73  ██████████████
pairing         1.85  ███████████████
min-max         2.12  █████████████████
weak            2.28  ██████████████████
interval        2.64  █████████████████████
skew            6.72  ██████████████████████████████████████████████████████
leftist         6.96  ████████████████████████████████████████████████████████
```

## Scenarios

### fill

```
fill -- ns/op on a log axis, 8 cells to a decade

unsorted       *·······················          2.08  at n = 10000
open-proved    *·······················          2.31  at n = 1000000
block-min      ·*······················          2.91  at n = 100000
open-buffered  ··*·····················          3.46  at n = 1000000
16-ary         ···**···················          6.36  at n = 1000000
pairing        ····*···················          6.45  at n = 1000000
8-ary          ···1*4··················          8.01  at n = 1000000
binary         ···1·*··················          9.85  at n = 1000000
4-ary          ····12*·················         10.61  at n = 1000000
min-max        ····1·*·················         13.16  at n = 1000000
interval       ·····1·*················         17.26  at n = 1000000
weak           ······1·*···············         20.29  at n = 1000000
leftist        ···········1234·········        101.90  at n = 1000000
skew           ···········1234·········        132.78  at n = 1000000
beap           ··········1···2···3·····        332.99  at n = 100000
sorted         ················1······2       1761.16  at n = 10000
```

### drain

```
drain -- ns/op on a log axis, 8 cells to a decade

sorted         *·····························          2.22  at n = 10000
binary         ········12·3·4················         92.54  at n = 1000000
4-ary          ··········1234················         93.63  at n = 1000000
interval       ··········1234················        106.91  at n = 1000000
8-ary          ···········1234···············        116.79  at n = 1000000
open-proved    ············23*···············        119.93  at n = 1000000
open-buffered  ···········1234···············        121.90  at n = 1000000
weak           ············1234··············        163.56  at n = 1000000
16-ary         ············1234··············        164.87  at n = 1000000
min-max        ············1234··············        170.68  at n = 1000000
pairing        ·············123·4············        322.95  at n = 1000000
skew           ············12·3··4···········        371.64  at n = 1000000
leftist        ·············1·2·3·4··········        492.94  at n = 1000000
beap           ·············1···2···3········        971.01  at n = 100000
block-min      ···················12··3······       1496.15  at n = 100000
unsorted       ·····················1·······2      10442.69  at n = 10000
```

### churn

```
churn -- ns/op on a log axis, 8 cells to a decade

binary         1·234···················         48.61  at n = 1000000
4-ary          ··12*···················         55.45  at n = 1000000
interval       ··1234··················         64.50  at n = 1000000
8-ary          ···1*4··················         67.42  at n = 1000000
open-buffered  ···1*4··················         67.94  at n = 1000000
open-proved    ····2*··················         71.65  at n = 1000000
weak           ····1*4·················         84.74  at n = 1000000
min-max        ···1234·················         85.31  at n = 1000000
16-ary         ····12*·················         87.22  at n = 1000000
pairing        ····123·4···············        159.08  at n = 1000000
skew           ····12·3··4·············        237.81  at n = 1000000
leftist        ·····12·3·4·············        268.44  at n = 1000000
beap           ······1··2····3·········        927.28  at n = 100000
block-min      ··········21···3········       1086.37  at n = 100000
sorted         ·······1·······2········       1218.65  at n = 10000
unsorted       ···············1·······2      10443.01  at n = 10000
```

### replace-forward

```
replace-forward -- ns/op on a log axis, 8 cells to a decade

sorted         1··2·························          6.60  at n = 10000
binary         ······1*·····················         23.03  at n = 1000000
4-ary          ········*····················         33.37  at n = 1000000
interval       ········1*···················         35.14  at n = 1000000
open-proved    ·········*21·················         42.43  at n = 1000000
8-ary          ·········*···················         44.74  at n = 1000000
open-buffered  ····1··23·4··················         53.21  at n = 1000000
min-max        ·······1234··················         57.71  at n = 1000000
16-ary         ·········12*·················         66.23  at n = 1000000
skew           ····1··2··34·················         74.57  at n = 1000000
pairing        ·····1··2·34·················         79.27  at n = 1000000
weak           ······1·2·34·················         80.46  at n = 1000000
leftist        ·····1···2·3·4···············        113.79  at n = 1000000
beap           ···········1···2···3·········        779.27  at n = 100000
block-min      ···············12····3·······       1160.13  at n = 100000
unsorted       ····················1·······2      10471.35  at n = 10000
```

### insert-asc

```
insert-asc -- ns/op on a log axis, 8 cells to a decade

binary         *··························          1.88  at n = 1000000
open-proved    *··························          1.94  at n = 1000000
unsorted       *··························          1.95  at n = 10000
block-min      *··························          2.14  at n = 100000
open-buffered  ·*·························          2.30  at n = 1000000
beap           ·*·························          2.61  at n = 100000
16-ary         ··1*·······················          4.80  at n = 1000000
weak           ···*2······················          5.00  at n = 1000000
8-ary          ··1*·······················          5.03  at n = 1000000
4-ary          ···*·······················          5.09  at n = 1000000
pairing        ····*······················          5.69  at n = 1000000
min-max        ····1234···················         12.56  at n = 1000000
interval       ········1234···············         48.22  at n = 1000000
leftist        ·············1234··········        164.24  at n = 1000000
skew           ···········1·2·3··4········        293.38  at n = 1000000
sorted         ··················1·······2       3506.56  at n = 10000
```

### insert-desc

```
insert-desc -- ns/op on a log axis, 8 cells to a decade

unsorted       *···················          1.94  at n = 10000
open-proved    *···················          2.02  at n = 1000000
sorted         ·*··················          2.33  at n = 10000
open-buffered  ·4*·················          2.86  at n = 1000000
block-min      1·*·················          3.48  at n = 100000
pairing        ····*···············          5.54  at n = 1000000
skew           ····**··············          7.47  at n = 1000000
leftist        ·····**·············          9.37  at n = 1000000
binary         ····1*4·············         10.84  at n = 1000000
min-max        ·····*34············         13.54  at n = 1000000
16-ary         ······1*4···········         19.39  at n = 1000000
weak           ·······1*4··········         25.50  at n = 1000000
8-ary          ······1·*4··········         27.09  at n = 1000000
interval       ·······1·*4·········         34.61  at n = 1000000
4-ary          ·······1·234········         39.53  at n = 1000000
beap           ············1··2···3        512.85  at n = 100000
```

### meld-accumulate

```
meld-accumulate -- ns/op on a log axis, 8 cells to a decade

pairing        12··3·4·········································         42.50  at n = 1000000
unsorted       ·······1······2·································        458.13  at n = 10000
leftist        ·········1·2·3····4·····························       1221.31  at n = 1000000
skew           ·······1·2··3·····4·····························       1232.50  at n = 1000000
sorted         ················1·······2·······················       8562.00  at n = 10000
block-min      ···········1······2·······3·····················      14789.56  at n = 100000
open-proved    ·······1······2·······3·······4·················      45576.25  at n = 1000000
open-buffered  ···········1·······2······3········4············     158670.88  at n = 1000000
4-ary          ················1·······2·······3·······4·······     715171.50  at n = 1000000
16-ary         ················1·······2·······3·······4·······     748968.19  at n = 1000000
8-ary          ················1·······2·······3·······4·······     752021.38  at n = 1000000
beap           ····················1·········2··········3······    1037750.81  at n = 100000
binary         ·················1········2·······3·······4·····    1396765.00  at n = 1000000
interval       ····················1·······2·······3·······4···    2219839.25  at n = 1000000
weak           ·····················1········2·······3·······4·    3936102.38  at n = 1000000
min-max        ······················1········2·······3·······4    5666506.25  at n = 1000000
```

### meld-into-full

```
meld-into-full -- ns/op on a log axis, 8 cells to a decade

open-proved    *···················································          4.38  at n = 1000000
unsorted       12··················································          6.25  at n = 10000
block-min      *··3················································          9.38  at n = 100000
open-buffered  ··*4················································         10.00  at n = 1000000
pairing        ··*···4·············································         28.13  at n = 1000000
leftist        ·········1·*4·······································        143.13  at n = 1000000
skew           ·········12·34······································        185.63  at n = 1000000
beap           ··········*····3····································        354.38  at n = 100000
sorted         ················1·······2···························       5015.69  at n = 10000
4-ary          ···················1·······2·······3·······4········    1093048.50  at n = 1000000
8-ary          ···················1·······2·······3········4·······    1242849.25  at n = 1000000
16-ary         ····················1·······2·······3·······4·······    1283104.19  at n = 1000000
binary         ···················1········2········3·······4······    1700445.38  at n = 1000000
interval       ·······················1·······2·······3·······4····    3416578.44  at n = 1000000
weak           ·······················1··········2·······3·······4·    7275666.06  at n = 1000000
min-max        ··························1········2·······3·······4   10043642.63  at n = 1000000
```

### drain-max

```
drain-max -- ns/op on a log axis, 8 cells to a decade

interval       1234··        118.47  at n = 1000000
open-proved    ··23*·        129.80  at n = 1000000
open-buffered  ·1234·        130.75  at n = 1000000
min-max        ··1234        189.08  at n = 1000000
```

### drain-both

```
drain-both -- ns/op on a log axis, 8 cells to a decade

interval       1234··        113.99  at n = 1000000
open-buffered  ·1234·        128.70  at n = 1000000
open-proved    ··23*·        130.85  at n = 1000000
min-max        ··1234        199.43  at n = 1000000
```

### trim

```
trim -- ns/op on a log axis, 8 cells to a decade

open-buffered  ·1*4·         70.80  at n = 1000000
interval       1234·         73.08  at n = 1000000
open-proved    ··**·         80.96  at n = 1000000
min-max        ·1234         99.38  at n = 1000000
```

## Checksums

Every entry accumulates a checksum over the keys a scenario makes
it see, so entries taking different internal paths over one key
stream owe the same answer.

Groups compared (one per scenario and size): 44.
Disagreements: none.
