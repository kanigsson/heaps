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
open-buffered   1.07  █████████
open-proved     1.68  █████████████
4-ary           1.76  ██████████████
8-ary           1.89  ███████████████
pairing         1.89  ███████████████
16-ary          2.08  █████████████████
min-max         2.12  █████████████████
weak            2.19  █████████████████
interval        2.65  █████████████████████
sorted          2.74  ██████████████████████
skew            3.31  ██████████████████████████
block-min       3.66  █████████████████████████████
leftist         4.61  █████████████████████████████████████
beap            4.68  █████████████████████████████████████
unsorted        5.53  ████████████████████████████████████████████
tournament     16.27  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 10 000, binary heap = 1.00. Lower is better.

open-buffered   0.89  ███████
open-proved     0.90  ███████
binary          1.00  ████████
pairing         1.60  █████████████
8-ary           1.62  █████████████
4-ary           1.63  █████████████
16-ary          1.83  ███████████████
min-max         2.00  ████████████████
weak            2.14  █████████████████
interval        2.59  █████████████████████
block-min       2.81  ██████████████████████
skew            3.42  ███████████████████████████
leftist         4.93  ███████████████████████████████████████
sorted          6.67  █████████████████████████████████████████████████████
beap            7.83  ███████████████████████████████████████████████████████████████
tournament     11.65  ████████████████████████████████████████████████████████████████+
unsorted       11.78  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 100 000, binary heap = 1.00. Lower is better.

open-proved     0.82  ███████
open-buffered   0.91  ███████
binary          1.00  ████████
8-ary           1.72  ██████████████
4-ary           1.73  ██████████████
pairing         1.83  ███████████████
16-ary          1.91  ███████████████
min-max         2.20  ██████████████████
weak            2.37  ███████████████████
interval        2.73  ██████████████████████
block-min       4.41  ███████████████████████████████████
skew            4.94  ████████████████████████████████████████
leftist         6.25  ██████████████████████████████████████████████████
tournament     10.92  ████████████████████████████████████████████████████████████████+
beap           19.12  ████████████████████████████████████████████████████████████████+

Relative cost, geometric mean of the 6 single-heap scenarios at
n = 1 000 000, binary heap = 1.00. Lower is better.

open-proved     0.74  ██████
open-buffered   0.91  ███████
binary          1.00  ████████
8-ary           1.63  █████████████
4-ary           1.63  █████████████
16-ary          1.74  ██████████████
min-max         2.13  █████████████████
weak            2.26  ██████████████████
pairing         2.31  ██████████████████
interval        2.67  █████████████████████
skew            7.02  ████████████████████████████████████████████████████████
leftist         7.62  █████████████████████████████████████████████████████████████
tournament      9.07  ████████████████████████████████████████████████████████████████+
```

## Scenarios

### fill

```
fill -- ns/op on a log axis, 8 cells to a decade

unsorted       *·······················          2.14  at n = 10000
open-proved    *·······················          2.39  at n = 1000000
block-min      ·*······················          3.06  at n = 100000
open-buffered  ··*·····················          3.60  at n = 1000000
16-ary         ···**···················          6.75  at n = 1000000
8-ary          ···1*4··················          8.23  at n = 1000000
pairing        ····*4··················          8.31  at n = 1000000
binary         ···1·*··················         10.08  at n = 1000000
4-ary          ····12*·················         11.56  at n = 1000000
min-max        ·····1*4················         14.15  at n = 1000000
interval       ·····1·2*···············         18.58  at n = 1000000
weak           ······1·*···············         20.24  at n = 1000000
leftist        ···········1234·········        105.44  at n = 1000000
tournament     ··············*·········        119.89  at n = 1000000
skew           ···········123·4········        150.65  at n = 1000000
beap           ··········1···2···3·····        342.10  at n = 100000
sorted         ···············1·······2       1786.27  at n = 10000
```

### drain

```
drain -- ns/op on a log axis, 8 cells to a decade

sorted         *·····························          2.24  at n = 10000
binary         ········1·23·4················         95.31  at n = 1000000
4-ary          ··········1234················         98.70  at n = 1000000
interval       ··········123·4···············        117.05  at n = 1000000
8-ary          ···········1234···············        121.43  at n = 1000000
open-proved    ············23*···············        131.77  at n = 1000000
open-buffered  ···········1234···············        133.13  at n = 1000000
16-ary         ············1234··············        173.68  at n = 1000000
weak           ············1234··············        174.45  at n = 1000000
min-max        ············1234··············        181.12  at n = 1000000
tournament     ················1*············        316.08  at n = 1000000
pairing        ·············12·3·4···········        427.55  at n = 1000000
skew           ············12··3··4··········        509.50  at n = 1000000
leftist        ·············1·2·3··4·········        697.01  at n = 1000000
beap           ·············1···2···3········       1004.96  at n = 100000
block-min      ···················1·2·3······       1572.50  at n = 100000
unsorted       ·····················1·······2      10655.56  at n = 10000
```

### churn

```
churn -- ns/op on a log axis, 8 cells to a decade

binary         1·*·4···················         52.07  at n = 1000000
4-ary          ··1234··················         60.07  at n = 1000000
interval       ··1234··················         69.37  at n = 1000000
8-ary          ···1*4··················         70.91  at n = 1000000
open-buffered  ···1*4··················         72.52  at n = 1000000
open-proved    ····*·*·················         78.13  at n = 1000000
16-ary         ····12*·················         89.63  at n = 1000000
min-max        ···1234·················         90.41  at n = 1000000
weak           ····1*4·················         91.29  at n = 1000000
tournament     ········*···············        170.21  at n = 1000000
pairing        ····12·3·4··············        224.92  at n = 1000000
skew           ····12·3···4············        330.86  at n = 1000000
leftist        ·····12·3··4············        331.25  at n = 1000000
beap           ······1··2····3·········        948.56  at n = 100000
block-min      ··········21···3········       1142.31  at n = 100000
sorted         ·······1·······2········       1238.18  at n = 10000
unsorted       ···············1·······2      10696.28  at n = 10000
```

### replace-forward

```
replace-forward -- ns/op on a log axis, 8 cells to a decade

sorted         1··2·························          8.04  at n = 10000
binary         ·····1·*·····················         24.15  at n = 1000000
4-ary          ·······1*····················         34.77  at n = 1000000
interval       ········*2···················         35.62  at n = 1000000
open-proved    ·········*21·················         43.44  at n = 1000000
8-ary          ········1*···················         47.42  at n = 1000000
open-buffered  ···1··2·3·4··················         54.72  at n = 1000000
min-max        ·······1234··················         60.39  at n = 1000000
16-ary         ·········1*··················         68.23  at n = 1000000
weak           ·····1··2·34·················         84.14  at n = 1000000
skew           ····1··2·3·4·················         87.80  at n = 1000000
pairing        ····1···2·34·················         89.37  at n = 1000000
leftist        ·····1···2·3·4···············        128.17  at n = 1000000
tournament     ·············*4··············        177.00  at n = 1000000
beap           ··········1····2···3·········        771.92  at n = 100000
block-min      ···············12···3········       1219.88  at n = 100000
unsorted       ····················1·······2      10671.76  at n = 10000
```

### insert-asc

```
insert-asc -- ns/op on a log axis, 8 cells to a decade

binary         *··························          1.95  at n = 1000000
unsorted       *··························          1.96  at n = 10000
open-proved    *··························          2.00  at n = 1000000
block-min      *··························          2.21  at n = 100000
open-buffered  ·*·························          2.54  at n = 1000000
beap           ·*·························          2.66  at n = 100000
weak           ···*·······················          4.99  at n = 1000000
16-ary         ··1*·······················          5.05  at n = 1000000
4-ary          ···*·······················          5.22  at n = 1000000
8-ary          ··1*·······················          5.23  at n = 1000000
pairing        ····*4·····················          7.72  at n = 1000000
min-max        ····1234···················         12.88  at n = 1000000
interval       ········1234···············         48.82  at n = 1000000
tournament     ··············*············        114.61  at n = 1000000
leftist        ·············1234··········        168.75  at n = 1000000
skew           ···········1·2·34··········        170.30  at n = 1000000
sorted         ··················1·······2       3573.09  at n = 10000
```

### insert-desc

```
insert-desc -- ns/op on a log axis, 8 cells to a decade

unsorted       *···················          1.96  at n = 10000
open-proved    *···················          2.07  at n = 1000000
sorted         ·*··················          2.31  at n = 10000
open-buffered  ·3*·················          3.19  at n = 1000000
block-min      1·*·················          3.58  at n = 100000
pairing        ····*4··············          7.31  at n = 1000000
skew           ····*4··············          8.48  at n = 1000000
leftist        ······*·············          9.98  at n = 1000000
binary         ····1*4·············         11.38  at n = 1000000
min-max        ·····1*4············         13.91  at n = 1000000
16-ary         ······12*···········         20.42  at n = 1000000
weak           ·······1*4··········         26.21  at n = 1000000
8-ary          ······1·*4··········         28.29  at n = 1000000
interval       ········12*·········         37.25  at n = 1000000
4-ary          ········1234········         40.39  at n = 1000000
tournament     ··············*·····        113.82  at n = 1000000
beap           ············1···2··3        522.03  at n = 100000
```

### meld-accumulate

```
meld-accumulate -- ns/op on a log axis, 8 cells to a decade

pairing        123·····4·······································         68.13  at n = 1000000
unsorted       ······1·······2·································        447.50  at n = 10000
leftist        ·········1·2·3····4·····························       1378.13  at n = 1000000
skew           ·······1··2·3·····4·····························       1395.63  at n = 1000000
sorted         ················1·······2·······················       8634.50  at n = 10000
block-min      ··········1·······2·······3·····················      14530.19  at n = 100000
open-proved    ·······1······2·······3·······4·················      44952.44  at n = 1000000
open-buffered  ···········1······2·······3········4············     167885.38  at n = 1000000
8-ary          ················1·······2·······3·······4·······     707233.75  at n = 1000000
4-ary          ················1·······2·······3·······4·······     722752.06  at n = 1000000
16-ary         ················1·······2·······3·······4·······     770390.94  at n = 1000000
beap           ····················1·········2··········3······    1039459.50  at n = 100000
binary         ·················1········2·······3·······4·····    1426112.75  at n = 1000000
interval       ····················1·······2·······3·······4···    2201748.06  at n = 1000000
weak           ·····················1········2·······3·······4·    4036216.25  at n = 1000000
tournament     ·············································*·4    5367057.75  at n = 1000000
min-max        ······················1········2·······3·······4    5732590.13  at n = 1000000
```

### meld-into-full

```
meld-into-full -- ns/op on a log axis, 8 cells to a decade

unsorted       *····················································          3.13  at n = 10000
open-proved    ·*4··················································          5.00  at n = 1000000
block-min      ··*··················································          6.25  at n = 100000
pairing        ··1*·················································          6.88  at n = 1000000
open-buffered  ···*4················································         10.00  at n = 1000000
leftist        ···········1*4·······································        125.00  at n = 1000000
skew           ··········12·3·4·····································        209.38  at n = 1000000
beap           ···········*····3····································        343.13  at n = 100000
sorted         ·················1········2··························       4984.44  at n = 10000
4-ary          ····················1·······2·······3·······4········    1115878.63  at n = 1000000
8-ary          ·····················1······2········3·······4·······    1261066.19  at n = 1000000
16-ary         ·····················1·······2·······3·······4·······    1333155.94  at n = 1000000
binary         ····················1········2········3·······4······    1660308.38  at n = 1000000
interval       ························1·······2·······3·······4····    3429110.63  at n = 1000000
weak           ·························1·········2·······3·······4·    7458536.88  at n = 1000000
tournament     ················································*··4·    8011980.44  at n = 1000000
min-max        ···························1········2·······3·······4   10280883.81  at n = 1000000
```

### drain-max

```
drain-max -- ns/op on a log axis, 8 cells to a decade

interval       123·4·        117.22  at n = 1000000
open-buffered  ·1234·        141.20  at n = 1000000
open-proved    ··23*·        142.28  at n = 1000000
min-max        ··1234        196.30  at n = 1000000
```

### drain-both

```
drain-both -- ns/op on a log axis, 8 cells to a decade

interval       123·4··        116.14  at n = 1000000
open-proved    ··23*··        136.47  at n = 1000000
open-buffered  ·1234··        137.82  at n = 1000000
min-max        ···1234        203.44  at n = 1000000
```

### trim

```
trim -- ns/op on a log axis, 8 cells to a decade

interval       1234·         74.31  at n = 1000000
open-buffered  ·1*4·         74.59  at n = 1000000
open-proved    ··2*4         84.59  at n = 1000000
min-max        ·1234         98.63  at n = 1000000
```

## Checksums

Every entry accumulates a checksum over the keys a scenario makes
it see, so entries taking different internal paths over one key
stream owe the same answer.

Groups compared (one per scenario and size): 44.
Disagreements: none.
