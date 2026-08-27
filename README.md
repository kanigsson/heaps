# Heaps in SPARK

Verified priority queues backed by arrays. No access types.

## Implementations

| Heap | Insert | Extract | Notes |
|------|--------|---------|-------|
| Binary heap | O(log n) | O(log n) min | Binary min-heap |
| d-ary heap | O(log\_d n) | O(d log\_d n) min | Configurable arity |
| Min-max heap | O(log n) | O(log n) min or max | Double-ended queue |
| Unsorted array | O(1) | O(n) min | Baseline |
| Sorted array | O(n) | O(1) min | Baseline |

The d-ary heap's arity is a type discriminant, so one proof covers all valid
arities.

## Planned

### Implicit array heaps

- Interval heap
- Beap
- Weak heap

### Array-backed node pools

- Leftist heap
- Skew heap
- Binomial heap
- Skew binomial heap
- Pairing heap
- Rank-pairing heap
- Fibonacci heap

### Integer-key queues

- Bucket queue
- Radix heap
- Bitmapped heap

## Verification

GNATprove proves for every implementation:

- absence of run-time errors (Silver);
- preservation of ordering and correct minimum or maximum results (Gold);
- full functional correctness against a multiset model (Platinum).

### Contracts

The contracts treat a heap as a multiset of keys. `Insert` adds one occurrence.
`Extract_Min` removes one occurrence of a minimum key. The min-max heap provides
the corresponding guarantee for `Extract_Max`. Each operation states the new
size and restores the heap invariant.

The multiset model is ghost code. Contracts and proof assertions are disabled
at run time.

## Build, test, and prove

```sh
gprbuild -P bench.gpr
./heaps_test
./bench_main
gnatprove -P heaps.gpr -j0 --level=2
```

`heaps_test` checks results against a proved linear-scan oracle. It also checks
extraction order and key preservation.

## Benchmarks

The benchmarks cover filling, draining, mixed extraction and insertion, and
ascending or descending input. Double-ended tests also drain from the maximum
end or alternate between both ends.

Each implementation receives the same fixed-seed key sequence. Each scenario
runs five times; the fastest time is reported in nanoseconds per operation. See
[OBSERVATIONS.md](OBSERVATIONS.md) for results.

## Layout

```text
src/            verified library
bench/          tests and benchmarks
heaps.gpr       proof project
bench.gpr       benchmark project
sparklib.gpr    local SPARKlib project file
```

## License

Apache License 2.0 with the LLVM exception. See [LICENSE](LICENSE).
