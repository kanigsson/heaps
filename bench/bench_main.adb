--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Entry point of the benchmark suite. Add a line per heap kind as they are
--  implemented; every one of them is measured on the same scenarios, sizes and
--  key sequence.

with Bench;
with Bench.Binary_Heap;

procedure Bench_Main is
   Sizes : constant Bench.Size_Array :=
     [1_000, 10_000, 100_000, 1_000_000];
begin
   Bench.Print_Header;
   Bench.Binary_Heap.Runner.Run (Sizes);
end Bench_Main;
