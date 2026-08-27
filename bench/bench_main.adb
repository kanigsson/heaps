--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Entry point of the benchmark suite. Add a line per heap kind as they are
--  implemented; every one of them is measured on the same scenarios and the
--  same key sequence.

with Bench;
with Bench.Binary_Heap;
with Bench.Sorted_Heap;
with Bench.Unsorted_Heap;

procedure Bench_Main is

   Sizes : constant Bench.Size_Array :=
     [1_000, 10_000, 100_000, 1_000_000];

   Baseline_Sizes : constant Bench.Size_Array := [1_000, 10_000];
   --  The two array baselines have a linear operation each, so their
   --  scenarios are quadratic; running them at the sizes above would take
   --  hours and say nothing that the small sizes do not already say.

begin
   Bench.Print_Header;
   Bench.Binary_Heap.Runner.Run (Sizes);
   Bench.Sorted_Heap.Runner.Run (Baseline_Sizes);
   Bench.Unsorted_Heap.Runner.Run (Baseline_Sizes);
end Bench_Main;
