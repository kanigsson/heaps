--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Entry point of the benchmark suite. Add a line per heap kind as they are
--  implemented; every one of them is measured on the same scenarios and the
--  same key sequence.

with Bench;
with Bench.Beap_Heap;
with Bench.Binary_Heap;
with Bench.Block_Min_Heap;
with Bench.Dary_4;
with Bench.Dary_8;
with Bench.Dary_16;
with Bench.Interval_Heap;
with Bench.Leftist_Heap;
with Bench.Min_Max_Heap;
with Bench.Open_Heap;
with Bench.Sorted_Heap;
with Bench.Unsorted_Heap;
with Bench.Weak_Heap;

procedure Bench_Main is

   Sizes : constant Bench.Size_Array :=
     [1_000, 10_000, 100_000, 1_000_000];

   Beap_Sizes : constant Bench.Size_Array := [1_000, 10_000, 100_000];
   --  The beap spends O(sqrt n) on an operation, so a decade of size costs it
   --  a factor of about thirty. Three decades are enough to show that growth
   --  without holding the rest of the suite back.

   Baseline_Sizes : constant Bench.Size_Array := [1_000, 10_000];
   --  The two array baselines have a linear operation each, so their
   --  scenarios are quadratic: each extra decade costs a hundred times the
   --  wall clock. Two decades already show the growth, and are the difference
   --  between a suite that runs in seconds and one that does not.

begin
   Bench.Print_Header;
   Bench.Binary_Heap.Runner.Run (Sizes);
   Bench.Block_Min_Heap.Runner.Run (Beap_Sizes);
   Bench.Dary_4.Runner.Run (Sizes);
   Bench.Dary_8.Runner.Run (Sizes);
   Bench.Dary_16.Runner.Run (Sizes);
   Bench.Weak_Heap.Runner.Run (Sizes);
   Bench.Leftist_Heap.Runner.Run (Sizes);
   Bench.Min_Max_Heap.Runner.Run (Sizes);
   Bench.Interval_Heap.Runner.Run (Sizes);
   Bench.Open_Heap.Runner.Run (Sizes);
   Bench.Beap_Heap.Runner.Run (Beap_Sizes);
   Bench.Sorted_Heap.Runner.Run (Baseline_Sizes);
   Bench.Unsorted_Heap.Runner.Run (Baseline_Sizes);

   --  Meld. Only the entries that have the operation so far; see the Planned
   --  operations section of README.md for the rest, and for why the leftist
   --  heap -- the one the column exists for -- is not here yet.
   Bench.Binary_Heap.Meld_Runner.Run (Sizes);
   Bench.Unsorted_Heap.Meld_Runner.Run (Baseline_Sizes);

   Bench.Min_Max_Heap.Deque_Runner.Run (Sizes);
   Bench.Interval_Heap.Deque_Runner.Run (Sizes);
   Bench.Open_Heap.Deque_Runner.Run (Sizes);
end Bench_Main;
