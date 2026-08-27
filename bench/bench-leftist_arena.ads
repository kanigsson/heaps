--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Leftist_Pool, the shared-pool leftist heap.
--
--  Only the meld workload. The single-heap scenarios are covered by
--  Bench.Leftist_Heap, which measures Heaps.Leftist; the two units hold the
--  same tree and differ in who owns the pool, and it is the meld where that
--  difference is the whole point.

with Bench.Meld_Driver;

package Bench.Leftist_Arena is

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "leftist-arena",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Leftist_Arena;
