--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Interval.
--
--  Like the min-max heap, the interval heap is measured twice: through the
--  common driver, which only uses the min end, and through the double-ended
--  driver, which is the workload it exists for.

with Bench.Driver;
with Bench.Meld_Driver;
with Bench.Deque_Driver;

package Bench.Interval_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);
   procedure Extract_Max (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "interval",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   package Deque_Runner is new Bench.Deque_Driver
     (Heap_Name   => "interval",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min,
      Extract_Max => Extract_Max);

   ----------
   -- Meld --
   ----------

   --  A second set of heaps, kept apart from the one the single-heap
   --  scenarios use: the meld workload needs an accumulator and several
   --  operands live at once.

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "interval",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Interval_Heap;
