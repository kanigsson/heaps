--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Min_Max.
--
--  The min-max heap is measured twice: through the common driver, which only
--  uses the min end and therefore places it next to the single-ended heaps,
--  and through the double-ended driver, which is the workload it exists for.

with Bench.Driver;
with Bench.Deque_Driver;

package Bench.Min_Max_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);
   procedure Extract_Max (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "min-max",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   package Deque_Runner is new Bench.Deque_Driver
     (Heap_Name   => "min-max",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min,
      Extract_Max => Extract_Max);

end Bench.Min_Max_Heap;
