--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for the unrestricted Heaps.Open priority queue. The
--  implementation may use facilities outside SPARK and adapt to current size
--  and representation, but is independent of benchmark scenarios, generator
--  state and key patterns.

with Bench.Driver;
with Bench.Deque_Driver;
with Bench.Meld_Driver;

package Bench.Open_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);
   procedure Extract_Max (K : out Key_Type);

   function Size return Natural;

   package Runner is new Bench.Driver
     (Heap_Name   => "open-buffered",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   package Deque_Runner is new Bench.Deque_Driver
     (Heap_Name   => "open-buffered",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min,
      Extract_Max => Extract_Max);

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "open-buffered",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Open_Heap;
