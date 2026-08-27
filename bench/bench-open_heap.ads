--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for the unrestricted Heaps.Open priority queue. The
--  implementation adapts to operation history and uses extra storage, but
--  does not inspect scenario names, generator state or future operations.

with Bench.Driver;
with Bench.Deque_Driver;

package Bench.Open_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);
   procedure Extract_Max (K : out Key_Type);

   function Size return Natural;

   package Runner is new Bench.Driver
     (Heap_Name   => "open-adaptive",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   package Deque_Runner is new Bench.Deque_Driver
     (Heap_Name   => "open-adaptive",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min,
      Extract_Max => Extract_Max);

end Bench.Open_Heap;
