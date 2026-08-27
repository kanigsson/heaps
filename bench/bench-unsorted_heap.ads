--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Unsorted.

with Bench.Driver;

package Bench.Unsorted_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "unsorted",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

end Bench.Unsorted_Heap;
