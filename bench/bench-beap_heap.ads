--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Beap.
--
--  The adapter owns the heap object and exposes the operations as parameterless
--  procedures, which is all Bench.Driver asks for.

with Bench.Driver;

package Bench.Beap_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "beap",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

end Bench.Beap_Heap;
