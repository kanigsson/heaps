--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Dary.
--
--  The adapter owns the heap object and exposes the operations as
--  parameterless procedures, which is all Bench.Driver asks for. It is
--  generic over the arity because the arity is the whole point of this heap
--  kind: the interesting measurement is one curve per arity on the same key
--  sequence.

with Bench.Driver;
with Heaps.Dary;

generic
   Arity      : Heaps.Dary.Arity_Type;
   Heap_Label : String;
package Bench.Dary_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => Heap_Label,
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

end Bench.Dary_Heap;
