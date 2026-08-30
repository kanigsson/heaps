--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for the platinum-proved open entry.

with Bench.Deque_Driver;
with Bench.Driver;
with Bench.Meld_Driver;

package Bench.Open_Proved_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);
   procedure Extract_Max (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "open-proved",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   package Deque_Runner is new Bench.Deque_Driver
     (Heap_Name   => "open-proved",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min,
      Extract_Max => Extract_Max);

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "open-proved",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Open_Proved_Heap;
