--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for the hierarchical bitmap queue. It keeps a count for
--  every possible key, so it runs the bounded-key scenarios only.

with Bench.Driver;
with Bench.Meld_Driver;

package Bench.Bitmap_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Bounded_Runner is new Bench.Driver
     (Heap_Name     => "bitmap",
      Universe_Bits => Bounded_Bits,
      Reset         => Reset,
      Insert        => Insert,
      Extract_Min   => Extract_Min);

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Bounded_Meld_Runner is new Bench.Meld_Driver
     (Heap_Name     => "bitmap",
      Universe_Bits => Bounded_Bits,
      Reset         => Meld_Reset,
      Insert        => Meld_Insert,
      Meld          => Meld_Meld,
      Extract_Min   => Meld_Extract_Min);

end Bench.Bitmap_Heap;
