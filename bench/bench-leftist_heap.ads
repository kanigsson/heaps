--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for Heaps.Leftist_Pool, an instance of the leftist arena.
--
--  A heap here is a tree of the shared pool, named by the index of its root,
--  so the adapter holds root indices rather than heap objects. The meld
--  scenarios use an accumulator and several operands, all trees of the same
--  pool.

with Bench.Driver;
with Bench.Meld_Driver;

package Bench.Leftist_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name   => "leftist",
      Reset       => Reset,
      Insert      => Insert,
      Extract_Min => Extract_Min);

   ----------
   -- Meld --
   ----------

   --  A second set of trees, kept apart from the one the single-heap
   --  scenarios use: the meld workload needs an accumulator and several
   --  operands live at once. The two sets never overlap in time, because
   --  either Reset clears the arena or Meld_Reset does, and each invalidates
   --  the other's names.

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "leftist",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Leftist_Heap;
