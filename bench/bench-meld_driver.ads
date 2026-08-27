--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Generic benchmark driver for the meld operation.
--
--  A single meld is far too fast to time: building its two operands costs
--  orders of magnitude more than the operation itself, and the clock's
--  resolution swamps the result. The workload here is therefore k-way
--  accumulation -- build Operands heaps and meld them one after another into
--  a single accumulator -- which makes the timed phase long enough to measure,
--  and sweeps the ratio between the two operand sizes for free as the
--  accumulator grows from N / Operands to N.
--
--  It is also a real workload rather than a microbenchmark: it is the merge
--  phase of an external sort, and the shape of a k-way join over sorted
--  streams.
--
--  For a mergeable heap the k melds cost O(k log n) altogether. For an
--  implicit heap that has to rebuild, they cost O(k * n / Operands * k), which
--  is the gap the column exists to show.

generic
   Heap_Name : String;

   with procedure Reset;
   --  Empty the accumulator and every operand

   with procedure Insert (Which : Natural; K : Key_Type);
   --  Which = 0 is the accumulator; 1 .. Operands are the operand heaps

   with procedure Meld (Which : Positive);
   --  Meld operand Which into the accumulator, leaving the operand empty

   with procedure Extract_Min (K : out Key_Type);
   --  From the accumulator

package Bench.Meld_Driver is

   Operands : constant := 16;
   --  Number of heaps melded into the accumulator per measurement. Adapters
   --  size their operand heaps at Max_Elements / Operands and their
   --  accumulator at Max_Elements.

   procedure Run (Sizes : Size_Array; Reps : Positive := 5);
   --  Run every scenario for every size, keeping the best of Reps runs. Only
   --  the melds are timed; filling the operands is not.

end Bench.Meld_Driver;
