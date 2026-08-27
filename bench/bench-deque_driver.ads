--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark driver for double-ended priority queues.
--
--  Same shape as Bench.Driver, and fed by the same key generator, but the
--  scenarios use both ends of the queue. Only heap kinds that can extract a
--  maximum are instantiated with it, so its rows are not comparable with the
--  single-ended table row for row; what they are for is measuring what the
--  second end costs relative to the first.

generic
   Heap_Name : String;

   with procedure Reset;
   with procedure Insert (K : Key_Type);
   with procedure Extract_Min (K : out Key_Type);
   with procedure Extract_Max (K : out Key_Type);

package Bench.Deque_Driver is

   procedure Run (Sizes : Size_Array; Reps : Positive := 5);

end Bench.Deque_Driver;
