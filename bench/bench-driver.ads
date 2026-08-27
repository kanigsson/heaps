--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Generic benchmark driver.
--
--  Instantiate it once per heap implementation with a thin adapter that hides
--  the heap object itself. Every heap kind is then measured on the same
--  scenarios and the same key sequence, which makes the numbers comparable and
--  the checksums cross-checkable.

generic
   Heap_Name : String;

   with procedure Reset;
   --  Empty the heap under test

   with procedure Insert (K : Key_Type);
   with procedure Extract_Min (K : out Key_Type);

package Bench.Driver is

   procedure Run (Sizes : Size_Array; Reps : Positive := 5);
   --  Run every scenario for every size, keeping the best of Reps runs. Only
   --  the measured phase of a scenario is timed; filling a heap before a
   --  drain, for instance, is not.

end Bench.Driver;
