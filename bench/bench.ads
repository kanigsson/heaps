--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Reusable micro-benchmark framework for the heaps in this collection.
--
--  This root package holds everything that is independent from a particular
--  heap implementation: the deterministic key generator (so that every heap
--  kind is measured on exactly the same input sequence), the timing helper
--  and the report formatting. Bench.Driver is the generic that turns a set of
--  heap operations into a set of measurements.
--
--  This code is deliberately outside the SPARK subset perimeter: it is not
--  part of the verified library, it only exercises it.

with Heaps;
with Interfaces;

package Bench is

   subtype Key_Type is Heaps.Key_Type;

   type Size_Array is array (Positive range <>) of Positive;

   subtype Checksum_Type is Interfaces.Unsigned_64;
   --  Checksums are accumulated in modular arithmetic so that they never
   --  overflow, whatever the number of operations.

   Max_Elements : constant := 2 ** 20;
   --  Upper bound on the number of elements any benchmark scenario puts in a
   --  heap at once. Adapters size their heap with this.

   ---------------------------
   -- Deterministic key stream
   ---------------------------

   type Generator is private;

   function Seeded (Seed : Long_Long_Integer := 88_172_645_463_325_252)
                    return Generator;
   --  A generator is always created from a fixed seed, so that two runs, and
   --  two different heap kinds, see the very same keys.

   procedure Next (G : in out Generator; K : out Key_Type);

   ------------
   -- Report --
   ------------

   procedure Print_Header;

   procedure Print_Row
     (Heap_Name : String;
      Scenario  : String;
      N         : Positive;
      Seconds   : Duration;
      Ops       : Long_Long_Integer;
      Checksum  : Checksum_Type);
   --  One measurement line: wall time is turned into nanoseconds per
   --  operation. The checksum is printed as well: it only depends on the key
   --  sequence and on the correctness of the heap, so two implementations
   --  disagreeing on it signals a bug rather than a performance difference.

private

   type Generator is record
      State : Interfaces.Unsigned_64;
   end record;

end Bench;
