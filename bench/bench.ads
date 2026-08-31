--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Micro-benchmark framework for the heaps.
--
--  This root package holds what does not depend on a particular heap: the
--  deterministic key generator, so that every heap kind sees the same input
--  sequence, the timing helper and the report formatting. Bench.Driver turns
--  a set of heap operations into a set of measurements.
--
--  This code is outside the SPARK subset perimeter: it exercises the verified
--  library, it is not part of it.

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

   procedure Write_Markdown (Path : String; Machine : String);
   --  Write the results document at Path: the overall charts, then one chart
   --  per scenario. Machine names the hardware and switches, which the
   --  program cannot find out for itself.

   procedure Write_Json (Path : String; Machine : String);
   --  Write every measurement at Path as a script defining RESULTS. A script
   --  rather than bare JSON so that the page loading it works from disk,
   --  where fetch does not.

   procedure Print_Summary;
   --  One bar chart per size measured: each heap's cost relative to the
   --  binary heap, as the geometric mean of its ratio on each single-heap
   --  scenario. Ratios are taken scenario by scenario before being averaged,
   --  so the figure does not depend on which scenario is slowest in absolute
   --  terms. A heap missing a scenario at a size is left out of that chart.

private

   type Generator is record
      State : Interfaces.Unsigned_64;
   end record;

end Bench;
