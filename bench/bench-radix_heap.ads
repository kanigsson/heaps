--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Benchmark adapter for the monotone radix heap. The general churn scenario
--  is excluded because it inserts arbitrary keys below the last extracted
--  key; replace-forward is the matching monotone workload.

with Bench.Driver;
with Bench.Meld_Driver;

package Bench.Radix_Heap is

   procedure Reset;
   procedure Insert (K : Key_Type);
   procedure Extract_Min (K : out Key_Type);

   package Runner is new Bench.Driver
     (Heap_Name     => "radix",
      Include_Churn => False,
      Reset         => Reset,
      Insert        => Insert,
      Extract_Min   => Extract_Min);

   procedure Meld_Reset;
   procedure Meld_Insert (Which : Natural; K : Key_Type);
   procedure Meld_Meld (Which : Positive);
   procedure Meld_Extract_Min (K : out Key_Type);

   package Meld_Runner is new Bench.Meld_Driver
     (Heap_Name   => "radix",
      Reset       => Meld_Reset,
      Insert      => Meld_Insert,
      Meld        => Meld_Meld,
      Extract_Min => Meld_Extract_Min);

end Bench.Radix_Heap;
