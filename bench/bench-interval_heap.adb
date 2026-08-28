--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Interval;

package body Bench.Interval_Heap is

   H : Heaps.Interval.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Interval.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Interval.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Interval.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Interval.Extract_Max (H, K);
   end Extract_Max;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Interval.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Interval.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Interval.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Interval.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Interval.Insert (Acc, K);
      else
         Heaps.Interval.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Interval.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Interval.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Interval_Heap;
