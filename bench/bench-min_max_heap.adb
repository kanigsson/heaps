--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Min_Max;

package body Bench.Min_Max_Heap is

   H : Heaps.Min_Max.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Min_Max.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Min_Max.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Min_Max.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Min_Max.Extract_Max (H, K);
   end Extract_Max;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Min_Max.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Min_Max.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Min_Max.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Min_Max.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Min_Max.Insert (Acc, K);
      else
         Heaps.Min_Max.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Min_Max.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Min_Max.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Min_Max_Heap;
