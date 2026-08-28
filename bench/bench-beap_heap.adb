--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Beap;

package body Bench.Beap_Heap is

   H : Heaps.Beap.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Beap.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Beap.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Beap.Extract_Min (H, K);
   end Extract_Min;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Beap.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Beap.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Beap.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Beap.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Beap.Insert (Acc, K);
      else
         Heaps.Beap.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Beap.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Beap.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Beap_Heap;
