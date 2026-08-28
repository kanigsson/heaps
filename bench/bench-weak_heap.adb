--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Weak;

package body Bench.Weak_Heap is

   H : Heaps.Weak.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Weak.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Weak.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Weak.Extract_Min (H, K);
   end Extract_Min;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Weak.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Weak.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Weak.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Weak.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Weak.Insert (Acc, K);
      else
         Heaps.Weak.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Weak.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Weak.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Weak_Heap;
