--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

package body Bench.Dary_Heap is

   H : Heaps.Dary.Heap (Heaps.Extended_Index (Max_Elements), Arity);

   procedure Reset is
   begin
      Heaps.Dary.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Dary.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Dary.Extract_Min (H, K);
   end Extract_Min;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Dary.Heap (Heaps.Extended_Index (Max_Elements), Arity);

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Dary.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands),
              Arity);

   procedure Meld_Reset is
   begin
      Heaps.Dary.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Dary.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Dary.Insert (Acc, K);
      else
         Heaps.Dary.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Dary.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Dary.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Dary_Heap;
