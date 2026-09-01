--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Sorted_Linked;

package body Bench.Sorted_Linked_Heap is

   H : Heaps.Sorted_Linked.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Sorted_Linked.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Sorted_Linked.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Sorted_Linked.Extract_Min (H, K);
   end Extract_Min;

   Acc : Heaps.Sorted_Linked.Heap
     (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Sorted_Linked.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Sorted_Linked.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Sorted_Linked.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Sorted_Linked.Insert (Acc, K);
      else
         Heaps.Sorted_Linked.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Sorted_Linked.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Sorted_Linked.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Sorted_Linked_Heap;
