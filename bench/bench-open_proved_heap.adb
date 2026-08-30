--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Open_Proved;

package body Bench.Open_Proved_Heap is

   H : Heaps.Open_Proved.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Open_Proved.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Open_Proved.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Open_Proved.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Open_Proved.Extract_Max (H, K);
   end Extract_Max;

   Acc : Heaps.Open_Proved.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Open_Proved.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Open_Proved.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Open_Proved.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Open_Proved.Insert (Acc, K);
      else
         Heaps.Open_Proved.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Open_Proved.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Open_Proved.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Open_Proved_Heap;
