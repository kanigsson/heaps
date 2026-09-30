--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Bench.Bitmap_Queue;

package body Bench.Bitmap_Heap is

   package Q renames Bench.Bitmap_Queue;

   H : Q.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Q.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Q.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Q.Extract_Min (H, K);
   end Extract_Min;

   Acc : Q.Heap (Heaps.Extended_Index (Max_Elements));
   Ops : array (1 .. Bounded_Meld_Runner.Operands) of
           Q.Heap
             (Heaps.Extended_Index
                (Max_Elements / Bounded_Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Q.Clear (Acc);
      for W in Ops'Range loop
         Q.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Q.Insert (Acc, K);
      else
         Q.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Q.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Q.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Bitmap_Heap;
