--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Tournament;

package body Bench.Tournament_Heap is

   Capacity : constant Heaps.Extended_Index :=
     Heaps.Extended_Index (Max_Elements);

   H : Heaps.Tournament.Heap (Capacity);

   procedure Reset is
   begin
      Heaps.Tournament.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Tournament.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Tournament.Extract_Min (H, K);
   end Extract_Min;

   Op_Capacity : constant Heaps.Extended_Index :=
     Capacity / Meld_Runner.Operands;

   Acc : Heaps.Tournament.Heap (Capacity);
   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Tournament.Heap (Op_Capacity);

   procedure Meld_Reset is
   begin
      Heaps.Tournament.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Tournament.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Tournament.Insert (Acc, K);
      else
         Heaps.Tournament.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Tournament.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Tournament.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Tournament_Heap;
