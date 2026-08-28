--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Open;

package body Bench.Open_Heap is

   H : Heaps.Open.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Open.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Open.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Open.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Open.Extract_Max (H, K);
   end Extract_Max;

   function Size return Natural is (Natural (Heaps.Open.Size (H)));

   Acc : Heaps.Open.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Open.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Open.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Open.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Open.Insert (Acc, K);
      else
         Heaps.Open.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Open.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Open.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Open_Heap;
