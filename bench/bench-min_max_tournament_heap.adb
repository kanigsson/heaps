--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Min_Max_Tournament;

package body Bench.Min_Max_Tournament_Heap is

   H : Heaps.Min_Max_Tournament.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Min_Max_Tournament.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Min_Max_Tournament.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Min_Max_Tournament.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Min_Max_Tournament.Extract_Max (H, K);
   end Extract_Max;

   ----------------
   -- Meld_Reset --
   ----------------

   Acc : Heaps.Min_Max_Tournament.Heap (Heaps.Extended_Index (Max_Elements));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Min_Max_Tournament.Heap
             (Heaps.Extended_Index (Max_Elements / Meld_Runner.Operands));

   procedure Meld_Reset is
   begin
      Heaps.Min_Max_Tournament.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Min_Max_Tournament.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Min_Max_Tournament.Insert (Acc, K);
      else
         Heaps.Min_Max_Tournament.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Min_Max_Tournament.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Min_Max_Tournament.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Min_Max_Tournament_Heap;
