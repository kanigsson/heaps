--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Block_Min;

package body Bench.Block_Min_Heap is

   Capacity : constant Heaps.Extended_Index :=
     Heaps.Extended_Index (Max_Elements);

   H : Heaps.Block_Min.Heap
     (Capacity            => Capacity,
      Directory_Capacity => Heaps.Block_Min.Blocks_For (Capacity));

   procedure Reset is
   begin
      Heaps.Block_Min.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Block_Min.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Block_Min.Extract_Min (H, K);
   end Extract_Min;

   ----------------
   -- Meld_Reset --
   ----------------

   Op_Capacity : constant Heaps.Extended_Index :=
     Capacity / Meld_Runner.Operands;

   Acc : Heaps.Block_Min.Heap
     (Capacity           => Capacity,
      Directory_Capacity => Heaps.Block_Min.Blocks_For (Capacity));

   Ops : array (1 .. Meld_Runner.Operands) of
           Heaps.Block_Min.Heap
             (Capacity           => Op_Capacity,
              Directory_Capacity => Heaps.Block_Min.Blocks_For (Op_Capacity));

   procedure Meld_Reset is
   begin
      Heaps.Block_Min.Clear (Acc);
      for W in Ops'Range loop
         Heaps.Block_Min.Clear (Ops (W));
      end loop;
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Heaps.Block_Min.Insert (Acc, K);
      else
         Heaps.Block_Min.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Heaps.Block_Min.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Heaps.Block_Min.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Block_Min_Heap;
