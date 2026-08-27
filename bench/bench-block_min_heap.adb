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

end Bench.Block_Min_Heap;
