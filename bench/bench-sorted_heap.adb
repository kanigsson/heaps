--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Sorted;

package body Bench.Sorted_Heap is

   H : Heaps.Sorted.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Sorted.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Sorted.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Sorted.Extract_Min (H, K);
   end Extract_Min;

end Bench.Sorted_Heap;
