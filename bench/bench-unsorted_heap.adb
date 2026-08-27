--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Unsorted;

package body Bench.Unsorted_Heap is

   H : Heaps.Unsorted.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Unsorted.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Unsorted.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Unsorted.Extract_Min (H, K);
   end Extract_Min;

end Bench.Unsorted_Heap;
