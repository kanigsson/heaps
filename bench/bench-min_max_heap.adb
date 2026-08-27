--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Min_Max;

package body Bench.Min_Max_Heap is

   H : Heaps.Min_Max.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Min_Max.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Min_Max.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Min_Max.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Min_Max.Extract_Max (H, K);
   end Extract_Max;

end Bench.Min_Max_Heap;
