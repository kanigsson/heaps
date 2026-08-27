--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Interval;

package body Bench.Interval_Heap is

   H : Heaps.Interval.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Interval.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Interval.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Interval.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Interval.Extract_Max (H, K);
   end Extract_Max;

end Bench.Interval_Heap;
