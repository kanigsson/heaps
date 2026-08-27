--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Leftist;

package body Bench.Leftist_Heap is

   H : Heaps.Leftist.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Leftist.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Leftist.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Leftist.Extract_Min (H, K);
   end Extract_Min;

end Bench.Leftist_Heap;
