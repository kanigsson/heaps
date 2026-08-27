--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Beap;

package body Bench.Beap_Heap is

   H : Heaps.Beap.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Beap.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Beap.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Beap.Extract_Min (H, K);
   end Extract_Min;

end Bench.Beap_Heap;
