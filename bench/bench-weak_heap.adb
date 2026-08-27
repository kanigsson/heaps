--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Weak;

package body Bench.Weak_Heap is

   H : Heaps.Weak.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Weak.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Weak.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Weak.Extract_Min (H, K);
   end Extract_Min;

end Bench.Weak_Heap;
