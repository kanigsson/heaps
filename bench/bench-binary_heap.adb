--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Binary;

package body Bench.Binary_Heap is

   H : Heaps.Binary.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Binary.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Binary.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Binary.Extract_Min (H, K);
   end Extract_Min;

end Bench.Binary_Heap;
