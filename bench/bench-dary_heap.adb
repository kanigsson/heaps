--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

package body Bench.Dary_Heap is

   H : Heaps.Dary.Heap (Heaps.Extended_Index (Max_Elements), Arity);

   procedure Reset is
   begin
      Heaps.Dary.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Dary.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Dary.Extract_Min (H, K);
   end Extract_Min;

end Bench.Dary_Heap;
