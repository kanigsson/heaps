--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Open;

package body Bench.Open_Heap is

   H : Heaps.Open.Heap (Heaps.Extended_Index (Max_Elements));

   procedure Reset is
   begin
      Heaps.Open.Clear (H);
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Heaps.Open.Insert (H, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Heaps.Open.Extract_Min (H, K);
   end Extract_Min;

   procedure Extract_Max (K : out Key_Type) is
   begin
      Heaps.Open.Extract_Max (H, K);
   end Extract_Max;

   function Size return Natural is (Natural (Heaps.Open.Size (H)));

end Bench.Open_Heap;
