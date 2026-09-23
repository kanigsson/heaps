--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Bench.Skew_Binomial_Arena;

package body Bench.Skew_Binomial_Heap is

   package Arena renames Bench.Skew_Binomial_Arena;

   T : Arena.Tree := 0;

   Acc : Arena.Tree := 0;
   Ops : array (1 .. Meld_Runner.Operands) of Arena.Tree := [others => 0];

   procedure Reset is
   begin
      Arena.Clear;
      T := 0;
   end Reset;

   procedure Insert (K : Key_Type) is
   begin
      Arena.Insert (T, K);
   end Insert;

   procedure Extract_Min (K : out Key_Type) is
   begin
      Arena.Extract_Min (T, K);
   end Extract_Min;

   procedure Meld_Reset is
   begin
      Arena.Clear;
      T := 0;
      Acc := 0;
      Ops := [others => 0];
   end Meld_Reset;

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Arena.Insert (Acc, K);
      else
         Arena.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   procedure Meld_Meld (Which : Positive) is
   begin
      Arena.Meld (Acc, Ops (Which));
   end Meld_Meld;

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Arena.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Skew_Binomial_Heap;
