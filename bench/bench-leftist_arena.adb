--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Heaps.Leftist_Pool;

package body Bench.Leftist_Arena is

   package Arena renames Heaps.Leftist_Pool;

   --  The accumulator and the operands are not objects here. They are all
   --  trees of the one arena, named by the index of their root, which is what
   --  lets a meld be a splice: the other adapters need one heap object per
   --  operand and a meld has to move keys between two arrays.
   --
   --  Heaps.Leftist_Pool is instantiated with 2 ** 20 nodes, which is
   --  Max_Elements, and both scenarios hold at most that many keys across all
   --  the trees at once -- Max_Elements for the accumulator in `meld-into-full`
   --  plus one key per operand, and Operands * (Max_Elements / Operands) in
   --  `meld-accumulate`.

   Acc : Arena.Tree := 0;
   Ops : array (1 .. Meld_Runner.Operands) of Arena.Tree := [others => 0];

   ----------------
   -- Meld_Reset --
   ----------------

   procedure Meld_Reset is
   begin
      Arena.Clear;

      --  Clear is the one arena operation that invalidates names it was not
      --  given: every tree in the pool ceases to exist, so the roots held here
      --  are stale and have to go back to the empty tree.

      Acc := 0;
      Ops := [others => 0];
   end Meld_Reset;

   -----------------
   -- Meld_Insert --
   -----------------

   procedure Meld_Insert (Which : Natural; K : Key_Type) is
   begin
      if Which = 0 then
         Arena.Insert (Acc, K);
      else
         Arena.Insert (Ops (Which), K);
      end if;
   end Meld_Insert;

   ---------------
   -- Meld_Meld --
   ---------------

   procedure Meld_Meld (Which : Positive) is
   begin
      Arena.Meld (Acc, Ops (Which));
   end Meld_Meld;

   ----------------------
   -- Meld_Extract_Min --
   ----------------------

   procedure Meld_Extract_Min (K : out Key_Type) is
   begin
      Arena.Extract_Min (Acc, K);
   end Meld_Extract_Min;

end Bench.Leftist_Arena;
