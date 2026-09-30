--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

package body Heaps.Words with SPARK_Mode is

   use Interfaces;

   Magic : constant := 16#03F7_9D71_B4CB_0A89#;
   --  A De Bruijn sequence: the top six bits of Magic * 2 ** B are distinct
   --  for every B in Bit

   type Position_Table is array (Word range 0 .. 63) of Bit
     with Component_Size => 8;

   Position : constant Position_Table :=
     [ 0,  1, 48,  2, 57, 49, 28,  3, 61, 58, 50, 42, 38, 29, 17,  4,
      62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12,  5,
      63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11,
      46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19,  9, 13,  8,  7,  6];
   --  Position (Shift_Right (Magic * 2 ** B, 58)) = B

   function Is_Power (X : Word) return Boolean is
     (X /= 0 and then (X and (X - 1)) = 0)
     with Ghost;

   function Log2 (X : Word) return Bit
     with Ghost,
          Pre  => Is_Power (X),
          Post => X = Shift_Left (1, Log2'Result);
   --  The witness that a power of two is a shift of one. The provers find
   --  the fact for a given position, but not the position.

   ----------
   -- Log2 --
   ----------

   function Log2 (X : Word) return Bit is
      R : Bit := 0;
   begin
      while X /= Shift_Left (1, R) loop
         pragma Loop_Invariant ((X and (Shift_Left (1, R) - 1)) = 0);
         pragma Loop_Variant (Increases => R);
         pragma Assert (R < Bit'Last);
         R := R + 1;
      end loop;
      return R;
   end Log2;

   ----------------
   -- Lemma_Zero --
   ----------------

   procedure Lemma_Zero (W : Word) is
   begin
      if (for all B in Bit => not Is_Set (W, B)) then
         for B in Bit loop
            pragma Loop_Invariant ((W and (Shift_Left (1, B) - 1)) = 0);
            pragma Assert (not Is_Set (W, B));
            if B = Bit'Last then
               pragma Assert (W = 0);
            end if;
         end loop;
      end if;
   end Lemma_Zero;

   ------------
   -- Lowest --
   ------------

   function Lowest (W : Word) return Bit is
      X : constant Word := W and (not W + 1);
      R : Bit;
   begin
      pragma Assert (Is_Power (X));
      pragma Assert ((W and X) /= 0 and (W and (X - 1)) = 0);
      pragma Assert
        (for all B in Bit =>
           Position (Shift_Right (Shift_Left (1, B) * Magic, 58)) = B);
      pragma Assert (X = Shift_Left (1, Log2 (X)));
      R := Position (Shift_Right (X * Magic, 58));
      pragma Assert (X = Shift_Left (1, R));
      return R;
   end Lowest;

end Heaps.Words;
