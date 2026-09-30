--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Sixty-four bit words read as sets of bit positions, for the summary levels
--  of the bitmap queue.
--
--  Every property is stated through Is_Set, one bit at a time, so that the
--  proofs above this unit never reason about masks or shifts. Only the bodies
--  here do.

with Interfaces;

package Heaps.Words with SPARK_Mode, Always_Terminates is

   subtype Word is Interfaces.Unsigned_64;

   subtype Bit is Natural range 0 .. 63;

   Bits_Per_Word : constant := 64;

   use type Word;

   function Is_Set (W : Word; B : Bit) return Boolean is
     ((W and Interfaces.Shift_Left (1, B)) /= 0);

   function With_Bit (W : Word; B : Bit) return Word is
     (W or Interfaces.Shift_Left (1, B))
     with Post => Is_Set (With_Bit'Result, B)
                  and then (for all C in Bit =>
                              (if C /= B
                               then Is_Set (With_Bit'Result, C)
                                    = Is_Set (W, C)));

   function Without_Bit (W : Word; B : Bit) return Word is
     (W and not Interfaces.Shift_Left (1, B))
     with Post => not Is_Set (Without_Bit'Result, B)
                  and then (for all C in Bit =>
                              (if C /= B
                               then Is_Set (Without_Bit'Result, C)
                                    = Is_Set (W, C)));

   procedure Lemma_Zero (W : Word)
     with Ghost,
          Post => (W = 0) = (for all B in Bit => not Is_Set (W, B));
   --  A word is zero exactly when it has no bit set

   function Lowest (W : Word) return Bit
     with Pre  => W /= 0,
          Post => Is_Set (W, Lowest'Result)
                  and then (for all C in 0 .. Lowest'Result - 1 =>
                              not Is_Set (W, C));
   --  The position of the lowest set bit. The body is a multiplication by a
   --  De Bruijn constant and a table lookup, which GCC turns into a single
   --  trailing-zero count on a target that has one.

end Heaps.Words;
