--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Run-time sanity check of the heap implementations.
--
--  The proofs cover the algorithms; this program covers the wiring, and gives
--  a quick way to check a new heap kind before pointing gnatprove at it. It is
--  deliberately built with assertions enabled.

with Ada.Text_IO; use Ada.Text_IO;
with Heaps;       use Heaps;
with Heaps.Binary;

procedure Heaps_Test is

   Failures : Natural := 0;

   Sizes : constant array (1 .. 7) of Positive :=
     [1, 2, 3, 7, 64, 1_000, 10_000];

   procedure Check (Condition : Boolean; Message : String);
   procedure Check (Condition : Boolean; Message : String) is
   begin
      if not Condition then
         Put_Line ("FAIL: " & Message);
         Failures := Failures + 1;
      end if;
   end Check;

   procedure Test_Binary (N : Positive);
   procedure Test_Binary (N : Positive) is
      H     : Heaps.Binary.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         --  A simple multiplicative generator; the point is only to obtain a
         --  reproducible, unsorted sequence.
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Binary.Insert (H, K);
         Check (Heaps.Binary.Size (H) = I, "size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Binary.Peek_Min (H) = Heaps.Binary.Min_Of (H),
                "peek agrees with the array minimum");
         Heaps.Binary.Extract_Min (H, K);
         Check (K >= Prev, "keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Binary.Is_Empty (H), "heap empty after draining");
      Check (Sum = Back, "the keys that came out are the keys that went in");
   end Test_Binary;

begin
   for N of Sizes loop
      Test_Binary (N);
   end loop;

   if Failures = 0 then
      Put_Line ("all heap tests passed");
   else
      Put_Line (Natural'Image (Failures) & " failure(s)");
   end if;
end Heaps_Test;
