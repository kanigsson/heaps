--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Focused run-time checks for the adaptive benchmark entry.  These exercise
--  transitions between buffering, one-sided heaps and sorted double-ended
--  draining, including arbitrary negative Key_Type values that the benchmark
--  generator itself does not produce.

with Ada.Command_Line;
with Ada.Text_IO;       use Ada.Text_IO;
with Bench.Open_Heap;
with Heaps;             use Heaps;
with Interfaces;        use Interfaces;

procedure Open_Heap_Test is

   Max_Reference : constant := 2_048;
   type Reference_Array is array (Positive range 1 .. Max_Reference) of Key_Type;

   Reference : Reference_Array;
   Ref_Count : Natural range 0 .. Max_Reference := 0;
   Failures  : Natural := 0;

   procedure Check (Condition : Boolean; Message : String);
   procedure Check (Condition : Boolean; Message : String) is
   begin
      if not Condition then
         Put_Line ("FAIL: " & Message);
         Failures := Failures + 1;
      end if;
   end Check;

   procedure Reset;
   procedure Reset is
   begin
      Ref_Count := 0;
      Bench.Open_Heap.Reset;
   end Reset;

   procedure Insert (K : Key_Type);
   procedure Insert (K : Key_Type) is
   begin
      Ref_Count := Ref_Count + 1;
      Reference (Ref_Count) := K;
      Bench.Open_Heap.Insert (K);
   end Insert;

   procedure Extract (Min_Side : Boolean);
   procedure Extract (Min_Side : Boolean) is
      Best     : Positive := 1;
      Expected : Key_Type;
      Actual   : Key_Type;
   begin
      for I in 2 .. Ref_Count loop
         if (if Min_Side then Reference (I) < Reference (Best)
             else Reference (I) > Reference (Best))
         then
            Best := I;
         end if;
      end loop;

      Expected := Reference (Best);
      Reference (Best) := Reference (Ref_Count);
      Ref_Count := Ref_Count - 1;

      if Min_Side then
         Bench.Open_Heap.Extract_Min (Actual);
      else
         Bench.Open_Heap.Extract_Max (Actual);
      end if;

      Check (Actual = Expected, "wrong extracted extreme");
      Check (Bench.Open_Heap.Size = Ref_Count, "wrong size");
   end Extract;

   State : Unsigned_32 := 16#9E37_79B9#;

   function Random_Key return Key_Type;
   function Random_Key return Key_Type is
   begin
      State := State xor Shift_Left (State, 13);
      State := State xor Shift_Right (State, 17);
      State := State xor Shift_Left (State, 5);
      return Key_Type (Integer (State mod 2_000_001) - 1_000_000);
   end Random_Key;

begin
   --  Force radix sorting with the complete signed range and duplicates.

   Reset;
   Insert (Key_Type'First);
   Insert (Key_Type'Last);
   Insert (0);
   Insert (-1);
   Insert (1);
   Insert (-1);
   Insert (Key_Type'First);
   Insert (Key_Type'Last);

   while Ref_Count > 0 loop
      Extract (Ref_Count mod 2 = 0);
   end loop;

   --  Exercise repeated representation changes under arbitrary online
   --  traffic.  No operation sequence or key range from the benchmark driver
   --  is assumed here.

   Reset;
   for I in 1 .. 512 loop
      Insert (Random_Key);
   end loop;

   for I in 1 .. 10_000 loop
      State := State xor Shift_Left (State, 13);
      State := State xor Shift_Right (State, 17);
      State := State xor Shift_Left (State, 5);

      if Ref_Count < 128 or else (Ref_Count < 1_024 and then State mod 3 = 0)
      then
         Insert (Random_Key);
      elsif State mod 2 = 0 then
         Extract (True);
      else
         Extract (False);
      end if;
   end loop;

   while Ref_Count > 0 loop
      Extract (Ref_Count mod 2 = 0);
   end loop;

   if Failures = 0 then
      Put_Line ("all open heap tests passed");
   else
      Put_Line (Natural'Image (Failures) & " failure(s)");
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Open_Heap_Test;
