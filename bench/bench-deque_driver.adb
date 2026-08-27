--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Ada.Real_Time; use Ada.Real_Time;
with Interfaces;    use Interfaces;

package body Bench.Deque_Driver is

   type Measure is record
      Elapsed  : Time_Span;
      Ops      : Long_Long_Integer;
      Checksum : Checksum_Type;
   end record;

   procedure Prefill (N : Positive);

   function Drain_Max (N : Positive) return Measure;
   function Drain_Both (N : Positive) return Measure;
   function Trim (N : Positive) return Measure;

   -------------
   -- Prefill --
   -------------

   procedure Prefill (N : Positive) is
      G : Generator := Seeded;
      K : Key_Type;
   begin
      Reset;
      for I in 1 .. N loop
         Next (G, K);
         Insert (K);
      end loop;
   end Prefill;

   ---------------
   -- Drain_Max --
   ---------------

   function Drain_Max (N : Positive) return Measure is
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Prefill (N);
      Start := Clock;
      for I in 1 .. N loop
         Extract_Max (K);
         Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Drain_Max;

   ----------------
   -- Drain_Both --
   ----------------

   function Drain_Both (N : Positive) return Measure is
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      --  Alternate the two ends: the keys come out from the outside in, and
      --  the two sift directions are exercised in equal measure.

      Prefill (N);
      Start := Clock;
      for I in 1 .. N loop
         if I mod 2 = 1 then
            Extract_Min (K);
         else
            Extract_Max (K);
         end if;
         Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Drain_Both;

   ----------
   -- Trim --
   ----------

   function Trim (N : Positive) return Measure is
      G     : Generator := Seeded (12_345_678_901);
      K     : Key_Type;
      New_K : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      --  A bounded "best N so far" queue: every insertion is followed by the
      --  eviction of the current worst, which is the standard reason to want
      --  a double-ended heap in the first place.

      Prefill (N);
      Start := Clock;
      for I in 1 .. N loop
         Next (G, New_K);
         Insert (New_K);
         Extract_Max (K);
         Sum := Sum + Checksum_Type (K);
      end loop;
      return (Clock - Start, 2 * Long_Long_Integer (N), Sum);
   end Trim;

   ---------
   -- Run --
   ---------

   procedure Run (Sizes : Size_Array; Reps : Positive := 5) is

      type Scenario is (S_Drain_Max, S_Drain_Both, S_Trim);

      function Label (S : Scenario) return String is
        (case S is
            when S_Drain_Max  => "drain-max",
            when S_Drain_Both => "drain-both",
            when S_Trim       => "trim");

      function Measure_Of (S : Scenario; N : Positive) return Measure is
        (case S is
            when S_Drain_Max  => Drain_Max (N),
            when S_Drain_Both => Drain_Both (N),
            when S_Trim       => Trim (N));

   begin
      for N of Sizes loop
         if N <= Max_Elements then
            for S in Scenario loop
               declare
                  Best : Measure := Measure_Of (S, N);
               begin
                  for R in 2 .. Reps loop
                     declare
                        M : constant Measure := Measure_Of (S, N);
                     begin
                        if M.Elapsed < Best.Elapsed then
                           Best := M;
                        end if;
                     end;
                  end loop;

                  Print_Row
                    (Heap_Name => Heap_Name,
                     Scenario  => Label (S),
                     N         => N,
                     Seconds   => To_Duration (Best.Elapsed),
                     Ops       => Best.Ops,
                     Checksum  => Best.Checksum);
               end;
            end loop;
         end if;
      end loop;
   end Run;

end Bench.Deque_Driver;
