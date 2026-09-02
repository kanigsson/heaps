--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Ada.Real_Time; use Ada.Real_Time;
with Interfaces;    use Interfaces;

package body Bench.Driver is

   use type Key_Type;

   --  The scenarios. Each of them is a procedure that performs its own
   --  untimed set-up, then reports the elapsed time of the measured phase,
   --  the number of operations it covers, and a checksum of the keys it saw.

   type Measure is record
      Elapsed  : Time_Span;
      Ops      : Long_Long_Integer;
      Checksum : Checksum_Type;
   end record;

   function Fill (N : Positive) return Measure;
   function Drain (N : Positive) return Measure;
   function Churn (N : Positive) return Measure;
   function Replace_Forward (N : Positive) return Measure;
   function Ascending (N : Positive) return Measure;
   function Descending (N : Positive) return Measure;

   procedure Prefill (N : Positive);
   --  Untimed: reset the heap and put N pseudo-random keys in it

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

   ----------
   -- Fill --
   ----------

   function Fill (N : Positive) return Measure is
      G     : Generator := Seeded;
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Reset;
      Start := Clock;
      for I in 1 .. N loop
         Next (G, K);
         Insert (K);
         Sum := Sum + Checksum_Type (K);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Fill;

   -----------
   -- Drain --
   -----------

   function Drain (N : Positive) return Measure is
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Prefill (N);
      Start := Clock;
      for I in 1 .. N loop
         Extract_Min (K);
         --  Weighting by the rank makes the checksum sensitive to the order
         --  in which the keys come out, not just to the set of keys.
         Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Drain;

   -----------
   -- Churn --
   -----------

   function Churn (N : Positive) return Measure is
      G     : Generator := Seeded (12_345_678_901);
      K     : Key_Type;
      New_K : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Prefill (N);
      Start := Clock;
      for I in 1 .. N loop
         Extract_Min (K);
         Next (G, New_K);
         Insert (New_K);
         Sum := Sum + Checksum_Type (K);
      end loop;
      return (Clock - Start, 2 * Long_Long_Integer (N), Sum);
   end Churn;

   ---------------------
   -- Replace_Forward --
   ---------------------

   function Replace_Forward (N : Positive) return Measure is
      Initial_G : Generator := Seeded;
      Delta_G   : Generator := Seeded (34_567_890_123);
      K         : Key_Type;
      Increment : Key_Type;
      Sum       : Checksum_Type := 0;
      Start     : Time;
   begin
      Reset;
      for I in 1 .. N loop
         Next (Initial_G, K);
         Insert (K mod 2 ** 29);
      end loop;

      Start := Clock;
      for I in 1 .. N loop
         Extract_Min (K);
         Next (Delta_G, Increment);
         Increment := 1 + Increment mod 2 ** 10;
         Insert (K + Increment);
         Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
      end loop;

      --  Initially K is below 2**29, and even one key receiving all N <=
      --  2**20 increments of at most 2**10 remains within Key_Type.
      return (Clock - Start, 2 * Long_Long_Integer (N), Sum);
   end Replace_Forward;

   ---------------
   -- Ascending --
   ---------------

   function Ascending (N : Positive) return Measure is
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Reset;
      Start := Clock;
      for I in 1 .. N loop
         Insert (Key_Type (I));
         Sum := Sum + Checksum_Type (I);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Ascending;

   ----------------
   -- Descending --
   ----------------

   function Descending (N : Positive) return Measure is
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      Reset;
      Start := Clock;
      for I in reverse 1 .. N loop
         Insert (Key_Type (I));
         Sum := Sum + Checksum_Type (I);
      end loop;
      return (Clock - Start, Long_Long_Integer (N), Sum);
   end Descending;

   ---------
   -- Run --
   ---------

   procedure Run (Sizes : Size_Array; Reps : Positive := 5) is

      type Scenario is
        (S_Fill,
         S_Drain,
         S_Churn,
         S_Replace_Forward,
         S_Ascending,
         S_Descending);

      function Label (S : Scenario) return String is
        (case S is
            when S_Fill            => "fill",
            when S_Drain           => "drain",
            when S_Churn           => "churn",
            when S_Replace_Forward => "replace-forward",
            when S_Ascending       => "insert-asc",
            when S_Descending      => "insert-desc");

      function Measure_Of (S : Scenario; N : Positive) return Measure is
        (case S is
            when S_Fill            => Fill (N),
            when S_Drain           => Drain (N),
            when S_Churn           => Churn (N),
            when S_Replace_Forward => Replace_Forward (N),
            when S_Ascending       => Ascending (N),
            when S_Descending      => Descending (N));

   begin
      for N of Sizes loop
         if N <= Max_Elements then
            for S in Scenario loop
               if Include_Churn or else S /= S_Churn then
                  declare
                     Best : Measure := Measure_Of (S, N);
                  begin
                     --  Keep the fastest run: the minimum is far more stable
                     --  than the mean under scheduling noise.
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
               end if;
            end loop;
         end if;
      end loop;
   end Run;

end Bench.Driver;
