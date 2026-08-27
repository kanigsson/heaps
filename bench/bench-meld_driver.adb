--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Ada.Real_Time; use Ada.Real_Time;
with Interfaces;    use Interfaces;

package body Bench.Meld_Driver is

   type Measure is record
      Elapsed  : Time_Span;
      Ops      : Long_Long_Integer;
      Checksum : Checksum_Type;
   end record;

   function Accumulate (N : Positive) return Measure;
   function Into_Full (N : Positive) return Measure;

   ----------------
   -- Accumulate --
   ----------------

   function Accumulate (N : Positive) return Measure is
      Each  : constant Positive := Positive'Max (1, N / Operands);
      G     : Generator := Seeded;
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      --  Untimed: fill the operands, leaving the accumulator empty

      Reset;
      for W in 1 .. Operands loop
         for I in 1 .. Each loop
            Next (G, K);
            Insert (W, K);
         end loop;
      end loop;

      Start := Clock;
      for W in 1 .. Operands loop
         Meld (W);
      end loop;
      declare
         Elapsed : constant Time_Span := Clock - Start;
      begin
         --  Drain outside the timed phase, purely to checksum the result: a
         --  meld that lost or duplicated a key shows up here rather than as a
         --  performance difference.

         for I in 1 .. Each * Operands loop
            Extract_Min (K);
            Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
         end loop;

         return (Elapsed, Long_Long_Integer (Operands), Sum);
      end;
   end Accumulate;

   ---------------
   -- Into_Full --
   ---------------

   function Into_Full (N : Positive) return Measure is
      G     : Generator := Seeded (55_555_555_551);
      K     : Key_Type;
      Sum   : Checksum_Type := 0;
      Start : Time;
   begin
      --  The lopsided case: a large accumulator receives small operands. A
      --  rebuild pays for the whole accumulator every time, however little
      --  arrives; a mergeable heap does not.

      Reset;
      for I in 1 .. N loop
         Next (G, K);
         Insert (0, K);
      end loop;

      for W in 1 .. Operands loop
         Next (G, K);
         Insert (W, K);
      end loop;

      Start := Clock;
      for W in 1 .. Operands loop
         Meld (W);
      end loop;
      declare
         Elapsed : constant Time_Span := Clock - Start;
      begin
         for I in 1 .. N + Operands loop
            Extract_Min (K);
            Sum := Sum + Checksum_Type (I) * Checksum_Type (K);
         end loop;

         return (Elapsed, Long_Long_Integer (Operands), Sum);
      end;
   end Into_Full;

   ---------
   -- Run --
   ---------

   procedure Run (Sizes : Size_Array; Reps : Positive := 5) is

      procedure One (Scenario : String;
                     What     : not null access function (N : Positive)
                                                         return Measure);

      procedure One (Scenario : String;
                     What     : not null access function (N : Positive)
                                                         return Measure)
      is
      begin
         for N of Sizes loop
            declare
               Best : Measure := What (N);
            begin
               for R in 2 .. Reps loop
                  declare
                     Try : constant Measure := What (N);
                  begin
                     if Try.Elapsed < Best.Elapsed then
                        Best := Try;
                     end if;
                  end;
               end loop;

               Print_Row (Heap_Name, Scenario, N,
                          To_Duration (Best.Elapsed), Best.Ops, Best.Checksum);
            end;
         end loop;
      end One;

   begin
      One ("meld-accumulate", Accumulate'Access);
      One ("meld-into-full", Into_Full'Access);
   end Run;

end Bench.Meld_Driver;
