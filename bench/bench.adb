--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;
with Ada.Strings.Fixed;   use Ada.Strings.Fixed;
with Ada.Strings;         use Ada.Strings;
with Ada.Numerics.Long_Elementary_Functions;
use  Ada.Numerics.Long_Elementary_Functions;
with Interfaces;          use Interfaces;

package body Bench is

   Name_Width     : constant := 21;
   Scenario_Width : constant := 15;

   subtype Heap_Name_Type is String (1 .. Name_Width);
   subtype Scenario_Type  is String (1 .. Scenario_Width);

   --  Measurements are kept as they are printed, so that Print_Summary can
   --  relate the heaps to each other once a run is over.

   Max_Rows : constant := 4_096;

   type Row is record
      Heap      : Heap_Name_Type;
      Scenario  : Scenario_Type;
      N         : Positive;
      Ns_Per_Op : Long_Float;
      Checksum  : Checksum_Type;
   end record;

   Rows  : array (1 .. Max_Rows) of Row;
   Count : Natural := 0;

   Baseline : constant String := "binary";
   --  The heap every other one is expressed relative to.

   Summary_Scenarios : constant array (1 .. 6) of Scenario_Type :=
     [Head ("fill", Scenario_Width),
      Head ("drain", Scenario_Width),
      Head ("churn", Scenario_Width),
      Head ("replace-forward", Scenario_Width),
      Head ("insert-asc", Scenario_Width),
      Head ("insert-desc", Scenario_Width)];
   --  The single-heap scenarios. Meld and deque scenarios are left out: they
   --  do not run for every entry, and a meld figure is a cost per meld rather
   --  than per operation.

   Bar_Unit : constant := 8;
   --  Characters per unit of relative cost, so the baseline is eight wide.

   Bar_Max : constant := 64;

   Block : constant String :=
     Character'Val (16#E2#) & Character'Val (16#96#) & Character'Val (16#88#);
   --  U+2588 FULL BLOCK, spelled out as its UTF-8 bytes so that the source
   --  does not depend on the encoding the compiler assumes for it.

   Max_Kinds : constant := 64;

   type Size_List     is array (1 .. Max_Kinds) of Positive;
   type Heap_List     is array (1 .. Max_Kinds) of Heap_Name_Type;
   type Scenario_List is array (1 .. Max_Kinds) of Scenario_Type;

   procedure Collect_Sizes (List : out Size_List; Last : out Natural);
   --  The sizes measured, smallest first. A heap kind may skip the larger
   --  ones, so this is a union rather than any one entry's set.

   procedure Collect_Heaps (List : out Heap_List; Last : out Natural);
   procedure Collect_Scenarios (List : out Scenario_List; Last : out Natural);
   --  Both in the order the run first printed them.

   function Log10 (X : Long_Float) return Long_Float is (Log (X) / Log (10.0));

   function Fixed_Image (X : Long_Float) return String;
   function Grouped (N : Positive) return String;
   function Bar (Ratio : Long_Float) return String;

   ------------
   -- Seeded --
   ------------

   function Seeded (Seed : Long_Long_Integer := 88_172_645_463_325_252)
                     return Generator is
   begin
      return (State => Interfaces.Unsigned_64'Mod (Seed));
   end Seeded;

   ----------
   -- Next --
   ----------

   procedure Next (G : in out Generator; K : out Key_Type) is
      --  xorshift64: cheap enough that the generator does not dominate the
      --  measurement, and reproducible across platforms.
      X : Unsigned_64 := G.State;
   begin
      X := X xor Shift_Left (X, 13);
      X := X xor Shift_Right (X, 7);
      X := X xor Shift_Left (X, 17);
      G.State := X;
      K := Key_Type (X mod 2 ** 30);
   end Next;

   -------------------
   -- Collect_Sizes --
   -------------------

   procedure Collect_Sizes (List : out Size_List; Last : out Natural) is
   begin
      List := [others => 1];
      Last := 0;
      for I in 1 .. Count loop
         if (for all J in 1 .. Last => List (J) /= Rows (I).N) then
            declare
               Place : Natural := Last + 1;
            begin
               while Place > 1 and then List (Place - 1) > Rows (I).N loop
                  List (Place) := List (Place - 1);
                  Place := Place - 1;
               end loop;
               List (Place) := Rows (I).N;
               Last := Last + 1;
            end;
         end if;
      end loop;
   end Collect_Sizes;

   -------------------
   -- Collect_Heaps --
   -------------------

   procedure Collect_Heaps (List : out Heap_List; Last : out Natural) is
   begin
      List := [others => Head ("", Name_Width)];
      Last := 0;
      for I in 1 .. Count loop
         if (for all J in 1 .. Last => List (J) /= Rows (I).Heap) then
            Last := Last + 1;
            List (Last) := Rows (I).Heap;
         end if;
      end loop;
   end Collect_Heaps;

   -----------------------
   -- Collect_Scenarios --
   -----------------------

   procedure Collect_Scenarios (List : out Scenario_List; Last : out Natural)
   is
   begin
      List := [others => Head ("", Scenario_Width)];
      Last := 0;
      for I in 1 .. Count loop
         if (for all J in 1 .. Last => List (J) /= Rows (I).Scenario) then
            Last := Last + 1;
            List (Last) := Rows (I).Scenario;
         end if;
      end loop;
   end Collect_Scenarios;

   -----------------
   -- Fixed_Image --
   -----------------

   function Fixed_Image (X : Long_Float) return String is
      Rounded : constant Long_Long_Integer :=
        Long_Long_Integer (Long_Float'Rounding (X * 100.0));
      Whole   : constant String :=
        Trim (Long_Long_Integer'Image (Rounded / 100), Both);
      Frac    : constant String :=
        Long_Long_Integer'Image (100 + Rounded mod 100);
      --  " 1dd": take the last two characters to get a zero-padded fraction
   begin
      return Whole & "." & Frac (Frac'Last - 1 .. Frac'Last);
   end Fixed_Image;

   -------------
   -- Grouped --
   -------------

   function Grouped (N : Positive) return String is
      Digits_Of : constant String := Trim (Positive'Image (N), Both);
      Result    : String (1 .. 2 * Digits_Of'Length);
      Last      : Natural := 0;
   begin
      for I in Digits_Of'Range loop
         if Last > 0 and then (Digits_Of'Last - I + 1) mod 3 = 0 then
            Last := Last + 1;
            Result (Last) := ' ';
         end if;
         Last := Last + 1;
         Result (Last) := Digits_Of (I);
      end loop;
      return Result (1 .. Last);
   end Grouped;

   ---------
   -- Bar --
   ---------

   function Bar (Ratio : Long_Float) return String is
      Length : constant Natural :=
        Natural'Max
          (1, Natural (Long_Float'Rounding (Ratio * Long_Float (Bar_Unit))));
      Shown  : constant Natural := Natural'Min (Length, Bar_Max);
      Result : String (1 .. Shown * Block'Length);
   begin
      for I in 1 .. Shown loop
         Result (Block'Length * (I - 1) + 1 .. Block'Length * I) := Block;
      end loop;

      --  A bar that would run off the line is cut and marked as cut.
      return (if Length > Bar_Max then Result & "+" else Result);
   end Bar;

   ------------------
   -- Print_Header --
   ------------------

   procedure Print_Header is
   begin
      Put_Line
        ("heap                 scenario           "
         & "n        ns/op        checksum");
      Put_Line (String'(1 .. 74 => '-'));
   end Print_Header;

   ---------------
   -- Print_Row --
   ---------------

   procedure Print_Row
     (Heap_Name : String;
      Scenario  : String;
      N         : Positive;
      Seconds   : Duration;
      Ops       : Long_Long_Integer;
      Checksum  : Checksum_Type)
   is
      Ns_Per_Op : constant Long_Float :=
        (if Ops = 0 then 0.0
         else Long_Float (Seconds) * 1.0E9 / Long_Float (Ops));

      procedure Pad (S : String; Width : Positive);
      procedure Pad (S : String; Width : Positive) is
      begin
         Put (S);
         if S'Length < Width then
            Put (String'(1 .. Width - S'Length => ' '));
         end if;
      end Pad;

      Shown : constant String := Fixed_Image (Ns_Per_Op);
   begin
      if Count < Max_Rows then
         Count := Count + 1;
         Rows (Count) :=
           (Heap      => Head (Heap_Name, Name_Width),
            Scenario  => Head (Scenario, Scenario_Width),
            N         => N,
            Ns_Per_Op => Ns_Per_Op,
            Checksum  => Checksum);
      end if;

      Pad (Heap_Name, Name_Width);
      Pad (Scenario, Scenario_Width);
      Put (N, Width => 10);
      Put ("  ");
      if Shown'Length < 9 then
         Put (String'(1 .. 9 - Shown'Length => ' '));
      end if;
      Put (Shown);
      Put ("  ");
      Put (Checksum_Type'Image (Checksum));
      New_Line;
   end Print_Row;

   -------------------
   -- Print_Summary --
   -------------------

   procedure Print_Summary is

      function Measured
        (Heap : Heap_Name_Type; Scenario : Scenario_Type; N : Positive)
         return Long_Float;
      --  The measurement, or 0.0 if this heap did not run this scenario at
      --  this size

      function Geometric_Mean
        (Heap : Heap_Name_Type; N : Positive) return Long_Float;
      --  The geometric mean of the heap's ratio to the baseline over the
      --  summary scenarios, or 0.0 if either of the two is missing one

      procedure Print_Chart (N : Positive);

      --------------
      -- Measured --
      --------------

      function Measured
        (Heap : Heap_Name_Type; Scenario : Scenario_Type; N : Positive)
         return Long_Float is
      begin
         for I in 1 .. Count loop
            if Rows (I).N = N
              and then Rows (I).Scenario = Scenario
              and then Rows (I).Heap = Heap
            then
               return Rows (I).Ns_Per_Op;
            end if;
         end loop;
         return 0.0;
      end Measured;

      --------------------
      -- Geometric_Mean --
      --------------------

      function Geometric_Mean
        (Heap : Heap_Name_Type; N : Positive) return Long_Float
      is
         Sum : Long_Float := 0.0;
      begin
         for S of Summary_Scenarios loop
            declare
               Reference : constant Long_Float :=
                 Measured (Head (Baseline, Name_Width), S, N);
               Time      : constant Long_Float := Measured (Heap, S, N);
            begin
               if Reference <= 0.0 or else Time <= 0.0 then
                  return 0.0;
               end if;
               Sum := Sum + Log (Time / Reference);
            end;
         end loop;

         return Exp (Sum / Long_Float (Summary_Scenarios'Length));
      end Geometric_Mean;

      -----------------
      -- Print_Chart --
      -----------------

      procedure Print_Chart (N : Positive) is
         type Entry_Type is record
            Heap  : Heap_Name_Type;
            Ratio : Long_Float;
         end record;

         Entries : array (1 .. Max_Rows) of Entry_Type :=
           [others => (Heap => Head ("", Name_Width), Ratio => 0.0)];
         Last    : Natural := 0;
      begin
         --  One entry per heap that ran the whole set of scenarios at this
         --  size, in increasing order of relative cost.

         for I in 1 .. Count loop
            declare
               Ratio : constant Long_Float :=
                 (if (for some J in 1 .. Last =>
                        Entries (J).Heap = Rows (I).Heap)
                  then 0.0
                  else Geometric_Mean (Rows (I).Heap, N));
               Place : Natural;
            begin
               if Ratio > 0.0 then
                  Place := Last + 1;
                  while Place > 1
                    and then Entries (Place - 1).Ratio > Ratio
                  loop
                     Entries (Place) := Entries (Place - 1);
                     Place := Place - 1;
                  end loop;
                  Entries (Place) := (Rows (I).Heap, Ratio);
                  Last := Last + 1;
               end if;
            end;
         end loop;

         if Last <= 1 then
            return;
         end if;

         New_Line;
         Put_Line
           ("Relative cost, geometric mean of the "
            & Trim (Integer'Image (Summary_Scenarios'Length), Both)
            & " single-heap scenarios at");
         Put_Line
           ("n = " & Grouped (N) & ", " & Baseline & " heap = 1.00."
            & " Lower is better.");
         New_Line;

         for I in 1 .. Last loop
            declare
               Shown : constant String := Fixed_Image (Entries (I).Ratio);
            begin
               Put (Head (Trim (Entries (I).Heap, Both), 15));
               if Shown'Length < 5 then
                  Put (String'(1 .. 5 - Shown'Length => ' '));
               end if;
               Put (Shown & "  " & Bar (Entries (I).Ratio));
               New_Line;
            end;
         end loop;
      end Print_Chart;

      Sizes : Size_List;
      Last  : Natural;

   begin
      Collect_Sizes (Sizes, Last);

      for I in 1 .. Last loop
         Print_Chart (Sizes (I));
      end loop;
   end Print_Summary;

   -----------------
   -- Strip_Chart --
   -----------------

   Cells_Per_Decade : constant := 8;

   Dot : constant String := Character'Val (16#C2#) & Character'Val (16#B7#);
   --  U+00B7 MIDDLE DOT, as its UTF-8 bytes

   procedure Strip_Chart (S : Scenario_Type) is
      Heaps  : Heap_List;
      Sizes  : Size_List;
      N_Heap : Natural;
      N_Size : Natural;

      Low  : Long_Float := 0.0;
      High : Long_Float := 0.0;

      function Value (H : Heap_Name_Type; N : Positive) return Long_Float;

      -----------
      -- Value --
      -----------

      function Value (H : Heap_Name_Type; N : Positive) return Long_Float is
      begin
         for I in 1 .. Count loop
            if Rows (I).N = N
              and then Rows (I).Scenario = S
              and then Rows (I).Heap = H
            then
               return Rows (I).Ns_Per_Op;
            end if;
         end loop;
         return 0.0;
      end Value;

   begin
      Collect_Heaps (Heaps, N_Heap);
      Collect_Sizes (Sizes, N_Size);

      --  The axis spans every measurement of this scenario, so that the rows
      --  of one chart can be read against each other.

      for I in 1 .. Count loop
         if Rows (I).Scenario = S and then Rows (I).Ns_Per_Op > 0.0 then
            if Low = 0.0 or else Rows (I).Ns_Per_Op < Low then
               Low := Rows (I).Ns_Per_Op;
            end if;
            High := Long_Float'Max (High, Rows (I).Ns_Per_Op);
         end if;
      end loop;

      if Low = 0.0 then
         return;
      end if;

      declare
         Width : constant Positive :=
           1 + Natural (Long_Float'Rounding
                          (Log10 (High / Low) * Long_Float
                             (Cells_Per_Decade)));

         type Order_Entry is record
            Heap : Heap_Name_Type;
            Last : Long_Float;  --  value at the largest size it was run at
            At_N : Positive;
         end record;

         Order : array (1 .. Max_Kinds) of Order_Entry :=
           [others => (Head ("", Name_Width), 0.0, 1)];
         Last  : Natural := 0;
      begin
         for I in 1 .. N_Heap loop
            declare
               Best   : Long_Float := 0.0;
               Best_N : Positive := 1;
            begin
               for J in 1 .. N_Size loop
                  if Value (Heaps (I), Sizes (J)) > 0.0 then
                     Best := Value (Heaps (I), Sizes (J));
                     Best_N := Sizes (J);
                  end if;
               end loop;

               if Best > 0.0 then
                  declare
                     Place : Natural := Last + 1;
                  begin
                     while Place > 1 and then Order (Place - 1).Last > Best
                     loop
                        Order (Place) := Order (Place - 1);
                        Place := Place - 1;
                     end loop;
                     Order (Place) := (Heaps (I), Best, Best_N);
                     Last := Last + 1;
                  end;
               end if;
            end;
         end loop;

         Put_Line
           (Trim (S, Both) & " -- ns/op on a log axis, "
            & Trim (Integer'Image (Cells_Per_Decade), Both)
            & " cells to a decade");
         New_Line;

         for I in 1 .. Last loop
            declare
               Marks : String (1 .. Width) := [others => ' '];
               Strip : String (1 .. 2 * Width);
               Wrote : Natural := 0;
               Shown : constant String := Fixed_Image (Order (I).Last);
            begin
               for J in 1 .. N_Size loop
                  declare
                     V : constant Long_Float :=
                       Value (Order (I).Heap, Sizes (J));
                     C : Natural;
                  begin
                     if V > 0.0 then
                        C := 1 + Natural (Long_Float'Rounding
                                            (Log10 (V / Low) * Long_Float
                                               (Cells_Per_Decade)));
                        Marks (C) :=
                          (if Marks (C) = ' '
                           then Character'Val (Character'Pos ('0') + J)
                           else '*');
                     end if;
                  end;
               end loop;

               for J in Marks'Range loop
                  if Marks (J) = ' ' then
                     Strip (Wrote + 1 .. Wrote + Dot'Length) := Dot;
                     Wrote := Wrote + Dot'Length;
                  else
                     Wrote := Wrote + 1;
                     Strip (Wrote) := Marks (J);
                  end if;
               end loop;

               Put (Head (Trim (Order (I).Heap, Both), 15));
               Put (Strip (1 .. Wrote));
               Put (String'(1 .. 2 + 12 - Shown'Length => ' '));
               Put (Shown);
               Put ("  at n =" & Positive'Image (Order (I).At_N));
               New_Line;
            end;
         end loop;
      end;
   end Strip_Chart;

   --------------------
   -- Write_Markdown --
   --------------------

   procedure Write_Markdown (Path : String; Machine : String) is
      File      : File_Type;
      Scenarios : Scenario_List;
      Sizes     : Size_List;
      Heaps     : Heap_List;
      N_Scen    : Natural;
      N_Size    : Natural;
      N_Heap    : Natural;

      Agreed    : Natural := 0;
      Disagreed : Natural := 0;
   begin
      Collect_Scenarios (Scenarios, N_Scen);
      Collect_Sizes (Sizes, N_Size);
      Collect_Heaps (Heaps, N_Heap);

      Create (File, Out_File, Path);
      Set_Output (File);

      Put_Line ("# Benchmark results");
      New_Line;
      Put_Line ("Nanoseconds per operation, the fastest of five runs, from one");
      Put_Line ("run of the whole suite on " & Machine & ".");
      New_Line;
      Put_Line ("This file is generated. To remake it:");
      New_Line;
      Put_Line ("```sh");
      Put_Line ("gprbuild -P bench.gpr");
      Put_Line ("./bench_main --machine=""" & Machine & """ \");
      Put_Line ("  --markdown=OBSERVATIONS.md --json=docs/results.js");
      Put_Line ("```");
      New_Line;
      Put_Line ("For a view whose metric, sizes and entries can be chosen, open");
      Put_Line ("[docs/index.html](docs/index.html) from a checkout, or the same");
      Put_Line ("page over GitHub Pages where the repository has it enabled.");
      New_Line;

      Put_Line ("## How to read the charts");
      New_Line;
      Put_Line ("Each row is one heap, placed on an axis of nanoseconds per");
      Put_Line ("operation that runs left to right, low to high. The axis is");
      Put_Line ("logarithmic and shared by every row of its chart, so distance");
      Put_Line ("along it is a ratio: eight cells is a factor of ten.");
      New_Line;
      Put_Line ("A digit is a size.");
      for I in 1 .. N_Size loop
         Put_Line
           ("- `" & Trim (Integer'Image (I), Both) & "` is n = "
            & Grouped (Sizes (I)));
      end loop;
      New_Line;
      Put_Line ("A `*` is two or more sizes landing on the same cell, which is");
      Put_Line ("a scenario whose cost does not grow over that stretch. The");
      Put_Line ("spread of the digits is therefore the growth: eight cells per");
      Put_Line ("decade of `n` is linear, four is `sqrt n`, one or two is");
      Put_Line ("logarithmic, and none at all is constant. Rows are ordered by");
      Put_Line ("the figure at the largest size the entry was run at, which the");
      Put_Line ("last column names, since not every entry runs at every size.");
      New_Line;
      Put_Line ("A meld figure is nanoseconds per *meld* rather than per key,");
      Put_Line ("and one measurement is sixteen melds.");
      New_Line;

      Put_Line ("## Overall");
      New_Line;
      Put_Line ("Cost relative to the binary heap, as the geometric mean of the");
      Put_Line ("ratio on each single-heap scenario.");
      New_Line;
      Put_Line ("```");
      Print_Summary;
      Put_Line ("```");
      New_Line;

      Put_Line ("## Scenarios");
      New_Line;
      for I in 1 .. N_Scen loop
         Put_Line ("### " & Trim (Scenarios (I), Both));
         New_Line;
         Put_Line ("```");
         Strip_Chart (Scenarios (I));
         Put_Line ("```");
         New_Line;
      end loop;

      --  Every entry that runs a scenario at a size must return the same
      --  checksum: they see one key stream and owe one answer.

      for I in 1 .. N_Scen loop
         for J in 1 .. N_Size loop
            declare
               Seen  : Boolean := False;
               First : Checksum_Type := 0;
            begin
               for K in 1 .. Count loop
                  if Rows (K).Scenario = Scenarios (I)
                    and then Rows (K).N = Sizes (J)
                  then
                     if not Seen then
                        Seen := True;
                        First := Rows (K).Checksum;
                     elsif Rows (K).Checksum /= First then
                        Disagreed := Disagreed + 1;
                     end if;
                  end if;
               end loop;

               if Seen then
                  Agreed := Agreed + 1;
               end if;
            end;
         end loop;
      end loop;

      Put_Line ("## Checksums");
      New_Line;
      Put_Line
        ("Every entry accumulates a checksum over the keys a scenario makes");
      Put_Line
        ("it see, so entries taking different internal paths over one key");
      Put_Line ("stream owe the same answer.");
      New_Line;
      Put_Line
        ("Groups compared (one per scenario and size):"
         & Natural'Image (Agreed) & ".");
      if Disagreed = 0 then
         Put_Line ("Disagreements: none.");
      else
         Put_Line
           ("Disagreements:" & Natural'Image (Disagreed)
            & " -- a wrong answer somewhere, not a slower one.");
      end if;

      Set_Output (Standard_Output);
      Close (File);
   end Write_Markdown;

   ----------------
   -- Write_Json --
   ----------------

   procedure Write_Json (Path : String; Machine : String) is
      File : File_Type;
   begin
      Create (File, Out_File, Path);
      Set_Output (File);

      Put_Line ("//  Generated by bench_main --json. One row per measurement:");
      Put_Line ("//  [heap, scenario, n, ns/op, checksum].");
      Put_Line ("const MACHINE = " & '"' & Machine & '"' & ";");
      Put_Line ("const RESULTS = [");
      for I in 1 .. Count loop
         Put ("  [""" & Trim (Rows (I).Heap, Both) & """, """
              & Trim (Rows (I).Scenario, Both) & """, "
              & Trim (Positive'Image (Rows (I).N), Both) & ", "
              & Fixed_Image (Rows (I).Ns_Per_Op) & ", """
              & Trim (Checksum_Type'Image (Rows (I).Checksum), Both) & """]");
         if I < Count then
            Put (",");
         end if;
         New_Line;
      end loop;
      Put_Line ("];");

      Set_Output (Standard_Output);
      Close (File);
   end Write_Json;

end Bench;
