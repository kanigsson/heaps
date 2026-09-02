--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Entry point of the benchmark suite: one line per heap kind, each measured
--  on the same scenarios and the same key sequence.
--
--  Options, all optional and processed after the run, so that one run feeds
--  every output:
--
--    --summary          bar chart per size, after the measurement rows
--    --markdown=PATH    regenerate the results document
--    --json=PATH        write the measurements for the interactive page
--    --machine=TEXT     the hardware and switches, quoted in the document

with Ada.Command_Line;
with Bench;
with Bench.Beap_Heap;
with Bench.Binary_Heap;
with Bench.Block_Min_Heap;
with Bench.Dary_4;
with Bench.Dary_8;
with Bench.Dary_16;
with Bench.Interval_Heap;
with Bench.Leftist_Heap;
with Bench.Min_Max_Heap;
with Bench.Min_Max_Tournament_Heap;
with Bench.Open_Heap;
with Bench.Open_Proved_Heap;
with Bench.Pairing_Heap;
with Bench.Radix_Heap;
with Bench.Skew_Heap;
with Bench.Sorted_Heap;
with Bench.Sorted_Linked_Heap;
with Bench.Tournament_Heap;
with Bench.Unsorted_Heap;
with Bench.Weak_Heap;

procedure Bench_Main is

   Sizes : constant Bench.Size_Array :=
     [1_000, 10_000, 100_000, 1_000_000];

   Beap_Sizes : constant Bench.Size_Array := [1_000, 10_000, 100_000];
   --  An O(sqrt n) operation costs about thirty times as much per decade of
   --  size, so three decades are as far as this can usefully run.

   Baseline_Sizes : constant Bench.Size_Array := [1_000, 10_000];
   --  A linear operation makes these scenarios quadratic, a hundredfold per
   --  decade, so they run over two.

   function Option (Name : String; Default : String) return String;
   --  The value of the first --name=value argument, or Default

   ------------
   -- Option --
   ------------

   function Option (Name : String; Default : String) return String is
   begin
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         declare
            Arg : constant String := Ada.Command_Line.Argument (I);
         begin
            if Arg'Length > Name'Length
              and then Arg (Arg'First .. Arg'First + Name'Length - 1) = Name
            then
               return Arg (Arg'First + Name'Length .. Arg'Last);
            end if;
         end;
      end loop;
      return Default;
   end Option;

begin
   Bench.Print_Header;
   Bench.Binary_Heap.Runner.Run (Sizes);
   Bench.Tournament_Heap.Runner.Run (Sizes);
   Bench.Block_Min_Heap.Runner.Run (Beap_Sizes);
   Bench.Dary_4.Runner.Run (Sizes);
   Bench.Dary_8.Runner.Run (Sizes);
   Bench.Dary_16.Runner.Run (Sizes);
   Bench.Weak_Heap.Runner.Run (Sizes);
   Bench.Leftist_Heap.Runner.Run (Sizes);
   Bench.Skew_Heap.Runner.Run (Sizes);
   Bench.Pairing_Heap.Runner.Run (Sizes);
   Bench.Min_Max_Heap.Runner.Run (Sizes);
   Bench.Min_Max_Tournament_Heap.Runner.Run (Sizes);
   Bench.Interval_Heap.Runner.Run (Sizes);
   Bench.Open_Heap.Runner.Run (Sizes);
   Bench.Open_Proved_Heap.Runner.Run (Sizes);
   Bench.Beap_Heap.Runner.Run (Beap_Sizes);
   Bench.Sorted_Heap.Runner.Run (Baseline_Sizes);
   Bench.Sorted_Linked_Heap.Runner.Run (Baseline_Sizes);
   Bench.Unsorted_Heap.Runner.Run (Baseline_Sizes);
   Bench.Radix_Heap.Runner.Run (Baseline_Sizes);

   --  Meld, each entry over the sizes its own worst operation can afford.
   Bench.Binary_Heap.Meld_Runner.Run (Sizes);
   Bench.Tournament_Heap.Meld_Runner.Run (Sizes);
   Bench.Dary_4.Meld_Runner.Run (Sizes);
   Bench.Dary_8.Meld_Runner.Run (Sizes);
   Bench.Dary_16.Meld_Runner.Run (Sizes);
   Bench.Weak_Heap.Meld_Runner.Run (Sizes);
   Bench.Min_Max_Heap.Meld_Runner.Run (Sizes);
   Bench.Min_Max_Tournament_Heap.Meld_Runner.Run (Sizes);
   Bench.Interval_Heap.Meld_Runner.Run (Sizes);
   Bench.Open_Heap.Meld_Runner.Run (Sizes);
   Bench.Open_Proved_Heap.Meld_Runner.Run (Sizes);
   Bench.Block_Min_Heap.Meld_Runner.Run (Beap_Sizes);
   Bench.Beap_Heap.Meld_Runner.Run (Beap_Sizes);
   Bench.Unsorted_Heap.Meld_Runner.Run (Baseline_Sizes);
   Bench.Sorted_Heap.Meld_Runner.Run (Baseline_Sizes);
   Bench.Sorted_Linked_Heap.Meld_Runner.Run (Baseline_Sizes);
   Bench.Leftist_Heap.Meld_Runner.Run (Sizes);
   Bench.Skew_Heap.Meld_Runner.Run (Sizes);
   Bench.Pairing_Heap.Meld_Runner.Run (Sizes);
   Bench.Radix_Heap.Meld_Runner.Run (Baseline_Sizes);

   Bench.Min_Max_Heap.Deque_Runner.Run (Sizes);
   Bench.Min_Max_Tournament_Heap.Deque_Runner.Run (Sizes);
   Bench.Interval_Heap.Deque_Runner.Run (Sizes);
   Bench.Open_Heap.Deque_Runner.Run (Sizes);
   Bench.Open_Proved_Heap.Deque_Runner.Run (Sizes);

   declare
      Machine : constant String := Option ("--machine=", "an unnamed machine");
   begin
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         if Ada.Command_Line.Argument (I) = "--summary" then
            Bench.Print_Summary;
         end if;
      end loop;

      if Option ("--markdown=", "") /= "" then
         Bench.Write_Markdown (Option ("--markdown=", ""), Machine);
      end if;

      if Option ("--json=", "") /= "" then
         Bench.Write_Json (Option ("--json=", ""), Machine);
      end if;
   end;
end Bench_Main;
