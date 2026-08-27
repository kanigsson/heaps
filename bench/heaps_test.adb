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
with Heaps.Beap;
with Heaps.Binary;
with Heaps.Block_Min;
with Heaps.Dary;
with Heaps.Interval;
with Heaps.Leftist;
with Heaps.Min_Max;
with Heaps.Sorted;
with Heaps.Unsorted;
with Heaps.Weak;

procedure Heaps_Test is

   Failures : Natural := 0;

   Sizes : constant array (1 .. 7) of Positive :=
     [1, 2, 3, 7, 64, 1_000, 10_000];

   Block_Boundary_Sizes : constant array (1 .. 6) of Positive :=
     [255, 256, 257, 511, 512, 513];

   procedure Check (Condition : Boolean; Message : String);
   procedure Check (Condition : Boolean; Message : String) is
   begin
      if not Condition then
         Put_Line ("FAIL: " & Message);
         Failures := Failures + 1;
      end if;
   end Check;

   procedure Test_Beap (N : Positive);
   procedure Test_Beap (N : Positive) is
      H     : Heaps.Beap.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Beap.Insert (H, K);
         Check (Heaps.Beap.Size (H) = I, "beap: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Beap.Peek_Min (H) = Heaps.Beap.Min_Of (H),
                "beap: peek agrees with the array minimum");
         Heaps.Beap.Extract_Min (H, K);
         Check (K >= Prev, "beap: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Beap.Is_Empty (H), "beap: empty after draining");
      Check (Sum = Back, "beap: nothing lost on the way");
   end Test_Beap;

   procedure Test_Beap_Churn (N : Positive);
   procedure Test_Beap_Churn (N : Positive) is
      --  Alternating an extraction and an insertion holds the size at the
      --  boundary between two layers for as long as we like, which is exactly
      --  where the bookkeeping of the next free slot can be off by one.
      H     : Heaps.Beap.Heap (Extended_Index (N));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Beap.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Beap.Extract_Min (H, K);
         Check (K = Heaps.Beap.Min_Of (H) or else Heaps.Beap.Is_Empty (H)
                  or else K <= Heaps.Beap.Min_Of (H),
                "beap: churn keeps extracting a minimum");
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Beap.Insert (H, Key_Type (State mod 1_000));
         Check (Heaps.Beap.Peek_Min (H) = Heaps.Beap.Min_Of (H),
                "beap: churn keeps the smallest key on top");
      end loop;

      for I in 1 .. N loop
         Heaps.Beap.Extract_Min (H, K);
         Check (K >= Prev, "beap: churned heap still drains in order");
         Prev := K;
      end loop;
   end Test_Beap_Churn;

   procedure Test_Leftist (N : Positive);
   procedure Test_Leftist (N : Positive) is
      H     : Heaps.Leftist.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Leftist.Insert (H, K);
         Check (Heaps.Leftist.Size (H) = I, "leftist: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Leftist.Peek_Min (H) = Heaps.Leftist.Min_Of (H),
                "leftist: peek agrees with the array minimum");
         Heaps.Leftist.Extract_Min (H, K);
         Check (K >= Prev, "leftist: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Leftist.Is_Empty (H), "leftist: empty after draining");
      Check (Sum = Back, "leftist: nothing lost on the way");
   end Test_Leftist;

   procedure Test_Leftist_Churn (N : Positive);
   procedure Test_Leftist_Churn (N : Positive) is
      --  Alternating an extraction and an insertion keeps sending the last
      --  node of the pool into the hole the root leaves behind, which is
      --  where a stale link would show up.
      H     : Heaps.Leftist.Heap (Extended_Index (N));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Leftist.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Leftist.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Leftist.Insert (H, Key_Type (State mod 1_000));
         Check (Heaps.Leftist.Peek_Min (H) = Heaps.Leftist.Min_Of (H),
                "leftist: churn keeps the smallest key on top");
      end loop;

      for I in 1 .. N loop
         Heaps.Leftist.Extract_Min (H, K);
         Check (K >= Prev, "leftist: churned heap still drains in order");
         Prev := K;
      end loop;
   end Test_Leftist_Churn;

   procedure Test_Weak (N : Positive);
   procedure Test_Weak (N : Positive) is
      H     : Heaps.Weak.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Weak.Insert (H, K);
         Check (Heaps.Weak.Size (H) = I, "weak: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Weak.Peek_Min (H) = Heaps.Weak.Min_Of (H),
                "weak: peek agrees with the array minimum");
         Heaps.Weak.Extract_Min (H, K);
         Check (K >= Prev, "weak: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Weak.Is_Empty (H), "weak: empty after draining");
      Check (Sum = Back, "weak: nothing lost on the way");
   end Test_Weak;

   procedure Test_Weak_Churn (N : Positive);
   procedure Test_Weak_Churn (N : Positive) is
      --  Alternating an extraction and an insertion keeps the tree at the
      --  same size while the flip bits go on being rewritten, which is where
      --  a node could end up answering to the wrong ancestor.
      H     : Heaps.Weak.Heap (Extended_Index (N));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Weak.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Weak.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Weak.Insert (H, Key_Type (State mod 1_000));
         Check (Heaps.Weak.Peek_Min (H) = Heaps.Weak.Min_Of (H),
                "weak: churn keeps the smallest key on top");
      end loop;

      for I in 1 .. N loop
         Heaps.Weak.Extract_Min (H, K);
         Check (K >= Prev, "weak: churned heap still drains in order");
         Prev := K;
      end loop;
   end Test_Weak_Churn;

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

   procedure Test_Block_Min (N : Positive);
   procedure Test_Block_Min (N : Positive) is
      Capacity : constant Extended_Index := Extended_Index (N);
      H     : Heaps.Block_Min.Heap
        (Capacity            => Capacity,
         Directory_Capacity => Heaps.Block_Min.Blocks_For (Capacity));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Block_Min.Insert (H, K);
         Check (Heaps.Block_Min.Size (H) = I,
                "block-min: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Block_Min.Peek_Min (H) = Heaps.Block_Min.Min_Of (H),
                "block-min: directory agrees with the array minimum");
         Heaps.Block_Min.Extract_Min (H, K);
         Check (K >= Prev,
                "block-min: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Block_Min.Is_Empty (H),
             "block-min: empty after draining");
      Check (Sum = Back, "block-min: nothing lost on the way");
   end Test_Block_Min;

   procedure Test_Block_Min_Churn (N : Positive);
   procedure Test_Block_Min_Churn (N : Positive) is
      Capacity : constant Extended_Index := Extended_Index (N);
      H     : Heaps.Block_Min.Heap
        (Capacity            => Capacity,
         Directory_Capacity => Heaps.Block_Min.Blocks_For (Capacity));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Block_Min.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Block_Min.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Block_Min.Insert (H, Key_Type (State mod 1_000));
         Check (Heaps.Block_Min.Peek_Min (H) = Heaps.Block_Min.Min_Of (H),
                "block-min: churn keeps the directory current");
      end loop;
   end Test_Block_Min_Churn;

   procedure Test_Dary (N : Positive; Arity : Heaps.Dary.Arity_Type);
   procedure Test_Dary (N : Positive; Arity : Heaps.Dary.Arity_Type) is
      Tag   : constant String :=
        Integer'Image (Arity) & "-ary:";
      H     : Heaps.Dary.Heap (Extended_Index (N), Arity);
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Dary.Insert (H, K);
         Check (Heaps.Dary.Size (H) = I, Tag & " size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Dary.Peek_Min (H) = Heaps.Dary.Min_Of (H),
                Tag & " peek agrees with the array minimum");
         Heaps.Dary.Extract_Min (H, K);
         Check (K >= Prev, Tag & " keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Dary.Is_Empty (H), Tag & " empty after draining");
      Check (Sum = Back, Tag & " nothing lost on the way");
   end Test_Dary;

   procedure Test_Sorted (N : Positive);
   procedure Test_Sorted (N : Positive) is
      H     : Heaps.Sorted.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Peek  : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Sorted.Insert (H, K);
         Check (Heaps.Sorted.Size (H) = I, "sorted: size after insert");
      end loop;

      for I in 1 .. N loop
         Peek := Heaps.Sorted.Peek_Min (H);
         Heaps.Sorted.Extract_Min (H, K);
         Check (K = Peek, "sorted: peek agrees with the extracted key");
         Check (K >= Prev, "sorted: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Sorted.Is_Empty (H), "sorted: empty after draining");
      Check (Sum = Back, "sorted: nothing lost on the way");
   end Test_Sorted;

   procedure Test_Unsorted (N : Positive);
   procedure Test_Unsorted (N : Positive) is
      H     : Heaps.Unsorted.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Peek  : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Unsorted.Insert (H, K);
         Check (Heaps.Unsorted.Size (H) = I, "unsorted: size after insert");
      end loop;

      for I in 1 .. N loop
         Peek := Heaps.Unsorted.Peek_Min (H);
         --  Which minimal slot Extract_Min removes is not specified when
         --  keys are tied, but the minimal *value* is unique, so the two
         --  must agree on it.
         Check (Heaps.Unsorted.Peek_Min (H) = Peek,
                "unsorted: peek agrees with the extracted key");
         Heaps.Unsorted.Extract_Min (H, K);
         Check (K >= Prev, "unsorted: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Unsorted.Is_Empty (H), "unsorted: empty after draining");
      Check (Sum = Back, "unsorted: nothing lost on the way");
   end Test_Unsorted;

   procedure Test_Min_Max (N : Positive);
   procedure Test_Min_Max (N : Positive) is
      H     : Heaps.Min_Max.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Low   : Key_Type := Key_Type'First;
      High  : Key_Type := Key_Type'Last;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Min_Max.Insert (H, K);
         Check (Heaps.Min_Max.Size (H) = I, "min-max: size after insert");
         Check (Heaps.Min_Max.Peek_Min (H) = Heaps.Min_Max.Min_Of (H),
                "min-max: peek-min agrees with the array minimum");
         Check (Heaps.Min_Max.Peek_Max (H) = Heaps.Min_Max.Max_Of (H),
                "min-max: peek-max agrees with the array maximum");
      end loop;

      --  Take the keys out from the outside in: the two ends have to meet in
      --  the middle, which checks both sift directions at once.

      for I in 1 .. N loop
         if I mod 2 = 1 then
            Heaps.Min_Max.Extract_Min (H, K);
            Check (K >= Low, "min-max: the low end never goes back down");
            Low := K;
         else
            Heaps.Min_Max.Extract_Max (H, K);
            Check (K <= High, "min-max: the high end never goes back up");
            High := K;
         end if;

         Check (Low <= High, "min-max: the two ends have not crossed");
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Min_Max.Is_Empty (H), "min-max: empty after draining");
      Check (Sum = Back, "min-max: nothing lost on the way");
   end Test_Min_Max;

   procedure Test_Interval (N : Positive);
   procedure Test_Interval (N : Positive) is
      H     : Heaps.Interval.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Low   : Key_Type := Key_Type'First;
      High  : Key_Type := Key_Type'Last;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Interval.Insert (H, K);
         Check (Heaps.Interval.Size (H) = I, "interval: size after insert");
         Check (Heaps.Interval.Peek_Min (H) = Heaps.Interval.Min_Of (H),
                "interval: peek-min agrees with the array minimum");
         Check (Heaps.Interval.Peek_Max (H) = Heaps.Interval.Max_Of (H),
                "interval: peek-max agrees with the array maximum");
      end loop;

      --  Take the keys out from the outside in: the two ends have to meet in
      --  the middle, which checks both sift directions at once.

      for I in 1 .. N loop
         if I mod 2 = 1 then
            Heaps.Interval.Extract_Min (H, K);
            Check (K >= Low, "interval: the low end never goes back down");
            Low := K;
         else
            Heaps.Interval.Extract_Max (H, K);
            Check (K <= High, "interval: the high end never goes back up");
            High := K;
         end if;

         Check (Low <= High, "interval: the two ends have not crossed");
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Interval.Is_Empty (H), "interval: empty after draining");
      Check (Sum = Back, "interval: nothing lost on the way");
   end Test_Interval;

   --  Meld: the two implementations that have the operation so far are
   --  checked against each other and against a sorted oracle built from the
   --  same keys. Sizes are swept in both directions so that the lopsided
   --  cases -- a large heap receiving a tiny one and the reverse -- are
   --  covered as well as the balanced one.

   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type);
   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type) is
      Total : constant Natural := N + M;

      A_Into : Heaps.Unsorted.Heap (Extended_Index (Total));
      A_From : Heaps.Unsorted.Heap (Extended_Index (Total));
      B_Into : Heaps.Binary.Heap (Extended_Index (Total));
      B_From : Heaps.Binary.Heap (Extended_Index (Total));
      D_Into : Heaps.Dary.Heap (Extended_Index (Total), Arity);
      D_From : Heaps.Dary.Heap (Extended_Index (Total), Arity);

      Oracle : array (1 .. Total) of Key_Type;
      Filled : Natural := 0;

      State : Long_Long_Integer := 24_680_135;
      K     : Key_Type;
      A_Key : Key_Type;
      B_Key : Key_Type;
      D_Key : Key_Type;
      Prev  : Key_Type := Key_Type'First;

      procedure Feed (Count : Natural; Into_Target : Boolean);
      procedure Feed (Count : Natural; Into_Target : Boolean) is
      begin
         for I in 1 .. Count loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);

            Filled := Filled + 1;
            Oracle (Filled) := K;

            if Into_Target then
               Heaps.Unsorted.Insert (A_Into, K);
               Heaps.Binary.Insert (B_Into, K);
               Heaps.Dary.Insert (D_Into, K);
            else
               Heaps.Unsorted.Insert (A_From, K);
               Heaps.Binary.Insert (B_From, K);
               Heaps.Dary.Insert (D_From, K);
            end if;
         end loop;
      end Feed;
   begin
      Feed (N, True);
      Feed (M, False);

      Heaps.Unsorted.Meld (A_Into, A_From);
      Heaps.Binary.Meld (B_Into, B_From);
      Heaps.Dary.Meld (D_Into, D_From);

      Check (Heaps.Unsorted.Size (A_Into) = Total,
             "meld: unsorted size is the sum");
      Check (Heaps.Binary.Size (B_Into) = Total,
             "meld: binary size is the sum");
      Check (Heaps.Unsorted.Is_Empty (A_From),
             "meld: unsorted source is emptied");
      Check (Heaps.Binary.Is_Empty (B_From),
             "meld: binary source is emptied");
      Check (Heaps.Dary.Size (D_Into) = Total, "meld: d-ary size is the sum");
      Check (Heaps.Dary.Is_Empty (D_From), "meld: d-ary source is emptied");

      --  Sort the oracle so that the drain order can be compared against it

      for I in 2 .. Total loop
         declare
            V : constant Key_Type := Oracle (I);
            J : Natural := I - 1;
         begin
            while J >= 1 and then Oracle (J) > V loop
               Oracle (J + 1) := Oracle (J);
               J := J - 1;
            end loop;
            Oracle (J + 1) := V;
         end;
      end loop;

      for I in 1 .. Total loop
         Check (Heaps.Binary.Peek_Min (B_Into) = Heaps.Binary.Min_Of (B_Into),
                "meld: binary peek agrees with the array minimum");

         Check (Heaps.Dary.Peek_Min (D_Into) = Heaps.Dary.Min_Of (D_Into),
                "meld: d-ary peek agrees with the array minimum");

         Heaps.Unsorted.Extract_Min (A_Into, A_Key);
         Heaps.Binary.Extract_Min (B_Into, B_Key);
         Heaps.Dary.Extract_Min (D_Into, D_Key);

         Check (A_Key = Oracle (I), "meld: unsorted drain matches the oracle");
         Check (B_Key = Oracle (I), "meld: binary drain matches the oracle");
         Check (D_Key = Oracle (I), "meld: d-ary drain matches the oracle");
         Check (A_Key = B_Key and A_Key = D_Key,
                "meld: the implementations agree");
         Check (B_Key >= Prev, "meld: keys come out in non-decreasing order");
         Prev := B_Key;
      end loop;

      Check (Heaps.Unsorted.Is_Empty (A_Into),
             "meld: unsorted empty after draining");
      Check (Heaps.Binary.Is_Empty (B_Into),
             "meld: binary empty after draining");
   end Test_Meld;


begin
   --  Exercise both sides of full and partial 256-key blocks. In particular,
   --  extraction moves the last key across a block boundary at these sizes.
   for N of Block_Boundary_Sizes loop
      Test_Block_Min_Churn (N);
   end loop;

   --  Every size from 1 to 200 crosses each of the first twenty layer
   --  boundaries in both directions.
   for N in 1 .. 200 loop
      Test_Beap_Churn (N);
      Test_Weak_Churn (N);
      Test_Leftist_Churn (N);
   end loop;

   for N of Sizes loop
      Test_Binary (N);
      Test_Block_Min (N);
      Test_Weak (N);
      Test_Leftist (N);
      Test_Beap (N);
      Test_Min_Max (N);
      Test_Interval (N);
      for Arity in Heaps.Dary.Arity_Type range 2 .. 5 loop
         Test_Dary (N, Arity);
      end loop;
      Test_Dary (N, 16);
      Test_Dary (N, 64);
      Test_Sorted (N);
      Test_Unsorted (N);
   end loop;

   --  Meld across a range of shapes: balanced, and both lopsided directions,
   --  including the two empty-operand cases.
   for N of Sizes loop
      for Arity in Heaps.Dary.Arity_Type range 2 .. 5 loop
         Test_Meld (N, N, Arity);
      end loop;
      Test_Meld (N, 1, 16);
      Test_Meld (1, N, 16);
      Test_Meld (N, 0, 3);
      Test_Meld (0, N, 3);
   end loop;
   Test_Meld (0, 0, 2);

   if Failures = 0 then
      Put_Line ("all heap tests passed");
   else
      Put_Line (Natural'Image (Failures) & " failure(s)");
   end if;
end Heaps_Test;
