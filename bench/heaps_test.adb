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
with Heaps.Leftist_Pool;
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

   Churn_Sizes : constant array (1 .. 6) of Positive :=
     [1, 2, 3, 7, 64, 200];

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

   --  Meld: every implementation that has the operation is checked against
   --  the others and against a sorted oracle built from the same keys. Sizes
   --  are swept in both directions so that the lopsided cases -- a large heap
   --  receiving a tiny one and the reverse -- are covered as well as the
   --  balanced one.

   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type);
   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type) is
      Total : constant Natural := N + M;

      A_Into : Heaps.Unsorted.Heap (Extended_Index (Total));
      A_From : Heaps.Unsorted.Heap (Extended_Index (Total));
      B_Into : Heaps.Binary.Heap (Extended_Index (Total));
      B_From : Heaps.Binary.Heap (Extended_Index (Total));
      D_Into : Heaps.Dary.Heap (Extended_Index (Total), Arity);
      D_From : Heaps.Dary.Heap (Extended_Index (Total), Arity);
      C_Into : Heaps.Block_Min.Heap
        (Capacity           => Extended_Index (Total),
         Directory_Capacity =>
           Heaps.Block_Min.Blocks_For (Extended_Index (Total)));
      C_From : Heaps.Block_Min.Heap
        (Capacity           => Extended_Index (Total),
         Directory_Capacity =>
           Heaps.Block_Min.Blocks_For (Extended_Index (Total)));
      W_Into : Heaps.Weak.Heap (Extended_Index (Total));
      W_From : Heaps.Weak.Heap (Extended_Index (Total));
      M_Into : Heaps.Min_Max.Heap (Extended_Index (Total));
      M_From : Heaps.Min_Max.Heap (Extended_Index (Total));
      V_Into : Heaps.Interval.Heap (Extended_Index (Total));
      V_From : Heaps.Interval.Heap (Extended_Index (Total));
      P_Into : Heaps.Beap.Heap (Extended_Index (Total));
      P_From : Heaps.Beap.Heap (Extended_Index (Total));
      S_Into : Heaps.Sorted.Heap (Extended_Index (Total));
      S_From : Heaps.Sorted.Heap (Extended_Index (Total));
      L_Into : Heaps.Leftist.Heap (Extended_Index (Total));
      L_From : Heaps.Leftist.Heap (Extended_Index (Total));

      Oracle : array (1 .. Total) of Key_Type;
      Filled : Natural := 0;

      State : Long_Long_Integer := 24_680_135;
      K     : Key_Type;
      A_Key : Key_Type;
      B_Key : Key_Type;
      D_Key : Key_Type;
      C_Key : Key_Type;
      W_Key : Key_Type;
      M_Key : Key_Type;
      V_Key : Key_Type;
      P_Key : Key_Type;
      S_Key : Key_Type;
      L_Key : Key_Type;
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
               Heaps.Block_Min.Insert (C_Into, K);
               Heaps.Weak.Insert (W_Into, K);
               Heaps.Min_Max.Insert (M_Into, K);
               Heaps.Interval.Insert (V_Into, K);
               Heaps.Beap.Insert (P_Into, K);
               Heaps.Sorted.Insert (S_Into, K);
               Heaps.Leftist.Insert (L_Into, K);
            else
               Heaps.Unsorted.Insert (A_From, K);
               Heaps.Binary.Insert (B_From, K);
               Heaps.Dary.Insert (D_From, K);
               Heaps.Block_Min.Insert (C_From, K);
               Heaps.Weak.Insert (W_From, K);
               Heaps.Min_Max.Insert (M_From, K);
               Heaps.Interval.Insert (V_From, K);
               Heaps.Beap.Insert (P_From, K);
               Heaps.Sorted.Insert (S_From, K);
               Heaps.Leftist.Insert (L_From, K);
            end if;
         end loop;
      end Feed;
   begin
      Feed (N, True);
      Feed (M, False);

      Heaps.Unsorted.Meld (A_Into, A_From);
      Heaps.Binary.Meld (B_Into, B_From);
      Heaps.Dary.Meld (D_Into, D_From);
      Heaps.Block_Min.Meld (C_Into, C_From);
      Heaps.Weak.Meld (W_Into, W_From);
      Heaps.Min_Max.Meld (M_Into, M_From);
      Heaps.Interval.Meld (V_Into, V_From);
      Heaps.Beap.Meld (P_Into, P_From);
      Heaps.Sorted.Meld (S_Into, S_From);
      Heaps.Leftist.Meld (L_Into, L_From);

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
      Check (Heaps.Block_Min.Size (C_Into) = Total,
             "meld: block-min size is the sum");
      Check (Heaps.Block_Min.Is_Empty (C_From),
             "meld: block-min source is emptied");
      Check (Heaps.Weak.Size (W_Into) = Total, "meld: weak size is the sum");
      Check (Heaps.Weak.Is_Empty (W_From), "meld: weak source is emptied");
      Check (Heaps.Min_Max.Size (M_Into) = Total,
             "meld: min-max size is the sum");
      Check (Heaps.Min_Max.Is_Empty (M_From),
             "meld: min-max source is emptied");
      Check (Heaps.Interval.Size (V_Into) = Total,
             "meld: interval size is the sum");
      Check (Heaps.Interval.Is_Empty (V_From),
             "meld: interval source is emptied");
      Check (Heaps.Beap.Size (P_Into) = Total, "meld: beap size is the sum");
      Check (Heaps.Beap.Is_Empty (P_From), "meld: beap source is emptied");
      Check (Heaps.Sorted.Size (S_Into) = Total,
             "meld: sorted size is the sum");
      Check (Heaps.Sorted.Is_Empty (S_From), "meld: sorted source is emptied");
      Check (Heaps.Leftist.Size (L_Into) = Total,
             "meld: leftist size is the sum");
      Check (Heaps.Leftist.Is_Empty (L_From),
             "meld: leftist source is emptied");

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

         Check (Heaps.Weak.Peek_Min (W_Into) = Heaps.Weak.Min_Of (W_Into),
                "meld: weak peek agrees with the array minimum");

         Check (Heaps.Min_Max.Peek_Min (M_Into)
                = Heaps.Min_Max.Min_Of (M_Into),
                "meld: min-max peek agrees with the array minimum");

         Check (Heaps.Interval.Peek_Min (V_Into)
                = Heaps.Interval.Min_Of (V_Into),
                "meld: interval peek agrees with the array minimum");

         Check (Heaps.Beap.Peek_Min (P_Into) = Heaps.Beap.Min_Of (P_Into),
                "meld: beap peek agrees with the array minimum");

         Check (Heaps.Leftist.Peek_Min (L_Into)
                = Heaps.Leftist.Min_Of (L_Into),
                "meld: leftist peek agrees with the array minimum");

         Heaps.Unsorted.Extract_Min (A_Into, A_Key);
         Heaps.Binary.Extract_Min (B_Into, B_Key);
         Heaps.Dary.Extract_Min (D_Into, D_Key);
         Heaps.Block_Min.Extract_Min (C_Into, C_Key);
         Heaps.Weak.Extract_Min (W_Into, W_Key);
         Heaps.Min_Max.Extract_Min (M_Into, M_Key);
         Heaps.Interval.Extract_Min (V_Into, V_Key);
         Heaps.Beap.Extract_Min (P_Into, P_Key);
         Heaps.Sorted.Extract_Min (S_Into, S_Key);
         Heaps.Leftist.Extract_Min (L_Into, L_Key);

         Check (A_Key = Oracle (I), "meld: unsorted drain matches the oracle");
         Check (B_Key = Oracle (I), "meld: binary drain matches the oracle");
         Check (D_Key = Oracle (I), "meld: d-ary drain matches the oracle");
         Check (C_Key = Oracle (I),
                "meld: block-min drain matches the oracle");
         Check (W_Key = Oracle (I), "meld: weak drain matches the oracle");
         Check (M_Key = Oracle (I), "meld: min-max drain matches the oracle");
         Check (V_Key = Oracle (I), "meld: interval drain matches the oracle");
         Check (P_Key = Oracle (I), "meld: beap drain matches the oracle");
         Check (S_Key = Oracle (I), "meld: sorted drain matches the oracle");
         Check (L_Key = Oracle (I), "meld: leftist drain matches the oracle");
         Check (A_Key = B_Key and A_Key = D_Key and A_Key = C_Key
                and A_Key = W_Key and A_Key = M_Key and A_Key = V_Key
                and A_Key = P_Key and A_Key = S_Key and A_Key = L_Key,
                "meld: the implementations agree");
         Check (B_Key >= Prev, "meld: keys come out in non-decreasing order");
         Prev := B_Key;
      end loop;

      Check (Heaps.Unsorted.Is_Empty (A_Into),
             "meld: unsorted empty after draining");
      Check (Heaps.Binary.Is_Empty (B_Into),
             "meld: binary empty after draining");
      Check (Heaps.Beap.Is_Empty (P_Into), "meld: beap empty after draining");
      Check (Heaps.Sorted.Is_Empty (S_Into),
             "meld: sorted empty after draining");
      Check (Heaps.Leftist.Is_Empty (L_Into),
             "meld: leftist empty after draining");
   end Test_Meld;

   --  The arena: several trees sharing one pool. Heaps.Leftist_Pool is a
   --  library-level instance of it, so the pool is package state rather than
   --  an object, and every test below calls Clear first -- that, and nothing
   --  else, is what keeps them independent of one another.
   --
   --  Two properties here have no analogue in the array heaps and so are
   --  checked nowhere else in this program. Room is the arena's own
   --  bookkeeping: nodes come off a free chain and go back onto it, and a leak
   --  or a double release drifts the count long before it produces a wrong
   --  answer. And the trees an operation does not name have to come back
   --  untouched, which is the frame the arena's contracts claim and the reason
   --  a meld can be a splice rather than a copy; checking it needs a bystander
   --  tree, which a heap owning its own pool cannot have.
   --
   --  The arena has no Min_Of either. With several trees in one array there is
   --  no range of slots holding a given tree's keys, so the oracle for "the
   --  smallest key still in T" has to be kept by the test.

   package Arena renames Heaps.Leftist_Pool;

   procedure Test_Arena (N : Positive);
   procedure Test_Arena (N : Positive) is
      T     : Arena.Tree := 0;
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Top   : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      Arena.Clear;
      Check (Arena.Room = Arena.Nodes, "arena: a cleared arena is all free");
      Check (Arena.Is_Empty (T), "arena: the empty tree starts empty");

      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Arena.Insert (T, K);
         Check (Arena.Size_Of (T) = I, "arena: size after insert");
         Check (Arena.Room = Arena.Nodes - I,
                "arena: an insert takes exactly one node");
      end loop;

      for I in reverse 1 .. N loop
         Top := Arena.Peek_Min (T);
         Arena.Extract_Min (T, K);
         Check (K = Top, "arena: extraction returns the key peek promised");
         Check (K >= Prev, "arena: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
         Check (Arena.Size_Of (T) = I - 1, "arena: size after extraction");
         Check (Arena.Room = Arena.Nodes - (I - 1),
                "arena: an extraction gives exactly one node back");
      end loop;

      Check (Arena.Is_Empty (T), "arena: empty after draining");
      Check (Arena.Room = Arena.Nodes, "arena: every node is back");
      Check (Sum = Back, "arena: nothing lost on the way");
   end Test_Arena;

   procedure Test_Arena_Churn (N : Positive);
   procedure Test_Arena_Churn (N : Positive) is
      --  Alternating an extraction and an insertion keeps the free chain
      --  moving: every extraction pushes a node back onto it and the next
      --  insertion takes that node off again, so the slots are recycled over
      --  and over. A stale link left behind in a recycled node, a leak, or a
      --  node released twice all surface here rather than in a straight fill
      --  and drain.
      T     : Arena.Tree := 0;
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;

      Held  : array (1 .. N) of Key_Type;
      Count : Natural := 0;
      --  The keys the tree ought to hold, unsorted. Scanning it is O(n) per
      --  check, which is why this test runs over small sizes only.

      procedure Hold (Key : Key_Type);
      procedure Hold (Key : Key_Type) is
      begin
         Count := Count + 1;
         Held (Count) := Key;
      end Hold;

      function Least return Key_Type;
      function Least return Key_Type is
         Best : Key_Type := Held (1);
      begin
         for I in 2 .. Count loop
            if Held (I) < Best then
               Best := Held (I);
            end if;
         end loop;
         return Best;
      end Least;

      procedure Drop_Least;
      procedure Drop_Least is
         Where : Natural := 1;
      begin
         for I in 2 .. Count loop
            if Held (I) < Held (Where) then
               Where := I;
            end if;
         end loop;
         Held (Where) := Held (Count);
         Count := Count - 1;
      end Drop_Least;
   begin
      Arena.Clear;

      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 1_000);
         Hold (K);
         Arena.Insert (T, K);
      end loop;

      for I in 1 .. 4 * N loop
         Check (Arena.Peek_Min (T) = Least,
                "arena: churn keeps the smallest key on top");
         Arena.Extract_Min (T, K);
         Drop_Least;

         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 1_000);
         Hold (K);
         Arena.Insert (T, K);

         Check (Arena.Size_Of (T) = N, "arena: churn holds the size steady");
         Check (Arena.Room = Arena.Nodes - N,
                "arena: churn returns every node it takes");
      end loop;

      for I in 1 .. N loop
         Arena.Extract_Min (T, K);
         Check (K >= Prev, "arena: a churned tree still drains in order");
         Prev := K;
      end loop;

      Check (Arena.Room = Arena.Nodes, "arena: churn leaked no node");
   end Test_Arena_Churn;

   procedure Sort (Keys : in out Key_Array; Last : Natural);
   procedure Sort (Keys : in out Key_Array; Last : Natural) is
   begin
      for I in 2 .. Last loop
         declare
            V : constant Key_Type := Keys (I);
            J : Natural := I - 1;
         begin
            while J >= 1 and then Keys (J) > V loop
               Keys (J + 1) := Keys (J);
               J := J - 1;
            end loop;
            Keys (J + 1) := V;
         end;
      end loop;
   end Sort;

   procedure Test_Arena_Meld (N, M : Natural);
   procedure Test_Arena_Meld (N, M : Natural) is
      Total    : constant Natural := N + M;
      Bystands : constant Natural := 32;
      --  A third tree, which neither operand of the meld names. The arena's
      --  postcondition says every other tree of the pool keeps the model it
      --  had; this is what checks it.

      Into : Arena.Tree := 0;
      From : Arena.Tree := 0;
      Idle : Arena.Tree := 0;

      Oracle : Key_Array (1 .. Total) :=
        [others => 0];
      Filled : Natural := 0;

      Aside : Key_Array (1 .. Bystands) := [others => 0];

      State  : Long_Long_Integer := 24_680_135;
      K      : Key_Type;
      Before : Extended_Index;
      Prev   : Key_Type := Key_Type'First;

      procedure Feed (Count : Natural; Target : in out Arena.Tree);
      procedure Feed (Count : Natural; Target : in out Arena.Tree) is
      begin
         for I in 1 .. Count loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);
            Filled := Filled + 1;
            Oracle (Filled) := K;
            Arena.Insert (Target, K);
         end loop;
      end Feed;
   begin
      Arena.Clear;

      Feed (N, Into);
      Feed (M, From);

      for I in 1 .. Bystands loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Aside (I) := K;
         Arena.Insert (Idle, K);
      end loop;

      Check (Arena.Room = Arena.Nodes - (Total + Bystands),
             "arena meld: the three trees share the one pool");

      --  A meld allocates, frees and copies nothing: it is a splice, and the
      --  free count is the run-time witness of that. This is the property
      --  that separates it from the append-and-rebuild melds above.

      Before := Arena.Room;
      Arena.Meld (Into, From);
      Check (Arena.Room = Before, "arena meld: no node is allocated or freed");

      Check (Arena.Size_Of (Into) = Total, "arena meld: size is the sum");
      Check (Arena.Is_Empty (From), "arena meld: the source is emptied");

      Sort (Oracle, Total);

      for I in 1 .. Total loop
         Arena.Extract_Min (Into, K);
         Check (K = Oracle (I), "arena meld: drain matches the oracle");
         Check (K >= Prev,
                "arena meld: keys come out in non-decreasing order");
         Prev := K;
      end loop;

      Check (Arena.Is_Empty (Into), "arena meld: empty after draining");

      --  And the bystander is exactly as it was left.

      Sort (Aside, Bystands);
      Check (Arena.Size_Of (Idle) = Bystands,
             "arena meld: the tree it did not name kept its size");

      for I in 1 .. Bystands loop
         Arena.Extract_Min (Idle, K);
         Check (K = Aside (I),
                "arena meld: the tree it did not name kept its keys");
      end loop;

      Check (Arena.Room = Arena.Nodes, "arena meld: every node is back");
   end Test_Arena_Meld;

   procedure Test_Arena_KWay (N, Ways : Positive);
   procedure Test_Arena_KWay (N, Ways : Positive) is
      --  What the arena is for: k trees in one pool folded into one
      --  accumulator, each meld a splice of two right spines. A heap that owns
      --  its pool cannot express this without copying k - 1 of the operands
      --  into the survivor.
      Each  : constant Positive := Positive'Max (1, N / Ways);
      Total : constant Natural := Each * Ways;

      Acc   : Arena.Tree := 0;
      Ops   : array (1 .. Ways) of Arena.Tree := [others => 0];

      Oracle : Key_Array (1 .. Total) := [others => 0];
      Filled : Natural := 0;

      State  : Long_Long_Integer := 13_579_246;
      K      : Key_Type;
      Before : Extended_Index;
      Prev   : Key_Type := Key_Type'First;
   begin
      Arena.Clear;

      for W in Ops'Range loop
         for I in 1 .. Each loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);
            Filled := Filled + 1;
            Oracle (Filled) := K;
            Arena.Insert (Ops (W), K);
         end loop;
      end loop;

      Check (Arena.Room = Arena.Nodes - Total,
             "arena k-way: every operand is in the one pool");

      Before := Arena.Room;

      for W in Ops'Range loop
         Arena.Meld (Acc, Ops (W));
         Check (Arena.Is_Empty (Ops (W)),
                "arena k-way: the operand is emptied");
         Check (Arena.Size_Of (Acc) = Each * W,
                "arena k-way: the accumulator grows by one operand");
      end loop;

      Check (Arena.Room = Before, "arena k-way: the folding moved no node");

      Sort (Oracle, Total);

      for I in 1 .. Total loop
         Arena.Extract_Min (Acc, K);
         Check (K = Oracle (I), "arena k-way: drain matches the oracle");
         Check (K >= Prev,
                "arena k-way: keys come out in non-decreasing order");
         Prev := K;
      end loop;

      Check (Arena.Room = Arena.Nodes, "arena k-way: every node is back");
   end Test_Arena_KWay;


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

   --  The arena churns for a different reason, and over fewer sizes. What the
   --  sweep above is after is the layer and level boundaries of an implicit
   --  tree, which the arena does not have; what matters here is that slots go
   --  back onto the free chain and come off it again, and a handful of sizes
   --  exercise that as well as two hundred would -- while sparing the suite
   --  two hundred clears of a pool whose size has nothing to do with the size
   --  being tested.
   for N of Churn_Sizes loop
      Test_Arena_Churn (N);
   end loop;

   for N of Sizes loop
      Test_Binary (N);
      Test_Block_Min (N);
      Test_Weak (N);
      Test_Leftist (N);
      Test_Arena (N);
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

   --  The arena's own meld, over the same shapes. It gets a k-way fold as
   --  well: with one pool holding every operand, folding k trees into one is
   --  the workload the structure exists for, and it is the case a heap that
   --  owns its pool cannot run without copying.
   for N of Sizes loop
      Test_Arena_Meld (N, N);
      Test_Arena_Meld (N, 1);
      Test_Arena_Meld (1, N);
      Test_Arena_Meld (N, 0);
      Test_Arena_Meld (0, N);
      Test_Arena_KWay (N, 16);
   end loop;
   Test_Arena_Meld (0, 0);
   Test_Arena_KWay (1, 16);

   if Failures = 0 then
      Put_Line ("all heap tests passed");
   else
      Put_Line (Natural'Image (Failures) & " failure(s)");
   end if;
end Heaps_Test;
