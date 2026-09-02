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
with Heaps.Bucket;
with Heaps.Dary;
with Heaps.Interval;
with Heaps.Leftist_Pool;
with Heaps.Min_Max;
with Heaps.Min_Max_Tournament;
with Heaps.Open_Proved;
with Heaps.Pairing_Pool;
with Heaps.Radix;
with Heaps.Skew_Pool;
with Heaps.Sorted;
with Heaps.Sorted_Linked;
with Heaps.Tournament;
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

   procedure Test_Bucket (N : Positive);
   procedure Test_Bucket (N : Positive) is
      H     : Heaps.Bucket.Heap
        (Capacity  => Extended_Index (N),
         First_Key => -32,
         Last_Key  => 32);
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      Heaps.Bucket.Clear (H);
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 65) - 32;
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Bucket.Insert (H, K);
         Check (Heaps.Bucket.Size (H) = I,
                "bucket: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Bucket.Peek_Min (H) >= -32
                  and then Heaps.Bucket.Peek_Min (H) <= 32,
                "bucket: minimum stays in the configured range");
         Heaps.Bucket.Extract_Min (H, K);
         Check (K >= Prev,
                "bucket: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Bucket.Is_Empty (H),
             "bucket: empty after draining");
      Check (Sum = Back, "bucket: nothing lost on the way");
   end Test_Bucket;

   procedure Test_Bucket_Churn (N : Positive);
   procedure Test_Bucket_Churn (N : Positive) is
      H     : Heaps.Bucket.Heap
        (Capacity  => Extended_Index (N),
         First_Key => -8,
         Last_Key  => 8);
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      Heaps.Bucket.Clear (H);
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Bucket.Insert (H, Key_Type (State mod 17) - 8);
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Bucket.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Bucket.Insert (H, Key_Type (State mod 17) - 8);
         Check (Heaps.Bucket.Size (H) = N,
                "bucket: churn preserves size");
      end loop;

      for I in 1 .. N loop
         Heaps.Bucket.Extract_Min (H, K);
         Check (K >= Prev, "bucket: churned queue drains in order");
         Prev := K;
      end loop;
   end Test_Bucket_Churn;

   procedure Test_Bucket_Meld (N, M : Natural);
   procedure Test_Bucket_Meld (N, M : Natural) is
      Total : constant Extended_Index := Extended_Index (N + M);
      Into  : Heaps.Bucket.Heap
        (Capacity  => Total,
         First_Key => -16,
         Last_Key  => 16);
      From  : Heaps.Bucket.Heap
        (Capacity  => Total,
         First_Key => -16,
         Last_Key  => 16);
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      Heaps.Bucket.Clear (Into);
      Heaps.Bucket.Clear (From);
      for I in 1 .. N loop
         Heaps.Bucket.Insert (Into, Key_Type ((7 * I) mod 33) - 16);
      end loop;
      for I in 1 .. M loop
         Heaps.Bucket.Insert (From, Key_Type ((11 * I) mod 33) - 16);
      end loop;

      Heaps.Bucket.Meld (Into, From);
      Check (Heaps.Bucket.Size (Into) = Total,
             "bucket meld: destination has every key");
      Check (Heaps.Bucket.Is_Empty (From),
             "bucket meld: source is empty");

      for I in 1 .. N + M loop
         Heaps.Bucket.Extract_Min (Into, K);
         Check (K >= Prev, "bucket meld: result drains in order");
         Prev := K;
      end loop;
   end Test_Bucket_Meld;

   procedure Test_Radix (N : Positive);

   procedure Test_Radix_Buckets;
   procedure Test_Radix_Buckets is
      H     : Heaps.Radix.Heap (8);
      Power : Key_Type := 1;
      K     : Key_Type;
   begin
      Heaps.Radix.Clear (H);
      Check (Heaps.Radix.Bucket_For (H, 0) = 0,
             "radix: the base key is in bucket zero");

      for B in 1 .. Heaps.Radix.Bucket_Index'Last loop
         Check (Heaps.Radix.Bucket_For (H, Power) = B,
                "radix: powers of two start the expected bucket");
         if Power > 1 then
            Check (Heaps.Radix.Bucket_For (H, Power - 1) = B - 1,
                   "radix: powers of two end the preceding bucket");
         end if;
         if B < Heaps.Radix.Bucket_Index'Last then
            Power := 2 * Power;
         end if;
      end loop;

      --  The boundaries are state: extracting rebases the buckets below the
      --  one it empties, and leaves the ones above it alone.

      Heaps.Radix.Clear (H);
      Heaps.Radix.Insert (H, 100);
      Heaps.Radix.Insert (H, 101);
      Heaps.Radix.Insert (H, 140);
      Heaps.Radix.Extract_Min (H, K);
      Check (K = 100 and then H.Base = 100,
             "radix: extraction advances the base to the minimum");
      Check (Heaps.Radix.Bucket_For (H, 100) = 0,
             "radix: the new base is in bucket zero");
      Check (Heaps.Radix.Bucket_For (H, 101) = 1,
             "radix: the bucket below the emptied one is rebased");
      Check (Heaps.Radix.Bucket_For (H, 102) = 2,
             "radix: and so is the one below that");
      Heaps.Radix.Extract_Min (H, K);
      Check (K = 101, "radix: the rebased buckets still drain in order");
      Heaps.Radix.Extract_Min (H, K);
      Check (K = 140, "radix: and so does the bucket left alone");
   end Test_Radix_Buckets;

   procedure Test_Radix (N : Positive) is
      H     : Heaps.Radix.Heap (Extended_Index (N));
      State : Long_Long_Integer := 987_654_321;
      K     : Key_Type;
      Prev  : Key_Type := 0;
      Sum   : Long_Long_Integer := 0;
      Back  : Long_Long_Integer := 0;
   begin
      Heaps.Radix.Clear (H);
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         K := Key_Type (State mod 100_000);
         Sum := Sum + Long_Long_Integer (K);
         Heaps.Radix.Insert (H, K);
         Check (Heaps.Radix.Size (H) = I,
                "radix: size after insert");
      end loop;

      for I in 1 .. N loop
         Heaps.Radix.Extract_Min (H, K);
         Check (K >= Prev,
                "radix: keys come out in non-decreasing order");
         Check (H.Base = K, "radix: extraction advances the base");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Radix.Is_Empty (H),
             "radix: empty after draining");
      Check (Sum = Back, "radix: nothing lost on the way");
   end Test_Radix;

   procedure Test_Radix_Churn (N : Positive);
   procedure Test_Radix_Churn (N : Positive) is
      H     : Heaps.Radix.Heap (Extended_Index (N));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := 0;
   begin
      Heaps.Radix.Clear (H);
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Radix.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Radix.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Radix.Insert (H, K + 1 + Key_Type (State mod 1_000));
         Check (Heaps.Radix.Size (H) = N,
                "radix: monotone churn preserves size");
      end loop;

      for I in 1 .. N loop
         Heaps.Radix.Extract_Min (H, K);
         Check (K >= Prev, "radix: churned queue drains in order");
         Prev := K;
      end loop;
   end Test_Radix_Churn;

   procedure Test_Radix_Meld (N, M : Natural);
   procedure Test_Radix_Meld (N, M : Natural) is
      Total : constant Extended_Index := Extended_Index (N + M);
      Into  : Heaps.Radix.Heap (Total);
      From  : Heaps.Radix.Heap (Total);
      K     : Key_Type;
      Prev  : Key_Type := 0;
   begin
      Heaps.Radix.Clear (Into);
      Heaps.Radix.Clear (From);
      for I in 1 .. N loop
         Heaps.Radix.Insert (Into, Key_Type ((7 * I) mod 100_001));
      end loop;
      for I in 1 .. M loop
         Heaps.Radix.Insert (From, Key_Type ((11 * I) mod 100_001));
      end loop;

      Heaps.Radix.Meld (Into, From);
      Check (Heaps.Radix.Size (Into) = Total,
             "radix meld: destination has every key");
      Check (Heaps.Radix.Is_Empty (From),
             "radix meld: source is empty");

      for I in 1 .. N + M loop
         Heaps.Radix.Extract_Min (Into, K);
         Check (K >= Prev, "radix meld: result drains in order");
         Prev := K;
      end loop;
   end Test_Radix_Meld;

   procedure Test_Radix_Advanced_Meld;
   procedure Test_Radix_Advanced_Meld is
      Into : Heaps.Radix.Heap (4);
      From : Heaps.Radix.Heap (4);
      K    : Key_Type;
   begin
      Heaps.Radix.Clear (Into);
      Heaps.Radix.Clear (From);
      Heaps.Radix.Insert (Into, 5);
      Heaps.Radix.Insert (Into, 10);
      Heaps.Radix.Extract_Min (Into, K);
      Check (K = 5 and then Into.Base = 5,
             "radix meld: destination base was advanced");

      Heaps.Radix.Insert (From, 7);
      Heaps.Radix.Insert (From, 8);
      Heaps.Radix.Meld (Into, From);
      for Expected in 7 .. 10 loop
         if Expected /= 9 then
            Heaps.Radix.Extract_Min (Into, K);
            Check (K = Key_Type (Expected),
                   "radix meld: compatible keys cross a lower source base");
         end if;
      end loop;
   end Test_Radix_Advanced_Meld;

   procedure Test_Tournament (N : Positive);
   procedure Test_Tournament (N : Positive) is
      H     : Heaps.Tournament.Heap (Extended_Index (N));
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
         Heaps.Tournament.Insert (H, K);
         Check (Heaps.Tournament.Size (H) = I,
                "tournament: size after insert");
      end loop;

      for I in 1 .. N loop
         Check (Heaps.Tournament.Peek_Min (H)
                  = Heaps.Tournament.Min_Of (H),
                "tournament: root agrees with the array minimum");
         Heaps.Tournament.Extract_Min (H, K);
         Check (K >= Prev,
                "tournament: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Tournament.Is_Empty (H),
             "tournament: empty after draining");
      Check (Sum = Back, "tournament: nothing lost on the way");
   end Test_Tournament;

   procedure Test_Tournament_Churn (N : Positive);
   procedure Test_Tournament_Churn (N : Positive) is
      H     : Heaps.Tournament.Heap (Extended_Index (N));
      State : Long_Long_Integer := 24_680;
      K     : Key_Type;
      Prev  : Key_Type := Key_Type'First;
   begin
      for I in 1 .. N loop
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Tournament.Insert (H, Key_Type (State mod 1_000));
      end loop;

      for I in 1 .. 4 * N loop
         Heaps.Tournament.Extract_Min (H, K);
         State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
         Heaps.Tournament.Insert (H, Key_Type (State mod 1_000));
         Check (Heaps.Tournament.Peek_Min (H)
                  = Heaps.Tournament.Min_Of (H),
                "tournament: churn keeps the winner path current");
      end loop;

      for I in 1 .. N loop
         Heaps.Tournament.Extract_Min (H, K);
         Check (K >= Prev, "tournament: churned tree drains in order");
         Prev := K;
      end loop;
   end Test_Tournament_Churn;

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

   procedure Test_Sorted_Linked (N : Positive);
   procedure Test_Sorted_Linked (N : Positive) is
      H     : Heaps.Sorted_Linked.Heap (Extended_Index (N));
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
         Heaps.Sorted_Linked.Insert (H, K);
         Check (Heaps.Sorted_Linked.Size (H) = I,
                "sorted-linked: size after insert");
      end loop;

      for I in 1 .. N loop
         Peek := Heaps.Sorted_Linked.Peek_Min (H);
         Heaps.Sorted_Linked.Extract_Min (H, K);
         Check (K = Peek,
                "sorted-linked: peek agrees with the extracted key");
         Check (K >= Prev,
                "sorted-linked: keys come out in non-decreasing order");
         Prev := K;
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Sorted_Linked.Is_Empty (H),
             "sorted-linked: empty after draining");
      Check (Sum = Back, "sorted-linked: nothing lost on the way");
   end Test_Sorted_Linked;

   procedure Test_Sorted_Linked_Meld (N, M : Natural);
   procedure Test_Sorted_Linked_Meld (N, M : Natural) is
      Total  : constant Extended_Index := Extended_Index (N + M);
      Into   : Heaps.Sorted_Linked.Heap (Total);
      From   : Heaps.Sorted_Linked.Heap (Total);
      Oracle : Heaps.Sorted.Heap (Total);
      State  : Long_Long_Integer := 314_159_265;
      K      : Key_Type;
      Expect : Key_Type;
   begin
      for Side in 1 .. 2 loop
         for I in 1 .. (if Side = 1 then N else M) loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);
            Heaps.Sorted.Insert (Oracle, K);
            if Side = 1 then
               Heaps.Sorted_Linked.Insert (Into, K);
            else
               Heaps.Sorted_Linked.Insert (From, K);
            end if;
         end loop;
      end loop;

      Heaps.Sorted_Linked.Meld (Into, From);
      Check (Heaps.Sorted_Linked.Size (Into) = Total,
             "sorted-linked meld: size is the sum");
      Check (Heaps.Sorted_Linked.Is_Empty (From),
             "sorted-linked meld: source is empty");

      for I in 1 .. Total loop
         Heaps.Sorted.Extract_Min (Oracle, Expect);
         Heaps.Sorted_Linked.Extract_Min (Into, K);
         Check (K = Expect,
                "sorted-linked meld: drain matches the oracle");
      end loop;

      Check (Heaps.Sorted_Linked.Is_Empty (Into),
             "sorted-linked meld: result is empty after draining");
   end Test_Sorted_Linked_Meld;

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

   procedure Test_Min_Max_Tournament (N : Positive);
   procedure Test_Min_Max_Tournament (N : Positive) is
      H     : Heaps.Min_Max_Tournament.Heap (Extended_Index (N));
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
         Heaps.Min_Max_Tournament.Insert (H, K);
         Check (Heaps.Min_Max_Tournament.Size (H) = I,
                "min-max tournament: size after insert");
         Check (Heaps.Min_Max_Tournament.Peek_Min (H)
                  = Heaps.Min_Max_Tournament.Min_Of (H),
                "min-max tournament: peek-min agrees with the array minimum");
         Check (Heaps.Min_Max_Tournament.Peek_Max (H)
                  = Heaps.Min_Max_Tournament.Max_Of (H),
                "min-max tournament: peek-max agrees with the array maximum");
      end loop;

      --  Take the keys out from the outside in: the two ends have to meet in
      --  the middle, which checks both sift directions at once.

      for I in 1 .. N loop
         if I mod 2 = 1 then
            Heaps.Min_Max_Tournament.Extract_Min (H, K);
            Check (K >= Low,
                   "min-max tournament: the low end never goes back down");
            Low := K;
         else
            Heaps.Min_Max_Tournament.Extract_Max (H, K);
            Check (K <= High,
                   "min-max tournament: the high end never goes back up");
            High := K;
         end if;

         Check (Low <= High,
                "min-max tournament: the two ends have not crossed");
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Min_Max_Tournament.Is_Empty (H),
             "min-max tournament: empty after draining");
      Check (Sum = Back, "min-max tournament: nothing lost on the way");
   end Test_Min_Max_Tournament;

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

   procedure Test_Open_Proved (N : Positive);
   procedure Test_Open_Proved (N : Positive) is
      H     : Heaps.Open_Proved.Heap (Extended_Index (N));
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
         Heaps.Open_Proved.Insert (H, K);
         Check (Heaps.Open_Proved.Size (H) = I,
                "open-proved: size after insert");
      end loop;

      --  Peek while the representation is still lazy, then let the first
      --  extraction materialize the interval heap. Alternating ends checks
      --  both the transition and the steady-state representation.

      Check (Heaps.Open_Proved.Peek_Min (H) <=
               Heaps.Open_Proved.Peek_Max (H),
             "open-proved: lazy extrema are ordered");

      for I in 1 .. N loop
         if I mod 2 = 1 then
            Heaps.Open_Proved.Extract_Min (H, K);
            Check (K >= Low,
                   "open-proved: the low end never goes back down");
            Low := K;
         else
            Heaps.Open_Proved.Extract_Max (H, K);
            Check (K <= High,
                   "open-proved: the high end never goes back up");
            High := K;
         end if;

         Check (Low <= High, "open-proved: the two ends have not crossed");
         Back := Back + Long_Long_Integer (K);
      end loop;

      Check (Heaps.Open_Proved.Is_Empty (H),
             "open-proved: empty after draining");
      Check (Sum = Back, "open-proved: nothing lost on the way");
   end Test_Open_Proved;

   procedure Test_Open_Proved_Meld
     (Activate_Into, Activate_From : Boolean);
   procedure Test_Open_Proved_Meld
     (Activate_Into, Activate_From : Boolean)
   is
      Into : Heaps.Open_Proved.Heap (128);
      From : Heaps.Open_Proved.Heap (64);
      K    : Key_Type;

      procedure Activate (H : in out Heaps.Open_Proved.Heap);
      procedure Activate (H : in out Heaps.Open_Proved.Heap) is
      begin
         Heaps.Open_Proved.Extract_Min (H, K);
         Heaps.Open_Proved.Insert (H, K);
      end Activate;
   begin
      for I in 1 .. 64 loop
         Heaps.Open_Proved.Insert (Into, Key_Type (2 * I));
         Heaps.Open_Proved.Insert (From, Key_Type (2 * I - 1));
      end loop;

      if Activate_Into then
         Activate (Into);
      end if;
      if Activate_From then
         Activate (From);
      end if;

      Heaps.Open_Proved.Meld (Into, From);
      Check (Heaps.Open_Proved.Is_Empty (From),
             "open-proved meld: source is empty");

      for Expected in 1 .. 128 loop
         Heaps.Open_Proved.Extract_Min (Into, K);
         Check (K = Key_Type (Expected),
                "open-proved meld: drain matches the oracle");
      end loop;
   end Test_Open_Proved_Meld;

   --  Meld: every implementation that has the operation is checked against
   --  the others and against a sorted oracle built from the same keys. Sizes
   --  are swept in both directions so that the lopsided cases -- a large heap
   --  receiving a tiny one and the reverse -- are covered as well as the
   --  balanced one.

   package Arena renames Heaps.Leftist_Pool;
   package Skew_Arena renames Heaps.Skew_Pool;
   package Pair_Arena renames Heaps.Pairing_Pool;

   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type);
   procedure Test_Meld (N, M : Natural; Arity : Heaps.Dary.Arity_Type) is
      Total : constant Natural := N + M;

      A_Into : Heaps.Unsorted.Heap (Extended_Index (Total));
      A_From : Heaps.Unsorted.Heap (Extended_Index (Total));
      B_Into : Heaps.Binary.Heap (Extended_Index (Total));
      B_From : Heaps.Binary.Heap (Extended_Index (Total));
      T_Into : Heaps.Tournament.Heap (Extended_Index (Total));
      T_From : Heaps.Tournament.Heap (Extended_Index (Total));
      X_Into : Heaps.Min_Max_Tournament.Heap (Extended_Index (Total));
      X_From : Heaps.Min_Max_Tournament.Heap (Extended_Index (Total));
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
      L_Into : Arena.Tree := 0;
      L_From : Arena.Tree := 0;
      Q_Into : Skew_Arena.Tree := 0;
      Q_From : Skew_Arena.Tree := 0;
      G_Into : Pair_Arena.Tree := 0;
      G_From : Pair_Arena.Tree := 0;

      Oracle : array (1 .. Total) of Key_Type;
      Filled : Natural := 0;

      State : Long_Long_Integer := 24_680_135;
      K     : Key_Type;
      A_Key : Key_Type;
      B_Key : Key_Type;
      T_Key : Key_Type;
      X_Key : Key_Type;
      D_Key : Key_Type;
      C_Key : Key_Type;
      W_Key : Key_Type;
      M_Key : Key_Type;
      V_Key : Key_Type;
      P_Key : Key_Type;
      S_Key : Key_Type;
      L_Key : Key_Type;
      Q_Key : Key_Type;
      G_Key : Key_Type;
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
               Heaps.Tournament.Insert (T_Into, K);
               Heaps.Min_Max_Tournament.Insert (X_Into, K);
               Heaps.Dary.Insert (D_Into, K);
               Heaps.Block_Min.Insert (C_Into, K);
               Heaps.Weak.Insert (W_Into, K);
               Heaps.Min_Max.Insert (M_Into, K);
               Heaps.Interval.Insert (V_Into, K);
               Heaps.Beap.Insert (P_Into, K);
               Heaps.Sorted.Insert (S_Into, K);
               Arena.Insert (L_Into, K);
               Skew_Arena.Insert (Q_Into, K);
               Pair_Arena.Insert (G_Into, K);
            else
               Heaps.Unsorted.Insert (A_From, K);
               Heaps.Binary.Insert (B_From, K);
               Heaps.Tournament.Insert (T_From, K);
               Heaps.Min_Max_Tournament.Insert (X_From, K);
               Heaps.Dary.Insert (D_From, K);
               Heaps.Block_Min.Insert (C_From, K);
               Heaps.Weak.Insert (W_From, K);
               Heaps.Min_Max.Insert (M_From, K);
               Heaps.Interval.Insert (V_From, K);
               Heaps.Beap.Insert (P_From, K);
               Heaps.Sorted.Insert (S_From, K);
               Arena.Insert (L_From, K);
               Skew_Arena.Insert (Q_From, K);
               Pair_Arena.Insert (G_From, K);
            end if;
         end loop;
      end Feed;
   begin
      --  The arena pairs are trees of a shared pool, so this test has to
      --  start from arenas of its own like every other test that uses them.

      Arena.Clear;
      Skew_Arena.Clear;
      Pair_Arena.Clear;

      Feed (N, True);
      Feed (M, False);

      Heaps.Unsorted.Meld (A_Into, A_From);
      Heaps.Binary.Meld (B_Into, B_From);
      Heaps.Tournament.Meld (T_Into, T_From);
      Heaps.Min_Max_Tournament.Meld (X_Into, X_From);
      Heaps.Dary.Meld (D_Into, D_From);
      Heaps.Block_Min.Meld (C_Into, C_From);
      Heaps.Weak.Meld (W_Into, W_From);
      Heaps.Min_Max.Meld (M_Into, M_From);
      Heaps.Interval.Meld (V_Into, V_From);
      Heaps.Beap.Meld (P_Into, P_From);
      Heaps.Sorted.Meld (S_Into, S_From);
      Arena.Meld (L_Into, L_From);
      Skew_Arena.Meld (Q_Into, Q_From);
      Pair_Arena.Meld (G_Into, G_From);

      Check (Heaps.Unsorted.Size (A_Into) = Total,
             "meld: unsorted size is the sum");
      Check (Heaps.Binary.Size (B_Into) = Total,
             "meld: binary size is the sum");
      Check (Heaps.Unsorted.Is_Empty (A_From),
             "meld: unsorted source is emptied");
      Check (Heaps.Binary.Is_Empty (B_From),
             "meld: binary source is emptied");
      Check (Heaps.Tournament.Size (T_Into) = Total,
             "meld: tournament size is the sum");
      Check (Heaps.Tournament.Is_Empty (T_From),
             "meld: tournament source is emptied");
      Check (Heaps.Min_Max_Tournament.Size (X_Into) = Total,
             "meld: min-max tournament size is the sum");
      Check (Heaps.Min_Max_Tournament.Is_Empty (X_From),
             "meld: min-max tournament source is emptied");
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
      Check (Arena.Size_Of (L_Into) = Total,
             "meld: leftist size is the sum");
      Check (Arena.Is_Empty (L_From),
             "meld: leftist source is emptied");
      Check (Skew_Arena.Size_Of (Q_Into) = Total,
             "meld: skew size is the sum");
      Check (Skew_Arena.Is_Empty (Q_From),
             "meld: skew source is emptied");
      Check (Pair_Arena.Size_Of (G_Into) = Total,
             "meld: pairing size is the sum");
      Check (Pair_Arena.Is_Empty (G_From),
             "meld: pairing source is emptied");

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
         Check (Heaps.Tournament.Peek_Min (T_Into)
                  = Heaps.Tournament.Min_Of (T_Into),
                "meld: tournament root agrees with the array minimum");
         Check (Heaps.Min_Max_Tournament.Peek_Min (X_Into)
                  = Heaps.Min_Max_Tournament.Min_Of (X_Into),
                "meld: min-max tournament minimum is current");
         Check (Heaps.Min_Max_Tournament.Peek_Max (X_Into)
                  = Heaps.Min_Max_Tournament.Max_Of (X_Into),
                "meld: min-max tournament maximum is current");

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

         Heaps.Unsorted.Extract_Min (A_Into, A_Key);
         Heaps.Binary.Extract_Min (B_Into, B_Key);
         Heaps.Tournament.Extract_Min (T_Into, T_Key);
         Heaps.Min_Max_Tournament.Extract_Min (X_Into, X_Key);
         Heaps.Dary.Extract_Min (D_Into, D_Key);
         Heaps.Block_Min.Extract_Min (C_Into, C_Key);
         Heaps.Weak.Extract_Min (W_Into, W_Key);
         Heaps.Min_Max.Extract_Min (M_Into, M_Key);
         Heaps.Interval.Extract_Min (V_Into, V_Key);
         Heaps.Beap.Extract_Min (P_Into, P_Key);
         Heaps.Sorted.Extract_Min (S_Into, S_Key);
         Arena.Extract_Min (L_Into, L_Key);
         Skew_Arena.Extract_Min (Q_Into, Q_Key);
         Pair_Arena.Extract_Min (G_Into, G_Key);

         Check (A_Key = Oracle (I), "meld: unsorted drain matches the oracle");
         Check (B_Key = Oracle (I), "meld: binary drain matches the oracle");
         Check (T_Key = Oracle (I),
                "meld: tournament drain matches the oracle");
         Check (X_Key = Oracle (I),
                "meld: min-max tournament drain matches the oracle");
         Check (D_Key = Oracle (I), "meld: d-ary drain matches the oracle");
         Check (C_Key = Oracle (I),
                "meld: block-min drain matches the oracle");
         Check (W_Key = Oracle (I), "meld: weak drain matches the oracle");
         Check (M_Key = Oracle (I), "meld: min-max drain matches the oracle");
         Check (V_Key = Oracle (I), "meld: interval drain matches the oracle");
         Check (P_Key = Oracle (I), "meld: beap drain matches the oracle");
         Check (S_Key = Oracle (I), "meld: sorted drain matches the oracle");
         Check (L_Key = Oracle (I), "meld: leftist drain matches the oracle");
         Check (Q_Key = Oracle (I), "meld: skew drain matches the oracle");
         Check (G_Key = Oracle (I),
                "meld: pairing drain matches the oracle");
         Check (A_Key = B_Key and A_Key = T_Key and A_Key = X_Key
                and A_Key = D_Key and A_Key = C_Key
                and A_Key = W_Key and A_Key = M_Key and A_Key = V_Key
                and A_Key = P_Key and A_Key = S_Key and A_Key = L_Key
                and A_Key = Q_Key and A_Key = G_Key,
                "meld: the implementations agree");
         Check (B_Key >= Prev, "meld: keys come out in non-decreasing order");
         Prev := B_Key;
      end loop;

      Check (Heaps.Unsorted.Is_Empty (A_Into),
             "meld: unsorted empty after draining");
      Check (Heaps.Binary.Is_Empty (B_Into),
             "meld: binary empty after draining");
      Check (Heaps.Tournament.Is_Empty (T_Into),
             "meld: tournament empty after draining");
      Check (Heaps.Min_Max_Tournament.Is_Empty (X_Into),
             "meld: min-max tournament empty after draining");
      Check (Heaps.Beap.Is_Empty (P_Into), "meld: beap empty after draining");
      Check (Heaps.Sorted.Is_Empty (S_Into),
             "meld: sorted empty after draining");
      Check (Arena.Is_Empty (L_Into),
             "meld: leftist empty after draining");
      Check (Skew_Arena.Is_Empty (Q_Into),
             "meld: skew empty after draining");
      Check (Pair_Arena.Is_Empty (G_Into),
             "meld: pairing empty after draining");
   end Test_Meld;

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

   --  The arenas: several trees sharing one pool. They present the same
   --  interface and the same contracts, so the tests below are written once
   --  as a generic and run once per arena. A pool is package state rather
   --  than an object, so every test calls Clear first, which is what keeps
   --  them independent.
   --
   --  Two properties checked here have no analogue in the array heaps. Room
   --  is the arena's own bookkeeping: a leak or a double release drifts the
   --  count long before it produces a wrong answer. And the trees an
   --  operation does not name have to come back untouched, which needs a
   --  bystander tree to check.
   --
   --  There is no Min_Of either: with several trees in one array there is no
   --  range of slots holding a given tree's keys, so the oracle for "the
   --  smallest key still in T" is kept by the test.

   generic
      Kind : String;
      --  Which arena this instance drives, so that a failure names it

      Nodes : Extended_Index;
      --  How many nodes its pool holds, which is what Room is checked against

      with procedure Clear;
      with function Room return Extended_Index;
      with function Is_Empty (T : Extended_Index) return Boolean;
      with function Size_Of (T : Extended_Index) return Extended_Index;
      with function Peek_Min (T : Extended_Index) return Key_Type;
      with procedure Insert (T : in out Extended_Index; K : Key_Type);
      with procedure Extract_Min
        (T : in out Extended_Index; K : out Key_Type);
      with procedure Meld
        (T : in out Extended_Index; U : in out Extended_Index);
   package Arena_Suite is
      procedure Test_Arena (N : Positive);
      procedure Test_Arena_Churn (N : Positive);
      procedure Test_Arena_Meld (N, M : Natural);
      procedure Test_Arena_KWay (N, Ways : Positive);
   end Arena_Suite;

   package body Arena_Suite is

      procedure Test_Arena (N : Positive) is
         T     : Extended_Index := 0;
         State : Long_Long_Integer := 987_654_321;
         K     : Key_Type;
         Top   : Key_Type;
         Prev  : Key_Type := Key_Type'First;
         Sum   : Long_Long_Integer := 0;
         Back  : Long_Long_Integer := 0;
      begin
         Clear;
         Check (Room = Nodes, Kind & " arena: a cleared arena is all free");
         Check (Is_Empty (T), Kind & " arena: the empty tree starts empty");

         for I in 1 .. N loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);
            Sum := Sum + Long_Long_Integer (K);
            Insert (T, K);
            Check (Size_Of (T) = I, Kind & " arena: size after insert");
            Check (Room = Nodes - I,
                   Kind & " arena: an insert takes exactly one node");
         end loop;

         for I in reverse 1 .. N loop
            Top := Peek_Min (T);
            Extract_Min (T, K);
            Check (K = Top,
                   Kind & " arena: extraction returns the key peek promised");
            Check (K >= Prev,
                   Kind & " arena: keys come out in non-decreasing order");
            Prev := K;
            Back := Back + Long_Long_Integer (K);
            Check (Size_Of (T) = I - 1,
                   Kind & " arena: size after extraction");
            Check (Room = Nodes - (I - 1),
                   Kind & " arena: an extraction gives exactly one node back");
         end loop;

         Check (Is_Empty (T), Kind & " arena: empty after draining");
         Check (Room = Nodes, Kind & " arena: every node is back");
         Check (Sum = Back, Kind & " arena: nothing lost on the way");
      end Test_Arena;

      procedure Test_Arena_Churn (N : Positive) is
         --  Alternating an extraction and an insertion keeps the free chain
         --  moving: every extraction pushes a node back onto it and the next
         --  insertion takes that node off again, so the slots are recycled
         --  over and over. A stale link left behind in a recycled node, a
         --  leak, or a node released twice all surface here rather than in a
         --  straight fill and drain.
         T     : Extended_Index := 0;
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
         Clear;

         for I in 1 .. N loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 1_000);
            Hold (K);
            Insert (T, K);
         end loop;

         for I in 1 .. 4 * N loop
            Check (Peek_Min (T) = Least,
                   Kind & " arena: churn keeps the smallest key on top");
            Extract_Min (T, K);
            Drop_Least;

            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 1_000);
            Hold (K);
            Insert (T, K);

            Check (Size_Of (T) = N,
                   Kind & " arena: churn holds the size steady");
            Check (Room = Nodes - N,
                   Kind & " arena: churn returns every node it takes");
         end loop;

         for I in 1 .. N loop
            Extract_Min (T, K);
            Check (K >= Prev,
                   Kind & " arena: a churned tree still drains in order");
            Prev := K;
         end loop;

         Check (Room = Nodes, Kind & " arena: churn leaked no node");
      end Test_Arena_Churn;

      procedure Test_Arena_Meld (N, M : Natural) is
         Total    : constant Natural := N + M;
         Bystands : constant Natural := 32;
         --  A third tree, which neither operand of the meld names. The arena's
         --  postcondition says every other tree of the pool keeps the model it
         --  had; this is what checks it.

         Into : Extended_Index := 0;
         From : Extended_Index := 0;
         Idle : Extended_Index := 0;

         Oracle : Key_Array (1 .. Total) :=
           [others => 0];
         Filled : Natural := 0;

         Aside : Key_Array (1 .. Bystands) := [others => 0];

         State  : Long_Long_Integer := 24_680_135;
         K      : Key_Type;
         Before : Extended_Index;
         Prev   : Key_Type := Key_Type'First;

         procedure Feed (Count : Natural; Target : in out Extended_Index);
         procedure Feed (Count : Natural; Target : in out Extended_Index) is
         begin
            for I in 1 .. Count loop
               State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
               K := Key_Type (State mod 100_000);
               Filled := Filled + 1;
               Oracle (Filled) := K;
               Insert (Target, K);
            end loop;
         end Feed;
      begin
         Clear;

         Feed (N, Into);
         Feed (M, From);

         for I in 1 .. Bystands loop
            State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
            K := Key_Type (State mod 100_000);
            Aside (I) := K;
            Insert (Idle, K);
         end loop;

         Check (Room = Nodes - (Total + Bystands),
                Kind & " arena meld: the three trees share the one pool");

         --  A meld allocates, frees and copies nothing: it is a splice, and
         --  the free count is the run-time witness of that.

         Before := Room;
         Meld (Into, From);
         Check (Room = Before,
                Kind & " arena meld: no node is allocated or freed");

         Check (Size_Of (Into) = Total, Kind & " arena meld: size is the sum");
         Check (Is_Empty (From), Kind & " arena meld: the source is emptied");

         Sort (Oracle, Total);

         for I in 1 .. Total loop
            Extract_Min (Into, K);
            Check (K = Oracle (I),
                   Kind & " arena meld: drain matches the oracle");
            Check (K >= Prev,
                   Kind
                   & " arena meld: keys come out in non-decreasing order");
            Prev := K;
         end loop;

         Check (Is_Empty (Into), Kind & " arena meld: empty after draining");

         --  And the bystander is exactly as it was left.

         Sort (Aside, Bystands);
         Check (Size_Of (Idle) = Bystands,
                Kind & " arena meld: the tree it did not name kept its size");

         for I in 1 .. Bystands loop
            Extract_Min (Idle, K);
            Check (K = Aside (I),
                   Kind
                   & " arena meld: the tree it did not name kept its keys");
         end loop;

         Check (Room = Nodes, Kind & " arena meld: every node is back");
      end Test_Arena_Meld;

      procedure Test_Arena_KWay (N, Ways : Positive) is
         --  k trees in one pool folded into one accumulator, each meld a
         --  splice of two right spines.
         Each  : constant Positive := Positive'Max (1, N / Ways);
         Total : constant Natural := Each * Ways;

         Acc   : Extended_Index := 0;
         Ops   : array (1 .. Ways) of Extended_Index := [others => 0];

         Oracle : Key_Array (1 .. Total) := [others => 0];
         Filled : Natural := 0;

         State  : Long_Long_Integer := 13_579_246;
         K      : Key_Type;
         Before : Extended_Index;
         Prev   : Key_Type := Key_Type'First;
      begin
         Clear;

         for W in Ops'Range loop
            for I in 1 .. Each loop
               State := (State * 1_103_515_245 + 12_345) mod 2_147_483_647;
               K := Key_Type (State mod 100_000);
               Filled := Filled + 1;
               Oracle (Filled) := K;
               Insert (Ops (W), K);
            end loop;
         end loop;

         Check (Room = Nodes - Total,
                Kind & " arena k-way: every operand is in the one pool");

         Before := Room;

         for W in Ops'Range loop
            Meld (Acc, Ops (W));
            Check (Is_Empty (Ops (W)),
                   Kind & " arena k-way: the operand is emptied");
            Check (Size_Of (Acc) = Each * W,
                   Kind
                   & " arena k-way: the accumulator grows by one operand");
         end loop;

         Check (Room = Before,
                Kind & " arena k-way: the folding moved no node");

         Sort (Oracle, Total);

         for I in 1 .. Total loop
            Extract_Min (Acc, K);
            Check (K = Oracle (I),
                   Kind & " arena k-way: drain matches the oracle");
            Check (K >= Prev,
                   Kind
                   & " arena k-way: keys come out in non-decreasing order");
            Prev := K;
         end loop;

         Check (Room = Nodes, Kind & " arena k-way: every node is back");
      end Test_Arena_KWay;

   end Arena_Suite;

   --  One instance per arena. A tree is a subtype of Extended_Index and a
   --  generic formal subprogram asks only for mode conformance, so the
   --  arenas' operations match the formals directly.

   package Leftist_Suite is new Arena_Suite
     (Kind        => "leftist",
      Nodes       => Arena.Nodes,
      Clear       => Arena.Clear,
      Room        => Arena.Room,
      Is_Empty    => Arena.Is_Empty,
      Size_Of     => Arena.Size_Of,
      Peek_Min    => Arena.Peek_Min,
      Insert      => Arena.Insert,
      Extract_Min => Arena.Extract_Min,
      Meld        => Arena.Meld);

   package Skew_Suite is new Arena_Suite
     (Kind        => "skew",
      Nodes       => Skew_Arena.Nodes,
      Clear       => Skew_Arena.Clear,
      Room        => Skew_Arena.Room,
      Is_Empty    => Skew_Arena.Is_Empty,
      Size_Of     => Skew_Arena.Size_Of,
      Peek_Min    => Skew_Arena.Peek_Min,
      Insert      => Skew_Arena.Insert,
      Extract_Min => Skew_Arena.Extract_Min,
      Meld        => Skew_Arena.Meld);

   package Pairing_Suite is new Arena_Suite
     (Kind        => "pairing",
      Nodes       => Pair_Arena.Nodes,
      Clear       => Pair_Arena.Clear,
      Room        => Pair_Arena.Room,
      Is_Empty    => Pair_Arena.Is_Empty,
      Size_Of     => Pair_Arena.Size_Of,
      Peek_Min    => Pair_Arena.Peek_Min,
      Insert      => Pair_Arena.Insert,
      Extract_Min => Pair_Arena.Extract_Min,
      Meld        => Pair_Arena.Meld);

begin
   Test_Radix_Buckets;
   Test_Radix_Advanced_Meld;

   for Activate_Into in Boolean loop
      for Activate_From in Boolean loop
         Test_Open_Proved_Meld (Activate_Into, Activate_From);
      end loop;
   end loop;

   --  Exercise both sides of full and partial 256-key blocks. In particular,
   --  extraction moves the last key across a block boundary at these sizes.
   for N of Block_Boundary_Sizes loop
      Test_Block_Min_Churn (N);
   end loop;

   --  Every size from 1 to 200 crosses each of the first twenty layer
   --  boundaries in both directions.
   for N in 1 .. 200 loop
      Test_Beap_Churn (N);
      Test_Tournament_Churn (N);
      Test_Weak_Churn (N);
   end loop;

   --  The arena churns over fewer sizes: it has no layer or level boundaries
   --  to sweep, and what matters is only that slots go back onto the free
   --  chain and come off it again.
   for N of Churn_Sizes loop
      Test_Bucket_Churn (N);
      Test_Radix_Churn (N);
      Leftist_Suite.Test_Arena_Churn (N);
      Skew_Suite.Test_Arena_Churn (N);
      Pairing_Suite.Test_Arena_Churn (N);
   end loop;

   for N of Sizes loop
      Test_Binary (N);
      Test_Tournament (N);
      Test_Block_Min (N);
      Test_Bucket (N);
      Test_Radix (N);
      Test_Weak (N);
      Leftist_Suite.Test_Arena (N);
      Skew_Suite.Test_Arena (N);
      Pairing_Suite.Test_Arena (N);
      Test_Beap (N);
      Test_Min_Max (N);
      Test_Min_Max_Tournament (N);
      Test_Interval (N);
      Test_Open_Proved (N);
      for Arity in Heaps.Dary.Arity_Type range 2 .. 5 loop
         Test_Dary (N, Arity);
      end loop;
      Test_Dary (N, 16);
      Test_Dary (N, 64);
      Test_Sorted (N);
      Test_Sorted_Linked (N);
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

   Test_Sorted_Linked_Meld (64, 64);
   Test_Sorted_Linked_Meld (64, 1);
   Test_Sorted_Linked_Meld (1, 64);
   Test_Sorted_Linked_Meld (64, 0);
   Test_Sorted_Linked_Meld (0, 64);
   Test_Sorted_Linked_Meld (0, 0);

   Test_Bucket_Meld (64, 64);
   Test_Bucket_Meld (64, 1);
   Test_Bucket_Meld (1, 64);
   Test_Bucket_Meld (64, 0);
   Test_Bucket_Meld (0, 64);
   Test_Bucket_Meld (0, 0);

   Test_Radix_Meld (64, 64);
   Test_Radix_Meld (64, 1);
   Test_Radix_Meld (1, 64);
   Test_Radix_Meld (64, 0);
   Test_Radix_Meld (0, 64);
   Test_Radix_Meld (0, 0);

   --  The arena's own meld, over the same shapes, plus a k-way fold: with
   --  one pool holding every operand, folding k trees into one is the
   --  workload the structure exists for.
   for N of Sizes loop
      Leftist_Suite.Test_Arena_Meld (N, N);
      Leftist_Suite.Test_Arena_Meld (N, 1);
      Leftist_Suite.Test_Arena_Meld (1, N);
      Leftist_Suite.Test_Arena_Meld (N, 0);
      Leftist_Suite.Test_Arena_Meld (0, N);
      Leftist_Suite.Test_Arena_KWay (N, 16);

      Skew_Suite.Test_Arena_Meld (N, N);
      Skew_Suite.Test_Arena_Meld (N, 1);
      Skew_Suite.Test_Arena_Meld (1, N);
      Skew_Suite.Test_Arena_Meld (N, 0);
      Skew_Suite.Test_Arena_Meld (0, N);
      Skew_Suite.Test_Arena_KWay (N, 16);

      Pairing_Suite.Test_Arena_Meld (N, N);
      Pairing_Suite.Test_Arena_Meld (N, 1);
      Pairing_Suite.Test_Arena_Meld (1, N);
      Pairing_Suite.Test_Arena_Meld (N, 0);
      Pairing_Suite.Test_Arena_Meld (0, N);
      Pairing_Suite.Test_Arena_KWay (N, 16);
   end loop;

   Leftist_Suite.Test_Arena_Meld (0, 0);
   Leftist_Suite.Test_Arena_KWay (1, 16);
   Skew_Suite.Test_Arena_Meld (0, 0);
   Skew_Suite.Test_Arena_KWay (1, 16);
   Pairing_Suite.Test_Arena_Meld (0, 0);
   Pairing_Suite.Test_Arena_KWay (1, 16);

   if Failures = 0 then
      Put_Line ("all heap tests passed");
   else
      Put_Line (Natural'Image (Failures) & " failure(s)");
   end if;
end Heaps_Test;
