--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Radix with SPARK_Mode is

   package KM renames Key_Multisets;

   --------------------------
   -- Monotonicity lifting --
   --------------------------

   --  Every operation re-establishes the ordering of the delimiters and of
   --  the boundaries from adjacent pairs, which is what the pointwise
   --  description of an update gives directly. These two lemmas lift that to
   --  the pairwise form the invariant is stated in.

   procedure Lemma_Lift_Starts (S : Start_Array)
     with Ghost,
          Pre  => (for all D in 0 .. Start_Index'Last - 1 => S (D) <= S (D + 1)),
          Post => (for all A in Start_Index =>
                     (for all B in Start_Index =>
                        (if A <= B then S (A) <= S (B))));

   procedure Lemma_Lift_Starts (S : Start_Array) is
   begin
      for A in Start_Index loop
         for B in A .. Start_Index'Last loop
            pragma Loop_Invariant (for all Q in A .. B => S (A) <= S (Q));
         end loop;

         pragma Loop_Invariant
           (for all X in 0 .. A =>
              (for all B in Start_Index => (if X <= B then S (X) <= S (B))));
      end loop;
   end Lemma_Lift_Starts;

   procedure Lemma_Lift_Bounds (B : Bound_Array)
     with Ghost,
          Pre  => (for all D in 1 .. Bucket_Index'Last => B (D - 1) <= B (D)),
          Post => (for all X in Bucket_Index =>
                     (for all Y in Bucket_Index =>
                        (if X <= Y then B (X) <= B (Y))));

   procedure Lemma_Lift_Bounds (B : Bound_Array) is
   begin
      for X in Bucket_Index loop
         for Y in X .. Bucket_Index'Last loop
            pragma Loop_Invariant (for all Q in X .. Y => B (X) <= B (Q));
         end loop;

         pragma Loop_Invariant
           (for all P in 0 .. X =>
              (for all Y in Bucket_Index => (if P <= Y then B (P) <= B (Y))));
      end loop;
   end Lemma_Lift_Bounds;

   procedure Lemma_Power_Monotonic (Left, Right : Split_Bit)
     with Ghost,
          Pre  => Left <= Right,
          Post => Power_Of_Two (Left) <= Power_Of_Two (Right),
          Subprogram_Variant => (Decreases => Right - Left);

   procedure Lemma_Power_Monotonic (Left, Right : Split_Bit) is
   begin
      if Left < Right then
         Lemma_Power_Monotonic (Left + 1, Right);
      end if;
   end Lemma_Power_Monotonic;

   procedure Lemma_Initial_Bounds
     with Ghost,
          Post => (for all D in 1 .. Bucket_Index'Last =>
                     Initial_Bound (D - 1) <= Initial_Bound (D));

   procedure Lemma_Initial_Bounds is
   begin
      for D in 1 .. Bucket_Index'Last loop
         if D < Bucket_Index'Last then
            Lemma_Power_Monotonic (D - 1, D);
         else
            Lemma_Power_Monotonic (D - 1, Split_Bit'Last);
         end if;

         pragma Loop_Invariant
           (for all Q in 1 .. D => Initial_Bound (Q - 1) <= Initial_Bound (Q));
      end loop;
   end Lemma_Initial_Bounds;

   ----------
   -- Swap --
   ----------

   procedure Swap (H : in out Heap; I, J : Index)
     with Pre  => I < J and then J <= H.Last,
          Post => H.Keys (I) = H.Keys'Old (J)
                  and then H.Keys (J) = H.Keys'Old (I)
                  and then (for all Q in 1 .. H.Capacity =>
                              (if Q /= I and then Q /= J
                               then H.Keys (Q) = H.Keys'Old (Q)))
                  and then H.Last = H.Last'Old
                  and then H.Base = H.Base'Old
                  and then H.Bound = H.Bound'Old
                  and then H.Starts = H.Starts'Old
                  and then Model (H) = Model (H'Old);
   --  The only way this unit ever rearranges keys, so the multiset argument
   --  of every operation reduces to the one slot it genuinely adds or drops.

   procedure Swap (H : in out Heap; I, J : Index) is
      Old_Keys : constant Key_Array := H.Keys with Ghost;
      T        : constant Key_Type := H.Keys (I);
   begin
      H.Keys (I) := H.Keys (J);
      H.Keys (J) := T;
      Models.Lemma_Swap (Old_Keys, H.Keys, I, J, H.Last);
   end Swap;

   ----------------
   -- Bucket_For --
   ----------------

   function Bucket_For (H : Heap; K : Key_Type) return Bucket_Index is
   begin
      for B in Bucket_Index loop
         if K <= H.Bound (B) then
            return B;
         end if;

         pragma Loop_Invariant (for all D in 0 .. B => K > H.Bound (D));
      end loop;

      return Bucket_Index'Last;
   end Bucket_For;

   ---------------------
   -- Lowest_Nonempty --
   ---------------------

   function Lowest_Nonempty (H : Heap) return Bucket_Index
     with Pre  => Is_Heap (H) and then not Is_Empty (H),
          Post => H.Starts (Lowest_Nonempty'Result) = 1
                  and then H.Starts (Lowest_Nonempty'Result + 1) > 1;

   function Lowest_Nonempty (H : Heap) return Bucket_Index is
   begin
      for B in Bucket_Index loop
         if H.Starts (B + 1) > 1 then
            return B;
         end if;

         pragma Loop_Invariant (for all D in 0 .. B + 1 => H.Starts (D) = 1);
      end loop;

      return Bucket_Index'Last;
   end Lowest_Nonempty;

   ------------------
   -- Min_Position --
   ------------------

   function Min_Position (H : Heap; J : Bucket_Index) return Index
     with Pre  => Is_Heap (H)
                  and then not Is_Empty (H)
                  and then H.Starts (J) = 1
                  and then H.Starts (J + 1) > 1,
          Post => Min_Position'Result in 1 .. H.Starts (J + 1) - 1
                  and then
                    (for all Q in 1 .. H.Starts (J + 1) - 1 =>
                       H.Keys (Min_Position'Result) <= H.Keys (Q));

   function Min_Position (H : Heap; J : Bucket_Index) return Index is
      Stop : constant Index := H.Starts (J + 1) - 1;
      Best : Index := 1;
   begin
      for I in 2 .. Stop loop
         if H.Keys (I) < H.Keys (Best) then
            Best := I;
         end if;

         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (for all Q in 1 .. I => H.Keys (Best) <= H.Keys (Q));
      end loop;

      return Best;
   end Min_Position;

   ------------------
   -- Lemma_Run_Of --
   ------------------

   procedure Lemma_Run_Of (H : Heap; I : Index)
     with Ghost,
          Pre  => Is_Heap (H) and then I <= H.Last,
          Post => (for some B in Bucket_Index =>
                     I >= H.Starts (B) and then I < H.Starts (B + 1));

   procedure Lemma_Run_Of (H : Heap; I : Index) is
   begin
      for B in Bucket_Index loop
         pragma Loop_Invariant (I >= H.Starts (B));

         if I < H.Starts (B + 1) then
            return;
         end if;
      end loop;
   end Lemma_Run_Of;

   ----------------------
   -- Lemma_Min_Below  --
   ----------------------

   procedure Lemma_Min_Below (H : Heap; J : Bucket_Index; K : Key_Type)
     with Ghost,
          Pre  => Is_Heap (H)
                  and then H.Starts (J) = 1
                  and then K <= H.Bound (J)
                  and then (for all Q in 1 .. H.Starts (J + 1) - 1 =>
                              K <= H.Keys (Q)),
          Post => Is_Minimum (H, K);
   --  Everything outside the lowest non-empty run sits in a bucket above J,
   --  and so above J's upper boundary, which K does not exceed.

   procedure Lemma_Min_Below (H : Heap; J : Bucket_Index; K : Key_Type) is
   begin
      for I in 1 .. H.Last loop
         if I >= H.Starts (J + 1) then
            Lemma_Run_Of (H, I);

            for B in Bucket_Index loop
               if I >= H.Starts (B) and then I < H.Starts (B + 1) then
                  pragma Assert (B > J);
                  pragma Assert (H.Keys (I) > H.Bound (B - 1));
                  pragma Assert (H.Bound (J) <= H.Bound (B - 1));
                  pragma Assert (K <= H.Keys (I));
                  exit;
               end if;

               pragma Loop_Invariant
                 (for all D in 0 .. B =>
                    not (I >= H.Starts (D) and then I < H.Starts (D + 1)));
            end loop;
         end if;

         pragma Assert (K <= H.Keys (I));
         pragma Loop_Invariant (for all Q in 1 .. I => K <= H.Keys (Q));
      end loop;
   end Lemma_Min_Below;

   -------------------------
   -- Lemma_Minima_Equal  --
   -------------------------

   procedure Lemma_Minima_Equal (H : Heap; A, B : Key_Type)
     with Ghost,
          Pre  => Is_Minimum (H, A)
                  and then Is_Minimum (H, B)
                  and then (for some I in 1 .. H.Last => A = H.Keys (I))
                  and then (for some I in 1 .. H.Last => B = H.Keys (I)),
          Post => A = B;

   procedure Lemma_Minima_Equal (H : Heap; A, B : Key_Type) is
   begin
      for I in 1 .. H.Last loop
         if H.Keys (I) = A then
            pragma Assert (B <= A);
         end if;
         if H.Keys (I) = B then
            pragma Assert (A <= B);
         end if;
      end loop;
   end Lemma_Minima_Equal;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
      H.Base := 0;
      H.Bound := Initial_Bound;
      H.Starts := [others => 1];

      Lemma_Initial_Bounds;
      Lemma_Lift_Bounds (H.Bound);
      Lemma_Lift_Starts (H.Starts);
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
      J : constant Bucket_Index := Lowest_Nonempty (H);
      P : constant Index := Min_Position (H, J);
   begin
      Lemma_Min_Below (H, J, H.Keys (P));
      return H.Keys (P);
   end Peek_Min;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Old_Last  : constant Extended_Index := H.Last;
      Slot      : constant Index := Old_Last + 1;
      Old_Keys  : constant Key_Array := H.Keys with Ghost;
      Old_Model : constant KM.Multiset := Model (H) with Ghost;
      Stale     : constant Key_Type := H.Keys (Slot) with Ghost;
      S0        : constant Start_Array := H.Starts with Ghost;
      B         : constant Bucket_Index := Bucket_For (H, K);
      Hole      : Delimiter := Slot;
   begin
      pragma Assert
        (for all A in Start_Index =>
           (for all B in Start_Index => (if A <= B then S0 (A) <= S0 (B))));
      pragma Assert (for all D in Start_Index => S0 (D) <= Slot);

      H.Last := Slot;
      H.Starts (Start_Index'Last) := Slot + 1;

      --  Every run above B slides up by one slot. Moving a run's first key
      --  to the slot just past its end does that in one write per run, and
      --  carries the hole down to the end of run B.

      for C in reverse B + 1 .. Bucket_Index'Last loop
         if H.Starts (C) < Hole then
            Swap (H, H.Starts (C), Hole);
            Hole := H.Starts (C);
         end if;

         H.Starts (C) := H.Starts (C) + 1;

         pragma Loop_Invariant (Hole = S0 (C));
         pragma Loop_Invariant (H.Keys (Hole) = Stale);
         pragma Loop_Invariant (H.Last = Slot);
         pragma Loop_Invariant (H.Base = H.Base'Loop_Entry);
         pragma Loop_Invariant (H.Bound = H.Bound'Loop_Entry);
         pragma Loop_Invariant (H.Starts (Start_Index'Last) = Slot + 1);
         pragma Loop_Invariant
           (for all D in Start_Index => H.Starts (D) <= Slot + 1);
         pragma Loop_Invariant
           (for all D in 0 .. C - 1 => H.Starts (D) = S0 (D));
         pragma Loop_Invariant
           (for all D in C .. Bucket_Index'Last => H.Starts (D) = S0 (D) + 1);
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, Slot)
              = Models.Occurrences (Old_Keys, Slot));
         pragma Loop_Invariant
           (for all D in C .. Bucket_Index'Last =>
              (for all I in H.Starts (D) .. H.Starts (D + 1) - 1 =>
                 H.Keys (I) <= H.Bound (D)
                 and then H.Keys (I) > H.Bound (D - 1)));
         pragma Loop_Invariant
           (for all D in 0 .. C - 1 =>
              (for all I in H.Starts (D) .. H.Starts (D + 1) - 1 =>
                 (if I /= Hole then
                    H.Keys (I) <= H.Bound (D)
                    and then (if D = 0
                              then H.Keys (I) = H.Base
                              else H.Keys (I) > H.Bound (D - 1)))));
      end loop;

      pragma Assert (Hole = S0 (B + 1));
      pragma Assert (H.Starts (B) = S0 (B));
      pragma Assert (H.Starts (B + 1) = S0 (B + 1) + 1);

      --  The stale key that the extended prefix started with has been walked
      --  down to Hole, so overwriting it exchanges it for K.

      declare
         Before : constant Key_Array := H.Keys with Ghost;
      begin
         H.Keys (Hole) := K;

         Models.Lemma_Set (Before, H.Keys, Hole, Slot);
         pragma Assert
           (KM.Add (Models.Occurrences (H.Keys, Slot), Stale)
              = KM.Add (Models.Occurrences (Before, Slot), K));
         pragma Assert
           (Models.Occurrences (Old_Keys, Slot) = KM.Add (Old_Model, Stale));
         Models.Lemma_Add_Congruent
           (Models.Occurrences (Before, Slot),
            KM.Add (Old_Model, Stale), K);
         Models.Lemma_Add_Commutes (Old_Model, Stale, K);
         Models.Lemma_Add_Cancels
           (Models.Occurrences (H.Keys, Slot), KM.Add (Old_Model, K), Stale);
      end;

      pragma Assert
        (for all D in 0 .. Start_Index'Last - 1 =>
           H.Starts (D) <= H.Starts (D + 1));
      Lemma_Lift_Starts (H.Starts);
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      M0   : constant KM.Multiset := Model (Into) with Ghost;
      Base : constant Extended_Index := Into.Last;
   begin
      for I in 1 .. From.Last loop
         Insert (Into, From.Keys (I));
         Models.Lemma_Sum_Add
           (M0, Models.Occurrences (From.Keys, I - 1), From.Keys (I));
         Models.Lemma_Sum_Empty (M0);

         pragma Loop_Invariant (Is_Heap (Into));
         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant (Into.Base = Into.Base'Loop_Entry);
         pragma Loop_Invariant
           (Model (Into) = M0 + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (M0);
      end if;

      Clear (From);
   end Meld;

   ---------------------------
   -- The phases of removal --
   ---------------------------

   --  Between the three steps below the heap is not a heap: the buckets at
   --  and below J have been merged into the single run 1 .. Starts (J + 1) - 1
   --  whose keys are known only to lie between the base and J's upper
   --  boundary. Everything above J is untouched throughout, which is the
   --  whole point of the structure and is what this predicate records.

   function Low_Run (H : Heap; J : Bucket_Index) return Boolean is
     (Runs_Delimited (H)
      and then H.Bound (Bucket_Index'Last) = Key_Type'Last
      and then Bounds_Sorted (H)
      and then (for all D in 0 .. J => H.Starts (D) = 1)
      and then
        (for all B in J + 1 .. Bucket_Index'Last =>
           (for all I in H.Starts (B) .. H.Starts (B + 1) - 1 =>
              H.Keys (I) <= H.Bound (B)
              and then H.Keys (I) > H.Bound (B - 1))))
     with Ghost;

   ----------------
   -- Detach_Min --
   ----------------

   procedure Detach_Min (H : in out Heap; J : Bucket_Index; K : out Key_Type)
     with Pre  => Is_Heap (H)
                  and then not Is_Empty (H)
                  and then H.Starts (J) = 1
                  and then H.Starts (J + 1) > 1,
          Post => Low_Run (H, J)
                  and then H.Base = H'Old.Base
                  and then H.Bound = H'Old.Bound
                  and then H.Last = H'Old.Last - 1
                  and then K >= H.Base
                  and then K <= H.Bound (J)
                  and then Is_Minimum (H'Old, K)
                  and then (for some I in 1 .. H'Old.Last => K = H'Old.Keys (I))
                  and then (for all I in 1 .. H.Starts (J + 1) - 1 =>
                              H.Keys (I) >= K
                              and then H.Keys (I) <= H.Bound (J))
                  and then Model (H'Old) = KM.Add (Model (H), K);

   procedure Detach_Min (H : in out Heap; J : Bucket_Index; K : out Key_Type) is
      Old_Last  : constant Index := H.Last;
      Old_Keys  : constant Key_Array := H.Keys with Ghost;
      Old_Base  : constant Key_Type := H.Base with Ghost;
      Old_Bound : constant Bound_Array := H.Bound with Ghost;
      S0        : constant Start_Array := H.Starts with Ghost;
      Top       : constant Index := H.Starts (J + 1) - 1;
      P         : constant Index := Min_Position (H, J);
      Hole      : Delimiter := Top;
   begin
      pragma Assert
        (for all A in Start_Index =>
           (for all B in Start_Index => (if A <= B then S0 (A) <= S0 (B))));
      pragma Assert (for all D in Start_Index => S0 (D) <= Old_Last + 1);
      pragma Assert (for all D in 0 .. J => S0 (D) = 1);

      K := H.Keys (P);
      Lemma_Min_Below (H, J, K);

      pragma Assert (K >= Old_Base);
      pragma Assert (K <= Old_Bound (J));

      --  Park the minimum at the end of its own run, then walk it up to the
      --  end of the array by handing it on from run to run: each run above J
      --  gives up its last key to the slot below its own start, which is a
      --  slide down by one.

      if P < Top then
         Swap (H, P, Top);
      end if;

      pragma Assert
        (for all I in 1 .. Top =>
           H.Keys (I) <= H.Bound (J)
           and then (if J = 0
                     then H.Keys (I) = H.Base
                     else H.Keys (I) > H.Bound (J - 1))
           and then K <= H.Keys (I));
      pragma Assert (H.Keys (Top) = K);
      pragma Assert
        (for all D in J + 1 .. Bucket_Index'Last =>
           (for all I in H.Starts (D) .. H.Starts (D + 1) - 1 =>
              H.Keys (I) <= H.Bound (D)
              and then H.Keys (I) > H.Bound (D - 1)));

      for C in J + 1 .. Bucket_Index'Last loop
         declare
            Old_S : constant Delimiter := H.Starts (C);
            Nxt   : constant Delimiter := H.Starts (C + 1);
         begin
            H.Starts (C) := Old_S - 1;

            if Old_S < Nxt then
               Swap (H, Hole, Nxt - 1);
               Hole := Nxt - 1;
            end if;
         end;

         pragma Loop_Invariant (Hole = S0 (C + 1) - 1);
         pragma Loop_Invariant (H.Keys (Hole) = K);
         pragma Loop_Invariant (H.Last = Old_Last);
         pragma Loop_Invariant (H.Base = Old_Base);
         pragma Loop_Invariant (H.Bound = Old_Bound);
         pragma Loop_Invariant
           (for all D in 0 .. C =>
              H.Starts (D) = (if D <= J then S0 (D) else S0 (D) - 1));
         pragma Loop_Invariant
           (for all D in C + 1 .. Start_Index'Last => H.Starts (D) = S0 (D));
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, Old_Last)
              = Models.Occurrences (Old_Keys, Old_Last));
         pragma Loop_Invariant
           (for all I in 1 .. Top - 1 =>
              H.Keys (I) <= H.Bound (J)
              and then (if J = 0
                        then H.Keys (I) = H.Base
                        else H.Keys (I) > H.Bound (J - 1))
              and then K <= H.Keys (I));
         pragma Loop_Invariant
           (for all D in J + 1 .. C =>
              (for all I in H.Starts (D) .. H.Starts (D + 1) - 1 =>
                 (if I /= Hole then
                    H.Keys (I) <= H.Bound (D)
                    and then H.Keys (I) > H.Bound (D - 1))));
         pragma Loop_Invariant
           (for all D in C + 1 .. Bucket_Index'Last =>
              (for all I in H.Starts (D) .. H.Starts (D + 1) - 1 =>
                 H.Keys (I) <= H.Bound (D)
                 and then H.Keys (I) > H.Bound (D - 1)));
      end loop;

      pragma Assert (Hole = Old_Last);

      H.Last := Old_Last - 1;
      H.Starts (Start_Index'Last) := H.Last + 1;

      pragma Assert
        (for all D in Start_Index =>
           H.Starts (D) = (if D <= J then S0 (D) else S0 (D) - 1));
      pragma Assert
        (for all D in 0 .. Start_Index'Last - 1 =>
           H.Starts (D) <= H.Starts (D + 1));
      Lemma_Lift_Starts (H.Starts);

      pragma Assert (H.Starts (J + 1) - 1 = Top - 1);

      pragma Assert
        (Models.Occurrences (H.Keys, Old_Last)
           = KM.Add (Model (H), H.Keys (Old_Last)));
   end Detach_Min;

   --------------------
   -- Rebuild_Bounds --
   --------------------

   procedure Rebuild_Bounds (H : in out Heap; J : Bucket_Index; K : Key_Type)
     with Pre  => Bounds_Sorted (H)
                  and then H.Bound (Bucket_Index'Last) = Key_Type'Last
                  and then K >= 0
                  and then K <= H.Bound (J)
                  and then (if J = 0 then K = H.Bound (0)),
          Post => Bounds_Sorted (H)
                  and then H.Bound (Bucket_Index'Last) = Key_Type'Last
                  and then H.Bound (0) = K
                  and then H.Base = K
                  and then (for all D in 1 .. Bucket_Index'Last =>
                              (if D >= J then H.Bound (D) = H'Old.Bound (D)))
                  and then H.Keys = H'Old.Keys
                  and then H.Starts = H'Old.Starts
                  and then H.Last = H'Old.Last
                  and then Model (H) = Model (H'Old);
   --  Bucket D below J takes the widest range of span 2 ** (D - 1) that still
   --  fits under J's own upper boundary. J and everything above it keep the
   --  ranges they had, which is what leaves their contents in place.

   procedure Rebuild_Bounds (H : in out Heap; J : Bucket_Index; K : Key_Type)
   is
      Old_Bound : constant Bound_Array := H.Bound with Ghost;
      Old_Keys  : constant Key_Array := H.Keys with Ghost;
   begin
      H.Base := K;
      H.Bound (0) := K;

      for D in 1 .. J - 1 loop
         if D > 1 then
            Lemma_Power_Monotonic (D - 1, D);
         end if;

         declare
            Span : constant Key_Type := Power_Of_Two (D) - 1;
         begin
            H.Bound (D) :=
              (if H.Bound (J) - K >= Span then K + Span else H.Bound (J));
         end;

         pragma Loop_Invariant (H.Bound (0) = K);
         pragma Loop_Invariant (H.Bound (J) = Old_Bound (J));
         pragma Loop_Invariant (K <= H.Bound (J));
         pragma Loop_Invariant
           (for all Q in 1 .. D =>
              H.Bound (Q) >= K and then H.Bound (Q) <= H.Bound (J));
         pragma Loop_Invariant
           (for all Q in 1 .. D =>
              H.Bound (Q) = (if H.Bound (J) - K >= Power_Of_Two (Q) - 1
                             then K + (Power_Of_Two (Q) - 1)
                             else H.Bound (J)));
         pragma Loop_Invariant
           (for all Q in 2 .. D =>
              Power_Of_Two (Q - 1) <= Power_Of_Two (Q));
         pragma Loop_Invariant
           (for all Q in 1 .. D => H.Bound (Q - 1) <= H.Bound (Q));
         pragma Loop_Invariant
           (for all Q in D + 1 .. Bucket_Index'Last =>
              H.Bound (Q) = Old_Bound (Q));
      end loop;

      pragma Assert
        (for all Q in 1 .. Bucket_Index'Last =>
           H.Bound (Q - 1) <= H.Bound (Q));
      Lemma_Lift_Bounds (H.Bound);
      Models.Lemma_Same_Prefix (Old_Keys, H.Keys, H.Last);
   end Rebuild_Bounds;

   ------------------
   -- Redistribute --
   ------------------

   procedure Redistribute (H : in out Heap; J : Bucket_Index)
     with Pre  => Low_Run (H, J)
                  and then H.Bound (0) = H.Base
                  and then (for all I in 1 .. H.Starts (J + 1) - 1 =>
                              H.Keys (I) >= H.Base
                              and then H.Keys (I) <= H.Bound (J)),
          Post => Is_Heap (H)
                  and then H.Base = H'Old.Base
                  and then H.Bound = H'Old.Bound
                  and then H.Last = H'Old.Last
                  and then Model (H) = Model (H'Old);
   --  One pass per bucket below J over what is left unplaced. Each pass needs
   --  a single comparison per key, because everything still unplaced is
   --  already known to sit above the previous bucket's boundary.

   procedure Redistribute (H : in out Heap; J : Bucket_Index) is
      Block    : constant Extended_Index := H.Starts (J + 1) - 1;
      Base     : constant Key_Type := H.Base with Ghost;
      Frontier : Delimiter := 1;
   begin
      pragma Assert (Block <= H.Last);

      for D in 0 .. J - 1 loop
         declare
            Opened : constant Delimiter := Frontier with Ghost;
         begin
            pragma Assert (H.Starts (D) = Opened);

            for Q in Frontier .. Block loop
               if H.Keys (Q) <= H.Bound (D) then
                  if Frontier /= Q then
                     Swap (H, Frontier, Q);
                  end if;
                  Frontier := Frontier + 1;
               end if;

               pragma Loop_Invariant (Frontier in Opened .. Q + 1);
               pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
               pragma Loop_Invariant (H.Base = Base);
               pragma Loop_Invariant (H.Bound = H.Bound'Loop_Entry);
               pragma Loop_Invariant (H.Starts = H.Starts'Loop_Entry);
               pragma Loop_Invariant
                 (Models.Occurrences (H.Keys, H.Last)
                    = Models.Occurrences (H.Keys'Loop_Entry, H.Last));
               pragma Loop_Invariant
                 (for all R in 1 .. Opened - 1 =>
                    H.Keys (R) = H.Keys'Loop_Entry (R));
               pragma Loop_Invariant
                 (for all R in Q + 1 .. Block =>
                    H.Keys (R) = H.Keys'Loop_Entry (R));
               pragma Loop_Invariant
                 (for all R in Block + 1 .. H.Last =>
                    H.Keys (R) = H.Keys'Loop_Entry (R));
               pragma Loop_Invariant
                 (for all R in Opened .. Frontier - 1 =>
                    H.Keys (R) <= H.Bound (D));
               pragma Loop_Invariant
                 (for all R in Frontier .. Q => H.Keys (R) > H.Bound (D));
               pragma Loop_Invariant
                 (for all R in Opened .. Block =>
                    H.Keys (R) >= Base and then H.Keys (R) <= H.Bound (J));
               pragma Loop_Invariant
                 (if D > 0
                  then (for all R in Opened .. Block =>
                          H.Keys (R) > H.Bound (D - 1)));
            end loop;
         end;

         H.Starts (D + 1) := Frontier;

         pragma Loop_Invariant (H.Starts (0) = 1);
         pragma Loop_Invariant (H.Starts (D + 1) = Frontier);
         pragma Loop_Invariant (Frontier <= Block + 1);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (H.Base = Base);
         pragma Loop_Invariant (H.Bound = H.Bound'Loop_Entry);
         pragma Loop_Invariant
           (for all E in 0 .. D => H.Starts (E) <= H.Starts (E + 1));
         pragma Loop_Invariant
           (for all E in 0 .. D + 1 => H.Starts (E) <= Frontier);
         pragma Loop_Invariant
           (for all Q in D + 2 .. Start_Index'Last =>
              H.Starts (Q) = H.Starts'Loop_Entry (Q));
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, H.Last)
              = Models.Occurrences (H.Keys'Loop_Entry, H.Last));
         pragma Loop_Invariant
           (for all R in Block + 1 .. H.Last =>
              H.Keys (R) = H.Keys'Loop_Entry (R));
         pragma Loop_Invariant
           (for all E in 0 .. D =>
              (for all I in H.Starts (E) .. H.Starts (E + 1) - 1 =>
                 H.Keys (I) <= H.Bound (E)
                 and then (if E = 0
                           then H.Keys (I) = H.Base
                           else H.Keys (I) > H.Bound (E - 1))));
         pragma Loop_Invariant
           (for all R in Frontier .. Block =>
              H.Keys (R) >= Base
              and then H.Keys (R) <= H.Bound (J)
              and then H.Keys (R) > H.Bound (D));
      end loop;

      pragma Assert (H.Starts (J) = Frontier);
      pragma Assert (H.Starts (J + 1) = Block + 1);
      pragma Assert
        (for all I in H.Starts (J) .. H.Starts (J + 1) - 1 =>
           H.Keys (I) <= H.Bound (J)
           and then (if J = 0
                     then H.Keys (I) = H.Base
                     else H.Keys (I) > H.Bound (J - 1)));
      pragma Assert
        (for all B in J + 1 .. Bucket_Index'Last =>
           (for all I in H.Starts (B) .. H.Starts (B + 1) - 1 =>
              H.Keys (I) <= H.Bound (B)
              and then H.Keys (I) > H.Bound (B - 1)));

      pragma Assert
        (for all D in 0 .. Start_Index'Last - 1 =>
           H.Starts (D) <= H.Starts (D + 1));
      Lemma_Lift_Starts (H.Starts);
   end Redistribute;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Old_Heap  : constant Heap := H with Ghost;
      J         : constant Bucket_Index := Lowest_Nonempty (H);
      Mid_Model : KM.Multiset with Ghost;
   begin
      Detach_Min (H, J, K);

      Mid_Model := Model (H);
      Lemma_Minima_Equal (Old_Heap, K, Peek_Min (Old_Heap));

      Rebuild_Bounds (H, J, K);
      pragma Assert (Model (H) = Mid_Model);

      Redistribute (H, J);
      pragma Assert (Model (H) = Mid_Model);
      Models.Lemma_Add_Congruent (Model (H), Mid_Model, K);
   end Extract_Min;

end Heaps.Radix;
