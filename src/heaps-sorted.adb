--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Sorted with SPARK_Mode is

   package KM renames Key_Multisets;

   ---------------------------
   -- Lemma_Last_Is_Minimum --
   ---------------------------

   procedure Lemma_Last_Is_Minimum (H : Heap) is
   begin
      for I in reverse 1 .. H.Last loop
         pragma Loop_Invariant
           (for all J in I .. H.Last => H.Keys (H.Last) <= H.Keys (J));
      end loop;
   end Lemma_Last_Is_Minimum;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
   end Clear;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Base : constant KM.Multiset := Model (H) with Ghost;

      Before : Key_Array := H.Keys with Ghost;
      --  Snapshot taken before each single-slot write, so that
      --  Models.Lemma_Set can relate the two states. SPARK does not allow
      --  declaring it inside the loop body, hence the hoisting.

      Hole : Index := H.Last + 1;
      --  As in the binary heap, a hole travels towards the front of the array
      --  and the key is stored once, at the end. Here the hole moves to the
      --  immediately preceding slot rather than to a parent, which is the
      --  only difference between the two proofs.
   begin
      H.Last := Hole;

      while Hole > 1 and then H.Keys (Hole - 1) < K loop

         Before := H.Keys;
         H.Keys (Hole) := H.Keys (Hole - 1);

         Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
         Models.Lemma_Add_Congruent
           (KM.Add (Base, Before (Hole)),
            Models.Occurrences (Before, H.Last),
            Before (Hole - 1));
         Models.Lemma_Add_Commutes (Base, Before (Hole), Before (Hole - 1));
         Models.Lemma_Add_Cancels
           (Models.Occurrences (H.Keys, H.Last),
            KM.Add (Base, Before (Hole - 1)),
            Before (Hole));

         Hole := Hole - 1;

         pragma Loop_Invariant (Hole <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant
           (Before'First = 1 and Before'Last = H.Keys'Last);

         --  The order holds everywhere except at the hole, whose content is
         --  about to be overwritten.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if J /= Hole then H.Keys (J - 1) >= H.Keys (J)));

         --  The slot before the hole still dominates the slot after it
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if J - 1 = Hole and Hole > 1
               then H.Keys (Hole - 1) >= H.Keys (J)));

         --  The key being inserted is small enough for the slot after the hole
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if J - 1 = Hole then K >= H.Keys (J)));

         --  Model: the array holds Base plus the stale key in the hole
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, H.Last)
            = KM.Add (Base, H.Keys (Hole)));

         pragma Loop_Variant (Decreases => Hole);
      end loop;

      --  The loop stopped because the slot before the hole is not below K,
      --  which is exactly what K needs to sit there; the invariants cover the
      --  slot after it. Splitting the order off from the model equations
      --  keeps the two arguments in separate proof obligations.

      pragma Assert (if Hole > 1 then H.Keys (Hole - 1) >= K);
      pragma Assert
        (for all J in 2 .. H.Last => (if J - 1 = Hole then K >= H.Keys (J)));

      Before := H.Keys;
      H.Keys (Hole) := K;

      pragma Assert (Is_Sorted (H));

      Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
      Models.Lemma_Add_Congruent
        (KM.Add (Base, Before (Hole)), Models.Occurrences (Before, H.Last), K);
      Models.Lemma_Add_Commutes (Base, Before (Hole), K);
      Models.Lemma_Add_Cancels
        (Models.Occurrences (H.Keys, H.Last),
         KM.Add (Base, K),
         Before (Hole));
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Old_Keys : constant Key_Array := Into.Keys with Ghost;
      Cap      : constant Extended_Index := Into.Capacity;

      Base  : constant Extended_Index := Into.Last;
      Extra : constant Extended_Index := From.Last;
      Total : constant Extended_Index := Base + Extra;

      Whole : constant KM.Multiset :=
        Models.Occurrences (Old_Keys, Base)
        + Models.Occurrences (From.Keys, Extra)
      with Ghost;

      Prev : Key_Array (1 .. Cap) with Ghost;
      --  See the comment on the homonym in Insert

      I : Extended_Index := Base;
      J : Extended_Index := Extra;
      --  The smallest key still to be taken from each run sits at these two
      --  slots; the runs decrease towards the front, so both walk backwards.

      K : Extended_Index := Total;
      --  The slot the next key goes into. It is always I + J, hence always
      --  above I, which is why the output never overwrites an unread key.

      Taken : Key_Type;
      --  The key the current step moves, whichever run it came from

      From_Side : Boolean;
      --  Which of the two runs the current step reads

      Head : KM.Multiset with Ghost;
      Done : KM.Multiset with Ghost;
      Rest : KM.Multiset with Ghost;
      --  The merged region including the key just written, that region
      --  without it, and the latter together with what is left of Into's own
      --  run. SPARK does not allow a non-scalar declaration ahead of a loop
      --  invariant, hence the hoisting.
   begin
      Models.Lemma_Sum_Empty_Left
        (Models.Occurrences (Old_Keys, Base)
         + Models.Occurrences (From.Keys, Extra));

      while J > 0 loop
         Prev := Into.Keys;

         --  Take the smaller of the two remaining minima and put it at the
         --  far end of what is left to fill. K is I + J, so the slot written
         --  always sits above the part of Into's own run still to be read.

         From_Side := I = 0 or else Into.Keys (I) > From.Keys (J);

         if From_Side then
            Taken := From.Keys (J);
         else
            Taken := Into.Keys (I);
         end if;

         Into.Keys (K) := Taken;

         if From_Side then
            J := J - 1;
         else
            I := I - 1;
         end if;

         K := K - 1;

         pragma Assert (Into.Keys (K + 1) = Taken);
         pragma Assert (if K + 2 <= Total then Taken >= Into.Keys (K + 2));
         pragma Assert (if not From_Side then Taken = Old_Keys (I + 1));
         pragma Assert (if From_Side then Taken = From.Keys (J + 1));

         --  The written slot is below the region already merged, so that
         --  region is unchanged and simply gains one key at its low end.

         Done := Models.Occurrences_In (Prev, K + 2, Total);
         Rest := Done + Models.Occurrences (Old_Keys, I);

         Models.Lemma_Range_Same (Prev, Into.Keys, K + 2, Total);
         Models.Lemma_Range_Peel (Into.Keys, K + 1, Total);
         Models.Lemma_Add_Congruent
           (Models.Occurrences_In (Into.Keys, K + 2, Total), Done, Taken);

         Head := Models.Occurrences_In (Into.Keys, K + 1, Total);
         pragma Assert (Head = KM.Add (Done, Taken));

         --  On the goal side, that one Add travels out through both sums.

         Models.Lemma_Sum_Congruent
           (Head, KM.Add (Done, Taken), Models.Occurrences (Old_Keys, I));
         Models.Lemma_Sum_Add_Left
           (Done, Models.Occurrences (Old_Keys, I), Taken);
         pragma Assert
           (Head + Models.Occurrences (Old_Keys, I) = KM.Add (Rest, Taken));
         Models.Lemma_Sum_Congruent
           (Head + Models.Occurrences (Old_Keys, I),
            KM.Add (Rest, Taken),
            Models.Occurrences (From.Keys, J));

         --  And on the other side the run the key came from loses it, which
         --  is the same Add coming out of the same place.

         if From_Side then
            pragma Assert
              (Whole = Rest + Models.Occurrences (From.Keys, J + 1));
            Models.Lemma_Sum_Add
              (Rest, Models.Occurrences (From.Keys, J), Taken);
            Models.Lemma_Sum_Add_Left
              (Rest, Models.Occurrences (From.Keys, J), Taken);
            pragma Assert
              (KM.Add (Rest, Taken) + Models.Occurrences (From.Keys, J)
               = Whole);
         else
            pragma Assert
              (Whole = Done + Models.Occurrences (Old_Keys, I + 1)
                       + Models.Occurrences (From.Keys, J));
            Models.Lemma_Sum_Add
              (Done, Models.Occurrences (Old_Keys, I), Taken);
            Models.Lemma_Sum_Congruent
              (Done + Models.Occurrences (Old_Keys, I + 1),
               KM.Add (Rest, Taken),
               Models.Occurrences (From.Keys, J));
            pragma Assert
              (KM.Add (Rest, Taken) + Models.Occurrences (From.Keys, J)
               = Whole);
         end if;

         pragma Assert
           (KM.Add (Rest, Taken) + Models.Occurrences (From.Keys, J) = Whole);
         pragma Assert
           (Head
            + Models.Occurrences (Old_Keys, I)
            + Models.Occurrences (From.Keys, J)
            = Whole);

         pragma Loop_Invariant (Into.Last = Base);
         pragma Loop_Invariant (I <= Base and J <= Extra and K = I + J);
         pragma Loop_Invariant
           (Prev'First = 1 and Prev'Last = Into.Keys'Last);
         pragma Loop_Invariant
           (for all M in 1 .. I => Into.Keys (M) = Old_Keys (M));

         --  The merged region is in order ...

         pragma Loop_Invariant
           (for all M in K + 2 .. Total =>
              Into.Keys (M - 1) >= Into.Keys (M));

         --  ... and everything still to be read is at least as large as the
         --  key at its low end, which is what lets the two parts be joined.

         pragma Loop_Invariant
           (if I >= 1 then Into.Keys (K + 1) <= Old_Keys (I));
         pragma Loop_Invariant
           (if J >= 1 then Into.Keys (K + 1) <= From.Keys (J));

         pragma Loop_Invariant
           (Models.Occurrences_In (Into.Keys, K + 1, Total)
            + Models.Occurrences (Old_Keys, I)
            + Models.Occurrences (From.Keys, J)
            = Whole);

         pragma Loop_Variant (Decreases => K);
      end loop;

      --  From is exhausted, so what is left of Into's own run is already
      --  where it belongs and the two regions meet at slot I.

      Into.Last := Total;

      pragma Assert (for all M in 1 .. I => Into.Keys (M) = Old_Keys (M));
      pragma Assert (for all M in 2 .. I => Into.Keys (M - 1) >= Into.Keys (M));
      pragma Assert
        (if I >= 1 and then I < Total
         then Into.Keys (I) >= Into.Keys (I + 1));
      pragma Assert
        (for all M in I + 2 .. Total => Into.Keys (M - 1) >= Into.Keys (M));
      pragma Assert (Is_Sorted (Into));

      pragma Assert (K = I);

      --  What the loop was carrying is the model of the two regions; with
      --  From exhausted its third term is empty, and the regions meet at I.

      Models.Lemma_Sum_Empty
        (Models.Occurrences_In (Into.Keys, I + 1, Total)
         + Models.Occurrences (Old_Keys, I));
      Models.Lemma_Sum_Empty_Left (Models.Occurrences (Old_Keys, I));
      Models.Lemma_Sum_Empty (Models.Occurrences (Old_Keys, Base));
      pragma Assert
        (Models.Occurrences_In (Into.Keys, I + 1, Total)
         + Models.Occurrences (Old_Keys, I) = Whole);

      Models.Lemma_Same_Prefix (Old_Keys, Into.Keys, I);
      Models.Lemma_Range_Split (Into.Keys, I, Total);
      Models.Lemma_Sum_Congruent
        (Models.Occurrences (Into.Keys, I),
         Models.Occurrences (Old_Keys, I),
         Models.Occurrences_In (Into.Keys, I + 1, Total));
      Models.Lemma_Sum_Symmetric
        (Models.Occurrences (Old_Keys, I),
         Models.Occurrences_In (Into.Keys, I + 1, Total));

      pragma Assert (Model (Into) = Whole);

      Clear (From);
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
   begin
      Lemma_Last_Is_Minimum (H);

      --  Dropping the last slot is all it takes: the model of a prefix is
      --  what the definition of Occurrences peels off, so the multiset
      --  equation holds by unfolding alone.

      K := H.Keys (H.Last);
      H.Last := H.Last - 1;
   end Extract_Min;

end Heaps.Sorted;
