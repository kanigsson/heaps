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

      Before := H.Keys;
      H.Keys (Hole) := K;

      Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
      Models.Lemma_Add_Congruent
        (KM.Add (Base, Before (Hole)), Models.Occurrences (Before, H.Last), K);
      Models.Lemma_Add_Commutes (Base, Before (Hole), K);
      Models.Lemma_Add_Cancels
        (Models.Occurrences (H.Keys, H.Last),
         KM.Add (Base, K),
         Before (Hole));
   end Insert;

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
