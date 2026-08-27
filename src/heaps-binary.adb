--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every O(log n) operation into a quadratic one. Since the
--  contracts are discharged by proof, run-time checking of them is redundant,
--  so assertions are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Binary with SPARK_Mode is

   package KM renames Key_Multisets;

   ---------------------------
   -- Lemma_Root_Is_Minimum --
   ---------------------------

   procedure Lemma_Root_Is_Minimum (H : Heap) is
   begin
      --  Induction on the index: the parent of I is a smaller index, so by the
      --  time I is reached the root has already been shown to be below it.

      for I in 1 .. H.Last loop
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (1) <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   ------------
   -- Min_Of --
   ------------

   function Min_Of (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) < Result then
            Result := H.Keys (I);
         end if;

         pragma Loop_Invariant (for all J in 1 .. I => Result <= H.Keys (J));
         pragma Loop_Invariant
           (for some J in 1 .. I => Result = H.Keys (J));
      end loop;

      return Result;
   end Min_Of;

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
      --  The model before the insertion

      Before : Key_Array := H.Keys with Ghost;
      --  Snapshot of the array taken just before each single-slot write, so
      --  that Models.Lemma_Set can relate the two states. SPARK does not
      --  allow declaring it inside the loop body, hence the hoisting.

      Hole : Index := H.Last + 1;
      --  The new key conceptually sits in a hole that travels up towards the
      --  root as long as the parent is strictly greater. Moving the hole
      --  rather than swapping halves the number of writes: the key itself is
      --  only stored once, when its final position is known.
   begin
      H.Last := Hole;

      while Hole > 1 and then H.Keys (Parent (Hole)) > K loop

         declare
            P : constant Index := Parent (Hole);
         begin
            Before := H.Keys;
            H.Keys (Hole) := H.Keys (P);

            --  Moving one key from P down to Hole exchanges, in the model,
            --  the key that was in the hole for a second copy of the key at
            --  P; cancelling the discarded key on both sides leaves the model
            --  with the new hole content added to Base.

            Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
            Models.Lemma_Add_Congruent
              (KM.Add (Base, Before (Hole)), Models.Occurrences (Before, H.Last),
               Before (P));
            Models.Lemma_Add_Commutes (Base, Before (Hole), Before (P));
            Models.Lemma_Add_Cancels
              (Models.Occurrences (H.Keys, H.Last),
               KM.Add (Base, Before (P)),
               Before (Hole));

            Hole := P;
         end;

         pragma Loop_Invariant (Hole <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);

         --  The heap ordering holds everywhere except at the hole, whose
         --  content is about to be overwritten.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if J /= Hole then H.Keys (Parent (J)) <= H.Keys (J)));

         --  The parent of the hole still dominates the children of the hole,
         --  which is what keeps the ordering valid when the hole moves up.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Parent (J) = Hole and Hole > 1
               then H.Keys (Parent (Hole)) <= H.Keys (J)));

         --  The key being inserted fits in the hole as far as the children of
         --  the hole are concerned.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Parent (J) = Hole then K <= H.Keys (J)));

         --  Model: everything the array holds is Base plus the stale key
         --  sitting in the hole.
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

   -------------------
   -- Ordered_Below --
   -------------------

   function Ordered_Below (H : Heap; I : Extended_Index) return Boolean is
     (for all J in 2 .. H.Last =>
        (if Parent (J) >= I then H.Keys (Parent (J)) <= H.Keys (J)))
     with Ghost;
   --  Every subtree whose root is at index I or later is a heap. This is the
   --  invariant a bottom-up build walks down: Ordered_Below (H, 1) is exactly
   --  Is_Heap (H), and Ordered_Below (H, H.Last / 2 + 1) is vacuous because
   --  such an index has no children inside the array.
   --
   --  Deliberately without a precondition: it appears as a hypothesis under
   --  an implication, and an expression function guarded by a precondition
   --  does not unfold there.

   ---------------
   -- Sift_Down --
   ---------------

   procedure Sift_Down (H : in out Heap; Start : Index)
     with Pre  => Start < H.Last
                  and then Ordered_Below (H, Start + 1),
          Post => Ordered_Below (H, Start)
                  and H.Last = H.Last'Old
                  and Model (H) = Model (H)'Old;
   --  Push the key at Start down until the subtree rooted there is a heap,
   --  given that the subtrees below it already are. The hole travels down and
   --  the key is stored once, as in Insert and Extract_Min.

   procedure Sift_Down (H : in out Heap; Start : Index) is
      Moved : constant Key_Type := H.Keys (Start);
      M0    : constant KM.Multiset := Model (H) with Ghost;

      Before : Key_Array := H.Keys with Ghost;
      --  See the comment on the homonym in Insert

      Hole  : Index := Start;
      Child : Index;
   begin
      loop
         exit when Hole > H.Last / 2;
         --  Past that point the hole is a leaf and the descent is over

         Child := 2 * Hole;

         if Child < H.Last and then H.Keys (Child + 1) < H.Keys (Child) then
            Child := Child + 1;
         end if;

         pragma Assert
           (for all J in 2 .. H.Last =>
              (if Parent (J) = Hole then H.Keys (Child) <= H.Keys (J)));

         exit when H.Keys (Child) >= Moved;

         Before := H.Keys;
         H.Keys (Hole) := H.Keys (Child);

         --  The same exchange argument as in Extract_Min, with the key to be
         --  placed standing in for the extracted minimum: the array holds the
         --  original model with Moved swapped for the stale key in the hole.

         Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
         Models.Lemma_Add_Congruent
           (KM.Add (Models.Occurrences (H.Keys, H.Last), Before (Hole)),
            KM.Add (Models.Occurrences (Before, H.Last), Before (Child)),
            Moved);
         Models.Lemma_Add_Commutes
           (Models.Occurrences (H.Keys, H.Last), Before (Hole), Moved);
         Models.Lemma_Add_Commutes
           (Models.Occurrences (Before, H.Last), Moved, Before (Child));
         Models.Lemma_Add_Congruent
           (KM.Add (Models.Occurrences (Before, H.Last), Moved),
            KM.Add (M0, Before (Hole)),
            Before (Child));
         Models.Lemma_Add_Commutes (M0, Before (Hole), Before (Child));
         Models.Lemma_Add_Cancels
           (KM.Add (Models.Occurrences (H.Keys, H.Last), Moved),
            KM.Add (M0, Before (Child)),
            Before (Hole));

         Hole := Child;

         pragma Loop_Invariant (Hole in Start .. H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant
           (Before'First = 1 and Before'Last = H.Keys'Last);

         --  The hole is a descendant of Start, so its parent is not above it

         pragma Loop_Invariant (if Hole /= Start then Parent (Hole) >= Start);

         --  The ordering holds throughout the subtree except at the hole,
         --  whose content is stale and about to be overwritten.

         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Parent (J) >= Start and then J /= Hole
               then H.Keys (Parent (J)) <= H.Keys (J)));

         --  The parent of the hole still dominates the children of the hole,
         --  which is what keeps the ordering valid as the hole descends.

         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Parent (J) = Hole and then Hole /= Start
               then H.Keys (Parent (Hole)) <= H.Keys (J)));

         --  And the key being carried down still fits above the hole

         pragma Loop_Invariant
           (if Hole /= Start then H.Keys (Parent (Hole)) <= Moved);

         pragma Loop_Invariant
           (KM.Add (Models.Occurrences (H.Keys, H.Last), Moved)
            = KM.Add (M0, H.Keys (Hole)));

         pragma Loop_Variant (Increases => Hole);
      end loop;

      Before := H.Keys;
      H.Keys (Hole) := Moved;

      --  Storing Moved in the hole puts back the key the descent was holding,
      --  so the model returns to what it was.

      Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
      Models.Lemma_Add_Cancels
        (Models.Occurrences (H.Keys, H.Last), M0, Before (Hole));
   end Sift_Down;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Before : constant Key_Array := Into.Keys with Ghost;
      Base   : constant Extended_Index := Into.Last;
      Cap    : constant Extended_Index := Into.Capacity;

      Joined : KM.Multiset with Ghost;
      --  The model of the concatenation, which the rebuild has to preserve

      Prev : Key_Array (1 .. Cap) with Ghost;
      --  See the comment on the homonym in Heaps.Unsorted.Meld
   begin
      --  Append the keys of From. This is the same argument as the unsorted
      --  array's meld: the prefix does not move and each copied key joins the
      --  sum in turn.

      for I in 1 .. From.Last loop
         Prev := Into.Keys;

         Into.Keys (Base + I) := From.Keys (I);
         Into.Last := Base + I;

         Models.Lemma_Same_Prefix (Prev, Into.Keys, Base + I - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (Prev, Base + I - 1),
            Models.Occurrences (Into.Keys, Base + I - 1),
            From.Keys (I));
         Models.Lemma_Sum_Add
           (Models.Occurrences (Before, Base),
            Models.Occurrences (From.Keys, I - 1),
            From.Keys (I));
         Models.Lemma_Sum_Empty (Models.Occurrences (Before, Base));

         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant
           (for all J in 1 .. Base => Into.Keys (J) = Before (J));
         pragma Loop_Invariant
           (Model (Into)
            = Models.Occurrences (Before, Base)
              + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (Models.Occurrences (Before, Base));
      end if;

      Joined := Model (Into);

      --  Rebuild bottom-up. An index past Last / 2 has no child inside the
      --  array, so the invariant starts out vacuously true and is extended
      --  one subtree at a time down to the root.

      pragma Assert (Ordered_Below (Into, Into.Last / 2 + 1));

      for I in reverse 1 .. Into.Last / 2 loop
         Sift_Down (Into, I);

         pragma Loop_Invariant (Ordered_Below (Into, I));
         pragma Loop_Invariant (Into.Last = Base + From.Last);
         pragma Loop_Invariant (Model (Into) = Joined);
      end loop;

      From.Last := 0;
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Moved : constant Key_Type := H.Keys (H.Last);
      --  The key of the last node, which has to be reinserted somewhere on
      --  the path from the root down

      Before : Key_Array := H.Keys with Ghost;
      --  See the comment on the homonym in Insert

      Hole  : Index := 1;
      Child : Index;
   begin
      Lemma_Root_Is_Minimum (H);

      K := H.Keys (1);
      H.Last := H.Last - 1;

      declare
         Base : constant KM.Multiset := Model (H) with Ghost;
         --  The model of the array with the last slot dropped: Full is Base
         --  plus Moved, by definition of Occurrences.
      begin
         loop
            exit when Hole > H.Last / 2;
            --  Past that point the hole is a leaf and the search is over

            --  Move down through the smaller of the two children
            Child := 2 * Hole;

            if Child < H.Last and then H.Keys (Child + 1) < H.Keys (Child) then
               Child := Child + 1;
            end if;

            pragma Assert
              (for all J in 2 .. H.Last =>
                 (if Parent (J) = Hole then H.Keys (Child) <= H.Keys (J)));

            exit when H.Keys (Child) >= Moved;

            Before := H.Keys;
            H.Keys (Hole) := H.Keys (Child);

            --  Same exchange argument as in Insert, but the key that has to
            --  be cancelled out is the extracted minimum K, which is what the
            --  hole held when the descent started.

            Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
            Models.Lemma_Add_Congruent
              (KM.Add (Models.Occurrences (H.Keys, H.Last), Before (Hole)),
               KM.Add (Models.Occurrences (Before, H.Last), Before (Child)),
               K);
            Models.Lemma_Add_Commutes
              (Models.Occurrences (H.Keys, H.Last), Before (Hole), K);
            Models.Lemma_Add_Commutes
              (Models.Occurrences (Before, H.Last), K, Before (Child));
            Models.Lemma_Add_Congruent
              (KM.Add (Models.Occurrences (Before, H.Last), K),
               KM.Add (Base, Before (Hole)),
               Before (Child));
            Models.Lemma_Add_Commutes (Base, Before (Hole), Before (Child));
            Models.Lemma_Add_Cancels
              (KM.Add (Models.Occurrences (H.Keys, H.Last), K),
               KM.Add (Base, Before (Child)),
               Before (Hole));

            Hole := Child;

            pragma Loop_Invariant (Hole <= H.Last);
            pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
            pragma Loop_Invariant
              (Before'First = 1 and Before'Last = H.Keys'Last);

            --  The heap ordering holds everywhere except at the hole
            pragma Loop_Invariant
              (for all J in 2 .. H.Last =>
                 (if J /= Hole then H.Keys (Parent (J)) <= H.Keys (J)));

            --  The parent of the hole dominates the children of the hole
            pragma Loop_Invariant
              (for all J in 2 .. H.Last =>
                 (if Parent (J) = Hole and Hole > 1
                  then H.Keys (Parent (Hole)) <= H.Keys (J)));

            --  The key being moved down is still large enough for the hole
            pragma Loop_Invariant
              (if Hole > 1 then H.Keys (Parent (Hole)) <= Moved);

            --  Model: the array still holds Base, except that the extracted
            --  key K has been replaced by whatever stale key is in the hole.
            pragma Loop_Invariant
              (KM.Add (Models.Occurrences (H.Keys, H.Last), K)
               = KM.Add (Base, H.Keys (Hole)));

            pragma Loop_Variant (Increases => Hole);
         end loop;

         if H.Last > 0 then
            Before := H.Keys;
            H.Keys (Hole) := Moved;

            Models.Lemma_Set (Before, H.Keys, Hole, H.Last);
            Models.Lemma_Add_Congruent
              (KM.Add (Models.Occurrences (H.Keys, H.Last), Before (Hole)),
               KM.Add (Models.Occurrences (Before, H.Last), Moved),
               K);
            Models.Lemma_Add_Commutes
              (Models.Occurrences (H.Keys, H.Last), Before (Hole), K);
            Models.Lemma_Add_Commutes
              (Models.Occurrences (Before, H.Last), K, Moved);
            Models.Lemma_Add_Congruent
              (KM.Add (Models.Occurrences (Before, H.Last), K),
               KM.Add (Base, Before (Hole)),
               Moved);
            Models.Lemma_Add_Commutes (Base, Before (Hole), Moved);
            Models.Lemma_Add_Cancels
              (KM.Add (Models.Occurrences (H.Keys, H.Last), K),
               KM.Add (Base, Moved),
               Before (Hole));
         end if;
      end;
   end Extract_Min;

end Heaps.Binary;
