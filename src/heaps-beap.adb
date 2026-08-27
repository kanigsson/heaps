--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every O(sqrt n) operation into a quadratic one. Since the
--  contracts are discharged by proof, run-time checking of them is redundant,
--  so assertions are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Beap with SPARK_Mode is

   package KM renames Key_Multisets;

   Double_Capacity : constant := 2 * Max_Capacity;

   ------------------------
   -- Moving a hole      --
   ------------------------

   --  Both sift loops work with a hole: a slot whose key has already been
   --  accounted for elsewhere and which the next write overwrites. The two
   --  lemmas below say what a single write to that slot does to the model, so
   --  that neither loop has to spell the multiset reasoning out again.

   procedure Lemma_Hole_Filled
     (A, R : Key_Array; I : Index; Lst : Extended_Index; Kept : KM.Multiset)
     with Ghost,
          Pre  => A'First = 1
                  and then R'First = 1
                  and then A'Last = R'Last
                  and then Lst <= A'Last
                  and then I <= Lst
                  and then (for all J in 1 .. Lst =>
                              (if J /= I then R (J) = A (J)))
                  and then Models.Occurrences (A, Lst) = KM.Add (Kept, A (I)),
          Post => Models.Occurrences (R, Lst) = KM.Add (Kept, R (I));
   --  The array holds Kept plus whatever sits in the hole

   procedure Lemma_Hole_Moved
     (A, R : Key_Array; I : Index; Lst : Extended_Index;
      Missing : Key_Type; Kept : KM.Multiset)
     with Ghost,
          Pre  => A'First = 1
                  and then R'First = 1
                  and then A'Last = R'Last
                  and then Lst <= A'Last
                  and then I <= Lst
                  and then (for all J in 1 .. Lst =>
                              (if J /= I then R (J) = A (J)))
                  and then KM.Add (Models.Occurrences (A, Lst), Missing)
                           = KM.Add (Kept, A (I)),
          Post => KM.Add (Models.Occurrences (R, Lst), Missing)
                  = KM.Add (Kept, R (I));
   --  The same, for a descent that has already handed one key -- the extracted
   --  minimum -- to the caller: the array is short of it by exactly one

   ------------------------
   -- Layer arithmetic   --
   ------------------------

   subtype Small_Natural is Natural range 0 .. 46_340;
   --  A range on which a product of two values still fits in an Integer

   procedure Lemma_Mult_Monotonic (A, B, C, D : Small_Natural)
     with Ghost,
          Pre  => A <= B and then C <= D,
          Post => A * C <= B * D;
   --  Products of naturals grow with both factors. Multiplication is where
   --  the provers need the most help, so the fact is isolated here and every
   --  comparison of triangular numbers goes through it.

   procedure Lemma_Small_Layer (L : Layer_Count)
     with Ghost,
          Pre  => L * (L + 1) <= Double_Capacity,
          Post => L < Max_Layer;
   --  A layer that starts within the capacity of a heap is far from the last
   --  layer the bound allows, so a layer number can always be incremented

   procedure Lemma_Tri_Monotonic (L1, L2 : Layer_Count)
     with Ghost,
          Pre  => L1 <= L2,
          Post => Tri (L1) <= Tri (L2);

   procedure Lemma_Layer (I : Index; L : Layer_Index; B : Extended_Index)
     with Ghost,
          Pre  => B = Tri (L - 1) and then B < I and then I <= B + L,
          Post => Layer_Of (I) = L and then Position (I) = I - B;
   --  Recognising the layer of an index from a pair of bounds. The layers
   --  partition the indices, so exhibiting one that contains I identifies it.

   procedure Lemma_Parents (I : Index; L : Layer_Index; B : Extended_Index)
     with Ghost,
          Pre  => B = Tri (L - 1) and then B < I and then I <= B + L,
          Post => Low_Parent (I) = (if I - B >= 2 then I - L else 0)
                  and then High_Parent (I) =
                            (if I - B < L then I - L + 1 else 0);
   --  The parents of a node, in terms of its layer rather than of the ghost
   --  function that computes that layer

   procedure Lemma_Children
     (I : Index; L : Layer_Index; B : Extended_Index; J : Index)
     with Ghost,
          Pre  => B = Tri (L - 1)
                  and then B < I
                  and then I <= B + L
                  and then (Low_Parent (J) = I or else High_Parent (J) = I),
          Post => J = I + L or else J = I + L + 1;
   --  A node has no children other than the two immediately below it

   procedure Lemma_Child_Set
     (H : Heap; I : Index; L : Layer_Index; B : Extended_Index)
     with Ghost,
          Pre  => B = Tri (L - 1) and then B < I and then I <= B + L,
          Post => (for all J in 2 .. H.Last =>
                     (if Low_Parent (J) = I or else High_Parent (J) = I
                      then J = I + L or else J = I + L + 1));
   --  The same statement about every node of a heap at once, so that a proof
   --  can talk about the children of a node without naming them

   procedure Lemma_Is_Child
     (I : Index; L : Layer_Index; B : Extended_Index; J : Index)
     with Ghost,
          Pre  => B = Tri (L - 1)
                  and then B < I
                  and then I <= B + L
                  and then (J = I + L or else J = I + L + 1),
          Post => Low_Parent (J) = I or else High_Parent (J) = I;
   --  ... and both of those really are its children

   procedure Lemma_Has_Parent (I : Index)
     with Ghost,
          Pre  => I >= 2,
          Post => Low_Parent (I) > 0 or else High_Parent (I) > 0;
   --  Only the first node has no parent at all

   -----------------------
   -- Lemma_Hole_Filled --
   -----------------------

   procedure Lemma_Hole_Filled
     (A, R : Key_Array; I : Index; Lst : Extended_Index; Kept : KM.Multiset)
   is
   begin
      --  Overwriting the hole exchanges the key it held for the new one; the
      --  discarded key cancels out on both sides.

      Models.Lemma_Set (A, R, I, Lst);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (A, Lst), KM.Add (Kept, A (I)), R (I));
      Models.Lemma_Add_Commutes (Kept, A (I), R (I));
      Models.Lemma_Add_Cancels
        (Models.Occurrences (R, Lst), KM.Add (Kept, R (I)), A (I));
   end Lemma_Hole_Filled;

   ----------------------
   -- Lemma_Hole_Moved --
   ----------------------

   procedure Lemma_Hole_Moved
     (A, R : Key_Array; I : Index; Lst : Extended_Index;
      Missing : Key_Type; Kept : KM.Multiset)
   is
   begin
      Models.Lemma_Set (A, R, I, Lst);
      Models.Lemma_Add_Congruent
        (KM.Add (Models.Occurrences (R, Lst), A (I)),
         KM.Add (Models.Occurrences (A, Lst), R (I)),
         Missing);
      Models.Lemma_Add_Commutes (Models.Occurrences (R, Lst), A (I), Missing);
      Models.Lemma_Add_Commutes (Models.Occurrences (A, Lst), R (I), Missing);
      Models.Lemma_Add_Congruent
        (KM.Add (Models.Occurrences (A, Lst), Missing),
         KM.Add (Kept, A (I)),
         R (I));
      Models.Lemma_Add_Commutes (Kept, A (I), R (I));
      Models.Lemma_Add_Cancels
        (KM.Add (Models.Occurrences (R, Lst), Missing),
         KM.Add (Kept, R (I)),
         A (I));
   end Lemma_Hole_Moved;

   ---------------------------
   -- Lemma_Mult_Monotonic  --
   ---------------------------

   procedure Lemma_Mult_Monotonic (A, B, C, D : Small_Natural) is
   begin
      pragma Assert (A * C <= B * C);
      pragma Assert (B * C <= B * D);
   end Lemma_Mult_Monotonic;

   -----------------------
   -- Lemma_Small_Layer --
   -----------------------

   procedure Lemma_Small_Layer (L : Layer_Count) is
   begin
      if L >= Max_Layer then
         Lemma_Mult_Monotonic (Max_Layer, L, Max_Layer + 1, L + 1);
         pragma Assert (Max_Layer * (Max_Layer + 1) <= L * (L + 1));
         pragma Assert (False);
      end if;
   end Lemma_Small_Layer;

   -------------------------
   -- Lemma_Tri_Monotonic --
   -------------------------

   procedure Lemma_Tri_Monotonic (L1, L2 : Layer_Count) is
   begin
      Lemma_Mult_Monotonic (L1, L2, L1 + 1, L2 + 1);
   end Lemma_Tri_Monotonic;

   ---------
   -- Tri --
   ---------

   function Tri (L : Layer_Count) return Natural is
      Acc : Natural := 0;
   begin
      for M in 1 .. L loop
         Lemma_Mult_Monotonic (M - 1, Max_Layer, M, Max_Layer + 1);
         Acc := Acc + M;

         pragma Loop_Invariant (2 * Acc = M * (M + 1));
      end loop;

      return Acc;
   end Tri;

   --------------
   -- Layer_Of --
   --------------

   function Layer_Of (I : Index) return Layer_Index is
      L : Layer_Index := 1;
   begin
      while Tri (L) < I loop
         Lemma_Small_Layer (L);
         L := L + 1;

         pragma Loop_Invariant (Tri (L - 1) < I);
         pragma Loop_Variant (Increases => L);
      end loop;

      return L;
   end Layer_Of;

   -----------------
   -- Lemma_Layer --
   -----------------

   procedure Lemma_Layer (I : Index; L : Layer_Index; B : Extended_Index) is
      M : constant Layer_Index := Layer_Of (I) with Ghost;
   begin
      pragma Assert (Tri (L) = B + L);

      if M < L then
         Lemma_Tri_Monotonic (M, L - 1);
      elsif M > L then
         Lemma_Tri_Monotonic (L, M - 1);
      end if;
   end Lemma_Layer;

   -------------------
   -- Lemma_Parents --
   -------------------

   procedure Lemma_Parents (I : Index; L : Layer_Index; B : Extended_Index) is
   begin
      Lemma_Layer (I, L, B);
   end Lemma_Parents;

   --------------------
   -- Lemma_Children --
   --------------------

   procedure Lemma_Children
     (I : Index; L : Layer_Index; B : Extended_Index; J : Index)
   is
      M : constant Layer_Index := Layer_Of (J) with Ghost;
      Q : constant Positive := Position (J) with Ghost;
   begin
      Lemma_Layer (I, L, B);

      pragma Assert (M >= 2);
      pragma Assert (Tri (M - 1) = Tri (M - 2) + (M - 1));

      if Low_Parent (J) = I then
         --  I sits one layer up, at position Q - 1
         pragma Assert (Q >= 2);
         pragma Assert (I = Tri (M - 2) + Q - 1);
         Lemma_Layer (I, M - 1, Tri (M - 2));
      else
         --  I sits one layer up, at position Q
         pragma Assert (Q < M);
         pragma Assert (I = Tri (M - 2) + Q);
         Lemma_Layer (I, M - 1, Tri (M - 2));
      end if;
   end Lemma_Children;

   ---------------------
   -- Lemma_Child_Set --
   ---------------------

   procedure Lemma_Child_Set
     (H : Heap; I : Index; L : Layer_Index; B : Extended_Index) is
   begin
      for J in 2 .. H.Last loop
         if Low_Parent (J) = I or else High_Parent (J) = I then
            Lemma_Children (I, L, B, J);
         end if;

         pragma Loop_Invariant
           (for all M in 2 .. J =>
              (if Low_Parent (M) = I or else High_Parent (M) = I
               then M = I + L or else M = I + L + 1));
      end loop;
   end Lemma_Child_Set;

   --------------------
   -- Lemma_Is_Child --
   --------------------

   procedure Lemma_Is_Child
     (I : Index; L : Layer_Index; B : Extended_Index; J : Index)
   is
   begin
      Lemma_Layer (I, L, B);
      Lemma_Small_Layer (L);

      --  Both indices fall in the layer that starts where this one ends, at
      --  the position of I and at the one after it.

      pragma Assert (Tri (L) = B + L);
      pragma Assert (Tri (L + 1) = Tri (L) + L + 1);
      Lemma_Layer (J, L + 1, Tri (L));
   end Lemma_Is_Child;

   ----------------------
   -- Lemma_Has_Parent --
   ----------------------

   procedure Lemma_Has_Parent (I : Index) is
      L : constant Layer_Index := Layer_Of (I) with Ghost;
   begin
      pragma Assert (L >= 2);
   end Lemma_Has_Parent;

   ---------------------------
   -- Lemma_Root_Is_Minimum --
   ---------------------------

   procedure Lemma_Root_Is_Minimum (H : Heap) is
   begin
      --  Induction on the index: both parents of I are smaller indices, so by
      --  the time I is reached the first node has already been shown to be
      --  below whichever of them dominates I.

      for I in 1 .. H.Last loop
         if I >= 2 then
            Lemma_Has_Parent (I);
         end if;

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
         pragma Loop_Invariant (for some J in 1 .. I => Result = H.Keys (J));
      end loop;

      return Result;
   end Min_Of;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last  := 0;
      H.Layer := 1;
      H.Base  := 0;
   end Clear;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Start : constant KM.Multiset := Model (H) with Ghost;
      --  The model before the insertion

      Before : Key_Array := H.Keys with Ghost;
      --  Snapshot of the array taken just before each single-slot write, so
      --  that Models.Lemma_Set can relate the two states. SPARK does not
      --  allow declaring it inside the loop body, hence the hoisting.

      Hole : Index := H.Last + 1;
      --  The new key conceptually sits in a hole that travels up as long as
      --  one of the parents is strictly greater. Moving the hole rather than
      --  swapping halves the number of writes: the key itself is only stored
      --  once, when its final position is known.

      L : Layer_Index := H.Layer;
      B : Extended_Index := H.Base;
      --  The layer holding the hole, and the index just before that layer

      Pos : Positive;
      Up  : Index;
   begin
      H.Last := Hole;

      --  Keep the description of the next free slot up to date: if the hole
      --  has just taken the last index of its layer, the following insertion
      --  opens the next one.

      if Hole = B + L then
         Lemma_Small_Layer (L);
         pragma Assert (Tri (L) = B + L);
         H.Base  := B + L;
         H.Layer := L + 1;
      end if;

      pragma Assert (Layers_Valid (H));

      while L > 1 loop
         Pos := Hole - B;

         --  A layer starts far enough into the array for the two indices one
         --  layer up to exist, which is what makes the arithmetic below stay
         --  inside the array.

         Lemma_Mult_Monotonic (2, L, L - 1, L - 1);
         pragma Assert (B >= L - 1);

         --  Move down whichever parent is the larger; the other one is then
         --  small enough to stay above the key that lands in the hole.

         if Pos = 1 then
            Up := Hole - L + 1;
         elsif Pos = L then
            Up := Hole - L;
         elsif H.Keys (Hole - L) >= H.Keys (Hole - L + 1) then
            Up := Hole - L;
         else
            Up := Hole - L + 1;
         end if;

         Lemma_Parents (Hole, L, B);

         pragma Assert
           (if Low_Parent (Hole) > 0
            then H.Keys (Low_Parent (Hole)) <= H.Keys (Up));
         pragma Assert
           (if High_Parent (Hole) > 0
            then H.Keys (High_Parent (Hole)) <= H.Keys (Up));

         exit when H.Keys (Up) <= K;

         Before := H.Keys;
         H.Keys (Hole) := H.Keys (Up);

         --  The hole now holds the key that was at Up, and the model is
         --  again Start plus whatever the hole holds.

         Lemma_Hole_Filled (Before, H.Keys, Hole, H.Last, Start);

         Hole := Up;
         L := L - 1;
         B := B - L;

         pragma Loop_Invariant (Hole <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (Layers_Valid (H));

         --  The hole is at position Hole - B of layer L
         pragma Loop_Invariant (B = Tri (L - 1));
         pragma Loop_Invariant (B < Hole and then Hole <= B + L);

         --  The ordering holds everywhere except at the hole, whose content
         --  is about to be overwritten.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if J /= Hole
               then (if Low_Parent (J) > 0
                     then H.Keys (Low_Parent (J)) <= H.Keys (J))
                    and then (if High_Parent (J) > 0
                              then H.Keys (High_Parent (J)) <= H.Keys (J))));

         --  The parents of the hole still dominate the children of the hole,
         --  which is what keeps the ordering valid when the hole moves up.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
               then (if Low_Parent (Hole) > 0
                     then H.Keys (Low_Parent (Hole)) <= H.Keys (J))
                    and then (if High_Parent (Hole) > 0
                              then H.Keys (High_Parent (Hole)) <= H.Keys (J))));

         --  The key being inserted fits in the hole as far as the children of
         --  the hole are concerned.
         pragma Loop_Invariant
           (for all J in 2 .. H.Last =>
              (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
               then K <= H.Keys (J)));

         --  Model: everything the array holds is Start plus the stale key
         --  sitting in the hole.
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, H.Last) = KM.Add (Start, H.Keys (Hole)));

         pragma Loop_Variant (Decreases => Hole);
      end loop;

      pragma Assert
        (if Low_Parent (Hole) > 0 then H.Keys (Low_Parent (Hole)) <= K);
      pragma Assert
        (if High_Parent (Hole) > 0 then H.Keys (High_Parent (Hole)) <= K);

      Before := H.Keys;
      H.Keys (Hole) := K;

      --  Nothing outside the hole and its children moved, and the key that
      --  landed in the hole sits between its parents and its children.

      pragma Assert
        (for all J in 2 .. H.Last =>
           (if J /= Hole
               and then Low_Parent (J) /= Hole
               and then High_Parent (J) /= Hole
            then (if Low_Parent (J) > 0
                  then H.Keys (Low_Parent (J)) <= H.Keys (J))
                 and then (if High_Parent (J) > 0
                           then H.Keys (High_Parent (J)) <= H.Keys (J))));
      pragma Assert
        (for all J in 2 .. H.Last =>
           (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
            then (if Low_Parent (J) > 0
                  then H.Keys (Low_Parent (J)) <= H.Keys (J))
                 and then (if High_Parent (J) > 0
                           then H.Keys (High_Parent (J)) <= H.Keys (J))));
      pragma Assert (Ordered (H));

      Lemma_Hole_Filled (Before, H.Keys, Hole, H.Last, Start);
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Moved : constant Key_Type := H.Keys (H.Last);
      --  The key of the last node, which has to be reinserted somewhere along
      --  a path leading down from the first one

      Before : Key_Array := H.Keys with Ghost;
      --  See the comment on the homonym in Insert

      Hole : Index := 1;
      L    : Layer_Index := 1;
      B    : Extended_Index := 0;

      Down : Index;
   begin
      Lemma_Root_Is_Minimum (H);

      K := H.Keys (1);

      --  The slot that is about to be freed becomes the next free one. When
      --  it is the first slot of its layer, the description of the next free
      --  slot moves back to the end of the layer before it.

      if H.Base = H.Last then
         H.Layer := H.Layer - 1;
         H.Base  := H.Base - H.Layer;
      end if;

      H.Last := H.Last - 1;

      pragma Assert (Layers_Valid (H));

      declare
         Start : constant KM.Multiset := Model (H) with Ghost;
         --  The model of the array with the last slot dropped: the full model
         --  is Start plus Moved, by definition of Occurrences.
      begin
         loop
            exit when Hole + L > H.Last;
            --  Past that point the hole has no children and the search is over

            --  Move up whichever child is the smaller
            Down := Hole + L;

            if Down < H.Last and then H.Keys (Down + 1) < H.Keys (Down) then
               Down := Down + 1;
            end if;

            Lemma_Is_Child (Hole, L, B, Hole + L);

            if Hole + L + 1 <= H.Last then
               Lemma_Is_Child (Hole, L, B, Hole + L + 1);
            end if;

            Lemma_Child_Set (H, Hole, L, B);

            pragma Assert
              (for all J in 2 .. H.Last =>
                 (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
                  then H.Keys (Down) <= H.Keys (J)));

            exit when H.Keys (Down) >= Moved;

            Before := H.Keys;
            H.Keys (Hole) := H.Keys (Down);

            --  Same argument as in Insert, except that the array is one key
            --  short: K has already been handed to the caller.

            Lemma_Hole_Moved (Before, H.Keys, Hole, H.Last, K, Start);

            B := B + L;
            L := L + 1;
            Hole := Down;

            pragma Loop_Invariant (Hole <= H.Last);
            pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
            pragma Loop_Invariant (Layers_Valid (H));
            pragma Loop_Invariant
              (Before'First = 1 and Before'Last = H.Keys'Last);

            pragma Loop_Invariant (B = Tri (L - 1));
            pragma Loop_Invariant (B < Hole and then Hole <= B + L);

            --  The ordering holds everywhere except at the hole
            pragma Loop_Invariant
              (for all J in 2 .. H.Last =>
                 (if J /= Hole
                  then (if Low_Parent (J) > 0
                        then H.Keys (Low_Parent (J)) <= H.Keys (J))
                       and then (if High_Parent (J) > 0
                                 then H.Keys (High_Parent (J)) <= H.Keys (J))));

            --  The parents of the hole dominate the children of the hole
            pragma Loop_Invariant
              (for all J in 2 .. H.Last =>
                 (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
                  then (if Low_Parent (Hole) > 0
                        then H.Keys (Low_Parent (Hole)) <= H.Keys (J))
                       and then (if High_Parent (Hole) > 0
                                 then H.Keys (High_Parent (Hole)) <= H.Keys (J))));

            --  The key being moved down is still large enough for the hole
            pragma Loop_Invariant
              ((if Low_Parent (Hole) > 0
                then H.Keys (Low_Parent (Hole)) <= Moved)
               and then (if High_Parent (Hole) > 0
                         then H.Keys (High_Parent (Hole)) <= Moved));

            --  Model: the array still holds Start, except that the extracted
            --  key K has been replaced by whatever stale key is in the hole.
            pragma Loop_Invariant
              (KM.Add (Models.Occurrences (H.Keys, H.Last), K)
               = KM.Add (Start, H.Keys (Hole)));

            pragma Loop_Variant (Increases => Hole);
         end loop;

         if H.Last > 0 then
            Lemma_Child_Set (H, Hole, L, B);

            pragma Assert
              (for all J in 2 .. H.Last =>
                 (if Low_Parent (J) = Hole or else High_Parent (J) = Hole
                  then Moved <= H.Keys (J)));

            Before := H.Keys;
            H.Keys (Hole) := Moved;

            Lemma_Hole_Moved (Before, H.Keys, Hole, H.Last, K, Start);
         end if;
      end;
   end Extract_Min;

end Heaps.Beap;
