--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Block_Min with SPARK_Mode is

   package KM renames Key_Multisets;

   procedure Recompute_Block (H : in out Heap; B : Index)
     with Pre  => B <= Blocks_For (H.Last),
          Post => H.Last = H.Last'Old
                  and then H.Keys = H.Keys'Old
                  and then Block_Valid (H, B)
                  and then (for all C in H.Winners'Range =>
                              (if C /= B then
                                 H.Winners (C) = H'Old.Winners (C)));

   procedure Locate_Min (H : Heap; Position : out Index)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Position <= H.Last
                  and then Is_Minimum (H, H.Keys (Position));

   procedure Lemma_Winner_Is_Minimum (H : Heap; Best : Index)
     with Ghost,
          Pre  => not Is_Empty (H)
                  and then Is_Heap (H)
                  and then Best <= Blocks_For (H.Last)
                  and then (for all B in 1 .. Blocks_For (H.Last) =>
                              H.Keys (H.Winners (Best))
                                <= H.Keys (H.Winners (B))),
          Post => Is_Minimum (H, H.Keys (H.Winners (Best)));

   procedure Lemma_Block_Valid (H : Heap; B : Index)
     with Ghost,
          Pre  => Is_Heap (H) and then B <= Blocks_For (H.Last),
          Post => Block_Valid (H, B);

   procedure Lemma_Insert_Preserves_Heap
     (Old_H, H : Heap; Changed : Index)
     with Ghost,
          Pre  => Is_Heap (Old_H)
                  and then H.Last = Old_H.Last + 1
                  and then Changed = Block_Number (H.Last)
                  and then Block_Valid (H, Changed)
                  and then (for all I in 1 .. Old_H.Last =>
                              H.Keys (I) = Old_H.Keys (I))
                  and then (for all B in 1 .. Blocks_For (Old_H.Last) =>
                              (if B /= Changed then
                                 H.Winners (B) = Old_H.Winners (B))),
          Post => Is_Heap (H);

   procedure Lemma_Extract_Preserves_Heap
     (Old_H, H : Heap; Changed, Last_Block : Index)
     with Ghost,
          Pre  => Is_Heap (Old_H)
                  and then Old_H.Last = H.Last + 1
                  and then Last_Block = Block_Number (Old_H.Last)
                  and then (for all B in 1 .. Blocks_For (H.Last) =>
                              (if B = Changed or else B = Last_Block
                               then Block_Valid (H, B)
                               else H.Winners (B) = Old_H.Winners (B)))
                  and then (for all I in 1 .. H.Last =>
                              (if Block_Number (I) /= Changed then
                                 H.Keys (I) = Old_H.Keys (I))),
          Post => Is_Heap (H);

   -----------------------------
   -- Lemma_Winner_Is_Minimum --
   -----------------------------

   procedure Lemma_Winner_Is_Minimum (H : Heap; Best : Index) is
   begin
      for I in 1 .. H.Last loop
         pragma Assert (Block_Number (I) <= Blocks_For (H.Last));
         pragma Assert (Block_Valid (H, Block_Number (I)));

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              H.Keys (H.Winners (Best)) <= H.Keys (J));
      end loop;
   end Lemma_Winner_Is_Minimum;

   -----------------------
   -- Lemma_Block_Valid --
   -----------------------

   procedure Lemma_Block_Valid (H : Heap; B : Index) is null;

   ---------------------------------
   -- Lemma_Insert_Preserves_Heap --
   ---------------------------------

   procedure Lemma_Insert_Preserves_Heap
     (Old_H, H : Heap; Changed : Index)
   is
   begin
      for B in 1 .. Blocks_For (H.Last) loop
         if B /= Changed then
            pragma Assert (B <= Blocks_For (Old_H.Last));
            pragma Assert (Block_Valid (Old_H, B));
            pragma Assert
              (Block_Last (B, H.Last) = Block_Last (B, Old_H.Last));
            pragma Assert (Block_Valid (H, B));
         end if;

         pragma Loop_Invariant
           (for all C in 1 .. B => Block_Valid (H, C));
      end loop;
   end Lemma_Insert_Preserves_Heap;

   ----------------------------------
   -- Lemma_Extract_Preserves_Heap --
   ----------------------------------

   procedure Lemma_Extract_Preserves_Heap
     (Old_H, H : Heap; Changed, Last_Block : Index)
   is
   begin
      for B in 1 .. Blocks_For (H.Last) loop
         if B /= Changed and then B /= Last_Block then
            pragma Assert (B <= Blocks_For (Old_H.Last));
            pragma Assert (Block_Valid (Old_H, B));
            pragma Assert
              (Block_Last (B, H.Last) = Block_Last (B, Old_H.Last));
            pragma Assert (Block_Valid (H, B));
         end if;

         pragma Loop_Invariant
           (for all C in 1 .. B => Block_Valid (H, C));
      end loop;
   end Lemma_Extract_Preserves_Heap;

   ---------------------
   -- Recompute_Block --
   ---------------------

   procedure Recompute_Block (H : in out Heap; B : Index) is
      First  : constant Index := Block_First (B);
      Last   : constant Index := Block_Last (B, H.Last);
      Winner : Index := First;
   begin
      for I in First + 1 .. Last loop
         if H.Keys (I) < H.Keys (Winner) then
            Winner := I;
         end if;

         pragma Loop_Invariant (Winner in First .. I);
         pragma Loop_Invariant
           (for all J in First .. I => H.Keys (Winner) <= H.Keys (J));
      end loop;

      H.Winners (B) := Winner;
   end Recompute_Block;

   ----------------
   -- Locate_Min --
   ----------------

   procedure Locate_Min (H : Heap; Position : out Index) is
      Best : Index := 1;
   begin
      for B in 2 .. Blocks_For (H.Last) loop
         if H.Keys (H.Winners (B)) < H.Keys (H.Winners (Best)) then
            Best := B;
         end if;

         pragma Loop_Invariant (Best <= B);
         pragma Loop_Invariant
           (for all C in 1 .. B =>
              H.Keys (H.Winners (Best)) <= H.Keys (H.Winners (C)));
      end loop;

      Lemma_Winner_Is_Minimum (H, Best);
      Position := H.Winners (Best);
   end Locate_Min;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
      Position : Index;
   begin
      Locate_Min (H, Position);
      return H.Keys (Position);
   end Peek_Min;

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

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;
      Old_H  : constant Heap := H with Ghost;
      Slot   : constant Index := H.Last + 1;
      B      : constant Index := Block_Number (Slot);
   begin
      H.Last := Slot;
      H.Keys (Slot) := K;

      if Slot = Block_First (B) then
         H.Winners (B) := Slot;
         pragma Assert (Block_Last (B, H.Last) = Slot);
      else
         pragma Assert (B <= Blocks_For (Old_H.Last));
         Lemma_Block_Valid (Old_H, B);
         pragma Assert (H.Winners (B) = Old_H.Winners (B));
         pragma Assert (H.Winners (B) in Block_First (B) .. Slot - 1);

         if K < H.Keys (H.Winners (B)) then
            H.Winners (B) := Slot;
         end if;
      end if;

      pragma Assert (Block_Valid (H, B));
      Lemma_Insert_Preserves_Heap (Old_H, H, B);

      Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Before, H.Last - 1),
         Models.Occurrences (H.Keys, H.Last - 1), K);
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

         --  Insert has already restored the directory and told us the model
         --  gained one key; all that is left is to carry that Add out through
         --  the sum accumulated so far.

         Models.Lemma_Sum_Add
           (M0, Models.Occurrences (From.Keys, I - 1), From.Keys (I));
         Models.Lemma_Sum_Empty (M0);

         pragma Loop_Invariant (Is_Heap (Into));
         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant
           (Model (Into) = M0 + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (M0);
      end if;

      From.Last := 0;

      --  Emptying From resets its directory implicitly: Blocks_For (0) is
      --  zero, so Is_Heap holds over an empty range of blocks.
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Before         : constant Key_Array := H.Keys with Ghost;
      Old_H          : constant Heap := H with Ghost;
      Old_Model      : constant KM.Multiset := Model (H) with Ghost;
      Remaining_Model : KM.Multiset with Ghost;
      Remaining_Keys  : Key_Array := H.Keys with Ghost;

      Min_At     : Index;
      Old_Last   : constant Index := H.Last;
      Last_Block : constant Index := Block_Number (Old_Last);
      Min_Block  : Index;
   begin
      Locate_Min (H, Min_At);
      K := H.Keys (Min_At);
      Min_Block := Block_Number (Min_At);

      H.Keys (Min_At) := H.Keys (Old_Last);

      if Min_At < Old_Last then
         Models.Lemma_Set (Before, H.Keys, Min_At, Old_Last - 1);
      else
         Models.Lemma_Same_Prefix (Before, H.Keys, Old_Last - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (H.Keys, Old_Last - 1),
            Models.Occurrences (Before, Old_Last - 1), K);
      end if;

      H.Last := Old_Last - 1;
      Remaining_Model := Model (H);
      Remaining_Keys := H.Keys;
      pragma Assert (Old_Model = KM.Add (Remaining_Model, K));

      if Min_At < Old_Last then
         Recompute_Block (H, Min_Block);
      end if;

      if Last_Block <= Blocks_For (H.Last)
        and then (Min_At = Old_Last or else Last_Block /= Min_Block)
      then
         Recompute_Block (H, Last_Block);
      end if;

      pragma Assert
        (for all B in 1 .. Blocks_For (H.Last) =>
           (if B = Min_Block or else B = Last_Block
            then Block_Valid (H, B)
            else H.Winners (B) = Old_H.Winners (B)));
      Lemma_Extract_Preserves_Heap (Old_H, H, Min_Block, Last_Block);

      Models.Lemma_Same_Prefix (Remaining_Keys, H.Keys, H.Last);
      pragma Assert (Model (H) = Remaining_Model);
      Models.Lemma_Add_Congruent (Model (H), Remaining_Model, K);
   end Extract_Min;

end Heaps.Block_Min;
