--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Sorted_Linked with SPARK_Mode is

   package KM renames Key_Multisets;

   procedure Lemma_Head_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Sorted (H),
          Post => Is_Minimum (H, H.Keys (H.Head));

   ---------------------------
   -- Lemma_Head_Is_Minimum --
   ---------------------------

   procedure Lemma_Head_Is_Minimum (H : Heap) is
   begin
      for P in reverse 1 .. H.Last loop
         if P < H.Last then
            pragma Assert (H.Keys (H.Order (P + 1)) <= H.Keys (H.Order (P)));
         end if;

         pragma Loop_Invariant
           (for all Q in P .. H.Last =>
              H.Keys (H.Head) <= H.Keys (H.Order (Q)));
      end loop;

      for I in 1 .. H.Last loop
         pragma Assert (Node_Valid (H, I));
         pragma Assert (H.Order (H.Links (I).Position) = I);

         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (H.Head) <= H.Keys (J));
      end loop;
   end Lemma_Head_Is_Minimum;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
      H.Head := 0;
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
   begin
      Lemma_Head_Is_Minimum (H);
      return H.Keys (H.Head);
   end Peek_Min;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Old      : constant Heap := H with Ghost;
      Old_Last : constant Extended_Index := H.Last;
      Slot     : constant Index := H.Last + 1;

      Current : Extended_Index := H.Head;
      P       : Extended_Index := H.Last;
      --  Current is Order (P); everything already passed is <= K.

      New_Position : Index;
      Node         : Index;
   begin
      while Current /= 0 and then H.Keys (Current) <= K loop
         pragma Assert (P > 0);
         pragma Assert (Current = H.Order (P));

         Current := H.Links (Current).Next;
         P := P - 1;

         pragma Loop_Invariant (H = Old);
         pragma Loop_Invariant (P <= Old_Last);
         pragma Loop_Invariant
           (Current = (if P = 0 then 0 else Old.Order (P)));
         pragma Loop_Invariant
           (for all Q in P + 1 .. Old_Last => Old.Keys (Old.Order (Q)) <= K);
         pragma Loop_Variant (Decreases => P);
      end loop;

      New_Position := P + 1;

      pragma Assert
        (for all Q in New_Position .. Old_Last => Old.Keys (Old.Order (Q)) <= K);
      pragma Assert
        (if P > 0 then K < Old.Keys (Old.Order (P)));

      --  Open one position in the inverse rank table. Going backwards keeps
      --  every source entry intact until it has been copied.

      for Q in reverse New_Position .. Old_Last loop
         H.Order (Q + 1) := H.Order (Q);

         pragma Loop_Invariant
           (for all R in Q + 1 .. Old_Last + 1 => H.Order (R) = Old.Order (R - 1));
         pragma Loop_Invariant
           (for all R in 1 .. Q => H.Order (R) = Old.Order (R));
      end loop;

      H.Order (New_Position) := Slot;
      H.Keys (Slot) := K;
      H.Last := Old_Last + 1;
      H.Head := H.Order (H.Last);

      --  Rebuild the two links and the inverse rank at each active node.
      --  Insertion is linear already, so this certificate maintenance does
      --  not change its asymptotic cost.

      for Q in 1 .. H.Last loop
         Node := H.Order (Q);
         H.Links (Node) :=
           (Prev     => (if Q = H.Last then 0 else H.Order (Q + 1)),
            Next     => (if Q = 1 then 0 else H.Order (Q - 1)),
            Position => Q);

         pragma Loop_Invariant
           (for all R in 1 .. Q =>
              H.Order (R) in 1 .. H.Last
              and then Position_Valid (H, R));
      end loop;

      pragma Assert
        (for all Q in 1 .. H.Last =>
           H.Order (Q)
             = (if Q = New_Position then Slot
                elsif Q < New_Position then Old.Order (Q)
                else Old.Order (Q - 1)));

      pragma Assert
        (for all Q in 1 .. H.Last =>
           Position_Valid (H, Q));

      --  Old Order was a permutation of the old dense prefix. Inserting the new
      --  physical slot at one position preserves that inverse relation.

      for I in 1 .. H.Last loop
         if I = Slot then
            pragma Assert (H.Order (H.Links (I).Position) = I);
         else
            pragma Assert (I <= Old_Last);
            pragma Assert (Node_Valid (Old, I));
            pragma Assert (Old.Order (Old.Links (I).Position) = I);
            pragma Assert
              (H.Links (I).Position
                 = (if Old.Links (I).Position < New_Position
                    then Old.Links (I).Position
                    else Old.Links (I).Position + 1));
            pragma Assert (H.Order (H.Links (I).Position) = I);
         end if;

         pragma Assert (Node_Valid (H, I));
         pragma Loop_Invariant
           (for all J in 1 .. I => Node_Valid (H, J));
      end loop;

      --  The rank sequence is the old one with K inserted between the passed
      --  prefix (<= K) and Current (> K).

      for Q in 2 .. H.Last loop
         if Q = New_Position then
            pragma Assert
              (if Q > 1 then K <= H.Keys (H.Order (Q - 1)));
         elsif Q = New_Position + 1 then
            pragma Assert (H.Keys (H.Order (Q)) <= K);
         else
            declare
               Old_Q : constant Index :=
                 (if Q < New_Position then Q else Q - 1);
            begin
               pragma Assert (Old_Q in 2 .. Old_Last);
               pragma Assert
                 (Old.Keys (Old.Order (Old_Q))
                    <= Old.Keys (Old.Order (Old_Q - 1)));
            end;
         end if;

         pragma Loop_Invariant
           (for all R in 2 .. Q =>
              H.Keys (H.Order (R)) <= H.Keys (H.Order (R - 1)));
      end loop;

      pragma Assert (Is_Sorted (H));

      Models.Lemma_Same_Prefix (Old.Keys, H.Keys, Old_Last);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Old.Keys, Old_Last),
         Models.Occurrences (H.Keys, Old_Last), K);
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Old       : constant Heap := H with Ghost;
      Old_Model : constant KM.Multiset := Model (H) with Ghost;
      Old_Last  : constant Index := H.Last;
      Removed   : constant Index := H.Head;
      Moved     : constant Index := H.Last;
      Moved_Pos : Extended_Index := 0;
      Remaining_Keys  : Key_Array := H.Keys with Ghost;
      Remaining_Model : KM.Multiset with Ghost;
   begin
      K := Peek_Min (H);
      pragma Assert (K = H.Keys (Removed));

      if Removed /= Moved then
         Moved_Pos := H.Links (Moved).Position;
         pragma Assert (Position_Valid (H, Moved_Pos));
         H.Keys (Removed) := H.Keys (Moved);
         H.Order (Moved_Pos) := Removed;

         --  Reconstruct the moved node's links from its rank. Copying its
         --  old Prev verbatim is wrong when it immediately followed the
         --  removed head: that old predecessor is the slot now occupied by
         --  the moved node itself.

         H.Links (Removed) :=
           (Prev     =>
              (if Moved_Pos = Old_Last - 1
               then 0
               else H.Order (Moved_Pos + 1)),
            Next     =>
              (if Moved_Pos = 1
               then 0
               else H.Order (Moved_Pos - 1)),
            Position => Moved_Pos);

         if H.Links (Removed).Prev /= 0 then
            H.Links (H.Links (Removed).Prev).Next := Removed;
         end if;

         if H.Links (Removed).Next /= 0 then
            H.Links (H.Links (Removed).Next).Prev := Removed;
         end if;
      end if;

      H.Last := Old_Last - 1;
      H.Head := (if H.Last = 0 then 0 else H.Order (H.Last));

      if H.Last > 0 then
         H.Links (H.Head).Prev := 0;
      end if;

      --  The remaining rank table is unchanged except that the physical last
      --  node may now be represented by the removed head's old slot.

      pragma Assert
        (for all P in 1 .. H.Last =>
           H.Order (P)
             = (if Removed /= Moved and then P = Moved_Pos
                then Removed
                else Old.Order (P)));

      pragma Assert
        (for all P in 1 .. H.Last =>
           H.Keys (H.Order (P)) = Old.Keys (Old.Order (P)));

      --  Spell out the four link cases introduced by moving the physical
      --  last node: the moved node itself, its two neighbours, and the new
      --  head. Every other link is unchanged.

      for P in 1 .. H.Last loop
         pragma Assert (H.Order (P) in 1 .. H.Last);

         if Removed /= Moved and then P = Moved_Pos then
            pragma Assert (H.Order (P) = Removed);
            pragma Assert (H.Links (H.Order (P)).Position = P);
         else
            pragma Assert (H.Order (P) = Old.Order (P));
            pragma Assert (H.Links (H.Order (P)).Position = P);
         end if;

         if P = H.Last then
            pragma Assert (H.Order (P) = H.Head);
            pragma Assert (H.Links (H.Order (P)).Prev = 0);
         elsif Removed /= Moved and then P + 1 = Moved_Pos then
            pragma Assert (H.Order (P + 1) = Removed);
            pragma Assert (H.Links (Removed).Next = H.Order (P));
            pragma Assert (H.Links (H.Order (P)).Prev = Removed);
         else
            pragma Assert
              (H.Links (H.Order (P)).Prev = H.Order (P + 1));
         end if;

         if P = 1 then
            if Removed /= Moved and then P = Moved_Pos then
               pragma Assert (H.Order (P) = Removed);
               pragma Assert (H.Links (Removed).Next = 0);
            else
               pragma Assert (H.Order (P) = Old.Order (P));
               pragma Assert (Position_Valid (Old, P));
               pragma Assert (Old.Links (Old.Order (P)).Next = 0);
            end if;
            pragma Assert (H.Links (H.Order (P)).Next = 0);
         elsif Removed /= Moved and then P - 1 = Moved_Pos then
            pragma Assert (H.Order (P - 1) = Removed);
            pragma Assert (H.Links (H.Order (P)).Next = Removed);
         else
            pragma Assert
              (H.Links (H.Order (P)).Next = H.Order (P - 1));
         end if;

         pragma Assert (Position_Valid (H, P));
         pragma Loop_Invariant
           (for all Q in 1 .. P => Position_Valid (H, Q));
      end loop;

      for I in 1 .. H.Last loop
         if Removed /= Moved and then I = Removed then
            pragma Assert (H.Links (I).Position = Moved_Pos);
         else
            pragma Assert (I /= Removed);
            pragma Assert (Node_Valid (Old, I));
            pragma Assert (H.Links (I).Position = Old.Links (I).Position);
         end if;

         pragma Assert (Node_Valid (H, I));
         pragma Loop_Invariant
           (for all J in 1 .. I => Node_Valid (H, J));
      end loop;

      pragma Assert
        (for all P in 1 .. H.Last =>
           Position_Valid (H, P));
      pragma Assert
        (for all P in 2 .. H.Last =>
           H.Keys (H.Order (P)) <= H.Keys (H.Order (P - 1)));
      pragma Assert (Is_Sorted (H));

      --  Replacing the removed physical slot by the old last key and then
      --  dropping the last slot removes exactly K from the dense-prefix model.

      Remaining_Keys := H.Keys;
      Remaining_Model := Model (H);

      if Removed < Old_Last then
         Models.Lemma_Set (Old.Keys, H.Keys, Removed, Old_Last - 1);
         pragma Assert
           (Old_Model
              = KM.Add
                  (Models.Occurrences (Old.Keys, Old_Last - 1),
                   Old.Keys (Old_Last)));
      else
         Models.Lemma_Same_Prefix (Old.Keys, H.Keys, Old_Last - 1);
         pragma Assert
           (Old_Model
              = KM.Add
                  (Models.Occurrences (Old.Keys, Old_Last - 1), K));
      end if;

      pragma Assert (Old_Model = KM.Add (Remaining_Model, K));
      Models.Lemma_Same_Prefix (Remaining_Keys, H.Keys, H.Last);
      pragma Assert (Model (H) = Remaining_Model);
   end Extract_Min;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Whole : constant KM.Multiset := Model (Into) + Model (From) with Ghost;
      Total : constant Extended_Index := Into.Last + From.Last;
      K     : Key_Type;
      Before_Into : KM.Multiset with Ghost;
      Before_From : KM.Multiset with Ghost;
   begin
      while From.Last > 0 loop
         Before_Into := Model (Into);
         Before_From := Model (From);

         Extract_Min (From, K);
         Insert (Into, K);

         pragma Assert (Before_From = KM.Add (Model (From), K));
         pragma Assert (Model (Into) = KM.Add (Before_Into, K));
         Models.Lemma_Sum_Add_Left (Before_Into, Model (From), K);
         Models.Lemma_Sum_Add (Before_Into, Model (From), K);
         pragma Assert
           (Model (Into) + Model (From) = Before_Into + Before_From);

         pragma Loop_Invariant (Is_Sorted (Into));
         pragma Loop_Invariant (Is_Sorted (From));
         pragma Loop_Invariant (Into.Last + From.Last = Total);
         pragma Loop_Invariant (Model (Into) + Model (From) = Whole);
         pragma Loop_Variant (Decreases => From.Last);
      end loop;

      Models.Lemma_Sum_Empty (Model (Into));
   end Meld;

end Heaps.Sorted_Linked;
