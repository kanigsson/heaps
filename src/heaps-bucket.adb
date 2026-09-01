--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Bucket with SPARK_Mode is

   package KM renames Key_Multisets;

   procedure Lemma_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, H.Minimum);

   procedure Lemma_Total_Same (A, B : Heap; At_Key : Key_Type)
     with Ghost,
          Pre  => A.First_Key = B.First_Key
                  and then A.Last_Key = B.Last_Key
                  and then At_Key in A.First_Key .. A.Last_Key
                  and then
                    (for all P in At_Key .. A.Last_Key =>
                       A.Counts (P) = B.Counts (P)),
          Post => Total_From (A, At_Key) = Total_From (B, At_Key),
          Subprogram_Variant => (Increases => At_Key);

   procedure Lemma_Total_Increment
     (Old_H, New_H : Heap; Changed, At_Key : Key_Type)
     with Ghost,
          Pre  => Old_H.First_Key = New_H.First_Key
                  and then Old_H.Last_Key = New_H.Last_Key
                  and then Changed in Old_H.First_Key .. Old_H.Last_Key
                  and then At_Key in Old_H.First_Key .. Changed
                  and then Old_H.Counts (Changed) < Max_Capacity
                  and then New_H.Counts (Changed)
                             = Old_H.Counts (Changed) + 1
                  and then
                    (for all P in Old_H.First_Key .. Old_H.Last_Key =>
                       (if P /= Changed
                        then New_H.Counts (P) = Old_H.Counts (P))),
          Post => Total_From (New_H, At_Key)
                    = Total_From (Old_H, At_Key) + 1,
          Subprogram_Variant => (Increases => At_Key);

   procedure Lemma_Count_Bounded (H : Heap; K, At_Key : Key_Type)
     with Ghost,
          Pre  => Is_Heap (H)
                  and then K in H.First_Key .. H.Last_Key
                  and then At_Key in H.First_Key .. K,
          Post => SPARK.Big_Integers.To_Big_Integer (H.Counts (K))
                    <= Total_From (H, At_Key),
          Subprogram_Variant => (Increases => At_Key);

   procedure Lemma_Total_Zero (H : Heap; At_Key : Key_Type)
     with Ghost,
          Pre  => At_Key in H.First_Key .. H.Last_Key
                  and then
                    (for all P in At_Key .. H.Last_Key => H.Counts (P) = 0),
          Post => Total_From (H, At_Key) = 0,
          Subprogram_Variant => (Increases => At_Key);

   function Minimum_Head (H : Heap) return Index
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Minimum_Head'Result = H.Heads (H.Minimum);

   -------------------
   -- Lemma_Minimum --
   -------------------

   procedure Lemma_Minimum (H : Heap) is
   begin
      for I in 1 .. H.Last loop
         pragma Assert (Node_Valid (H, I));
         pragma Assert (H.Counts (H.Keys (I)) > 0);
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Minimum <= H.Keys (J));
      end loop;
   end Lemma_Minimum;

   ----------------------
   -- Lemma_Total_Same --
   ----------------------

   procedure Lemma_Total_Same (A, B : Heap; At_Key : Key_Type) is
   begin
      if At_Key < A.Last_Key then
         Lemma_Total_Same (A, B, Key_Type'Succ (At_Key));
      end if;
   end Lemma_Total_Same;

   ---------------------------
   -- Lemma_Total_Increment --
   ---------------------------

   procedure Lemma_Total_Increment
     (Old_H, New_H : Heap; Changed, At_Key : Key_Type)
   is
   begin
      if At_Key < Changed then
         Lemma_Total_Increment
           (Old_H, New_H, Changed, Key_Type'Succ (At_Key));
      elsif At_Key < Old_H.Last_Key then
         Lemma_Total_Same
           (Old_H, New_H, Key_Type'Succ (At_Key));
      end if;
   end Lemma_Total_Increment;

   -------------------------
   -- Lemma_Count_Bounded --
   -------------------------

   procedure Lemma_Count_Bounded (H : Heap; K, At_Key : Key_Type) is
   begin
      if At_Key < K then
         Lemma_Count_Bounded (H, K, Key_Type'Succ (At_Key));
      end if;
   end Lemma_Count_Bounded;

   ----------------------
   -- Lemma_Total_Zero --
   ----------------------

   procedure Lemma_Total_Zero (H : Heap; At_Key : Key_Type) is
   begin
      if At_Key < H.Last_Key then
         Lemma_Total_Zero (H, Key_Type'Succ (At_Key));
      end if;
   end Lemma_Total_Zero;

   ------------------
   -- Minimum_Head --
   ------------------

   function Minimum_Head (H : Heap) return Index is
   begin
      pragma Assert (Bucket_Valid (H, H.Minimum));
      pragma Assert (H.Heads (H.Minimum) in 1 .. H.Last);
      return H.Heads (H.Minimum);
   end Minimum_Head;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      for K in H.First_Key .. H.Last_Key loop
         H.Heads (K) := 0;
         H.Counts (K) := 0;

         pragma Loop_Invariant
           (for all P in H.First_Key .. K =>
              H.Heads (P) = 0 and then H.Counts (P) = 0);
      end loop;

      H.Last := 0;
      H.Minimum := H.First_Key;
      H.Has_Min := False;
      Lemma_Total_Zero (H, H.First_Key);
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
   begin
      Lemma_Minimum (H);
      return H.Minimum;
   end Peek_Min;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Before    : constant Key_Array := H.Keys with Ghost;
      Old_H     : constant Heap := H with Ghost;
      Slot      : constant Index := H.Last + 1;
      Old_Head  : constant Extended_Index := H.Heads (K);
      Old_Count : constant Extended_Index := H.Counts (K);
   begin
      Lemma_Count_Bounded (H, K, H.First_Key);
      pragma Assert (Old_Count <= H.Last);
      pragma Assert (Old_Count < H.Capacity);
      H.Last := Slot;
      H.Keys (Slot) := K;
      H.Links (Slot) :=
        (Prev   => 0,
         Next   => Old_Head,
         Length => Old_Count + 1);

      if Old_Head /= 0 then
         H.Links (Old_Head).Prev := Slot;
      end if;

      H.Heads (K) := Slot;
      H.Counts (K) := Old_Count + 1;

      if not H.Has_Min or else K < H.Minimum then
         H.Minimum := K;
      end if;
      H.Has_Min := True;

      Lemma_Total_Increment (Old_H, H, K, H.First_Key);

      pragma Assert (Node_Valid (H, Slot));
      pragma Assert
        (for all I in 1 .. Old_H.Last =>
           (if I = Old_Head then Node_Valid (H, I)
            else Node_Valid (H, I)));
      pragma Assert
        (for all P in H.First_Key .. H.Last_Key => Bucket_Valid (H, P));
      pragma Assert (Is_Heap (H));

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
         pragma Assert (Node_Valid (From, I));
         pragma Assert
           (From.Keys (I) in Into.First_Key .. Into.Last_Key);
         Insert (Into, From.Keys (I));
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

      Clear (From);
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Before          : constant Key_Array := H.Keys with Ghost;
      Old_H           : constant Heap := H with Ghost;
      Old_Model       : constant KM.Multiset := Model (H) with Ghost;
      Removed         : constant Index := Minimum_Head (H);
      Old_Last        : constant Index := H.Last;
      Next            : constant Extended_Index := H.Links (Removed).Next;
      Moved_Key       : Key_Type;
      Moved_Link      : Link;
      Remaining_Model : KM.Multiset with Ghost;
      Remaining_Keys  : Key_Array := H.Keys with Ghost;
   begin
      pragma Assert (Node_Valid (H, Removed));
      K := H.Minimum;

      H.Counts (K) := H.Counts (K) - 1;
      H.Heads (K) := Next;
      if Next /= 0 then
         H.Links (Next).Prev := 0;
      end if;

      Moved_Key := H.Keys (Old_Last);
      Moved_Link := H.Links (Old_Last);

      if Removed /= Old_Last then
         H.Keys (Removed) := Moved_Key;
         H.Links (Removed) := Moved_Link;

         if Moved_Link.Prev = 0 then
            H.Heads (Moved_Key) := Removed;
         else
            H.Links (Moved_Link.Prev).Next := Removed;
         end if;

         if Moved_Link.Next /= 0 then
            H.Links (Moved_Link.Next).Prev := Removed;
         end if;

         pragma Assert (Removed <= Old_Last - 1);
         Models.Lemma_Set (Before, H.Keys, Removed, Old_Last - 1);
      else
         Models.Lemma_Same_Prefix (Before, H.Keys, Old_Last - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (H.Keys, Old_Last - 1),
            Models.Occurrences (Before, Old_Last - 1), K);
      end if;

      Remaining_Model := Models.Occurrences (H.Keys, Old_Last - 1);
      Remaining_Keys := H.Keys;
      pragma Assert (Old_Model = KM.Add (Remaining_Model, K));

      H.Last := Old_Last - 1;
      pragma Assert (Model (H) = Remaining_Model);

      pragma Assert
        (for all P in H.First_Key .. H.Last_Key =>
           H.Counts (P)
             = (if P = K then Old_H.Counts (P) - 1
                else Old_H.Counts (P)));
      for I in 1 .. H.Last loop
         declare
            Source : constant Index :=
              (if Removed /= Old_Last and then I = Removed
               then Old_Last else I);
         begin
            pragma Assert (Source /= Removed);
            pragma Assert (Node_Valid (Old_H, Source));
            pragma Assert (H.Keys (I) = Old_H.Keys (Source));
            if Removed /= Old_Last and then I = Removed then
               pragma Assert (Source = Old_Last);
               pragma Assert (H.Links (I).Length = Moved_Link.Length);
               pragma Assert
                 (Moved_Link.Length = Old_H.Links (Old_Last).Length);
            else
               pragma Assert (Source = I);
               pragma Assert
                 (H.Links (I).Length = Old_H.Links (I).Length);
            end if;
            pragma Assert
              (H.Links (I).Length = Old_H.Links (Source).Length);

            if H.Keys (I) = K then
               pragma Assert (Old_H.Keys (Source) = K);
               pragma Assert (Old_H.Links (Source).Prev /= 0);
               pragma Assert
                 (Old_H.Links (Old_H.Links (Source).Prev).Length
                    = Old_H.Links (Source).Length + 1);
               pragma Assert
                 (Old_H.Links (Source).Length < Old_H.Counts (K));
            end if;
         end;

         if I = Next then
            pragma Assert (H.Links (I).Prev = 0);
         end if;
         if Removed /= Old_Last and then I = Moved_Link.Prev then
            pragma Assert (H.Links (I).Next = Removed);
         end if;
         if Removed /= Old_Last and then I = Moved_Link.Next then
            pragma Assert (H.Links (I).Prev = Removed);
         end if;

         if H.Links (I).Prev = Old_Last then
            pragma Assert (False);
         end if;
         if H.Links (I).Next = Old_Last then
            pragma Assert (False);
         end if;

         pragma Assert (H.Keys (I) in H.First_Key .. H.Last_Key);
         pragma Assert
           (H.Links (I).Length in 1 .. H.Counts (H.Keys (I)));
         pragma Assert (H.Links (I).Prev in 0 .. H.Last);
         pragma Assert (H.Links (I).Next in 0 .. H.Last);
         if H.Links (I).Prev = 0 then
            if Removed /= Old_Last and then I = Removed then
               pragma Assert (H.Heads (H.Keys (I)) = I);
            elsif I = Next then
               pragma Assert (H.Heads (K) = I);
            else
               pragma Assert (Old_H.Links (I).Prev = 0);
               pragma Assert (Old_H.Heads (Old_H.Keys (I)) = I);
               pragma Assert (H.Heads (H.Keys (I)) = I);
            end if;
         end if;
         if H.Links (I).Next /= 0 then
            if Removed /= Old_Last and then I = Moved_Link.Prev then
               pragma Assert (H.Links (I).Next = Removed);
               pragma Assert (H.Keys (Removed) = H.Keys (I));
            else
               pragma Assert (H.Keys (H.Links (I).Next) = H.Keys (I));
            end if;
         end if;
         if H.Links (I).Prev /= 0 then
            if Removed /= Old_Last and then I = Removed then
               pragma Assert
                 (H.Links (H.Links (I).Prev).Next = I);
            elsif Removed /= Old_Last and then I = Moved_Link.Next then
               pragma Assert (H.Links (I).Prev = Removed);
               pragma Assert (H.Links (Removed).Next = I);
            else
               pragma Assert (Old_H.Links (I).Prev /= Removed);
               pragma Assert (Old_H.Links (I).Prev /= Old_Last);
               pragma Assert (H.Links (I).Prev = Old_H.Links (I).Prev);
               pragma Assert (H.Links (I).Prev /= Moved_Link.Prev);
               pragma Assert
                 (H.Links (H.Links (I).Prev).Next
                    = Old_H.Links (Old_H.Links (I).Prev).Next);
               pragma Assert
                 (H.Links (H.Links (I).Prev).Next = I);
            end if;
         end if;
         if H.Links (I).Next /= 0 then
            if Removed /= Old_Last and then I = Removed then
               pragma Assert
                 (H.Links (H.Links (I).Next).Prev = I);
            elsif Removed /= Old_Last and then I = Moved_Link.Prev then
               pragma Assert (H.Links (I).Next = Removed);
               pragma Assert (H.Links (Removed).Prev = I);
            else
               pragma Assert (Old_H.Links (I).Next /= Removed);
               pragma Assert (Old_H.Links (I).Next /= Old_Last);
               pragma Assert (H.Links (I).Next = Old_H.Links (I).Next);
               pragma Assert (H.Links (I).Next /= Moved_Link.Next);
               pragma Assert
                 (H.Links (H.Links (I).Next).Prev
                    = Old_H.Links (Old_H.Links (I).Next).Prev);
               pragma Assert
                 (H.Links (H.Links (I).Next).Prev = I);
            end if;
         end if;
         pragma Assert
           (if H.Links (I).Prev = 0
            then H.Heads (H.Keys (I)) = I
                 and then H.Links (I).Length = H.Counts (H.Keys (I))
            else H.Keys (H.Links (I).Prev) = H.Keys (I)
                 and then H.Links (H.Links (I).Prev).Next = I
                 and then H.Links (H.Links (I).Prev).Length
                            = H.Links (I).Length + 1);
         pragma Assert
           (if H.Links (I).Next = 0
            then H.Links (I).Length = 1
            else H.Keys (H.Links (I).Next) = H.Keys (I)
                 and then H.Links (H.Links (I).Next).Prev = I
                 and then H.Links (H.Links (I).Next).Length + 1
                            = H.Links (I).Length);
         pragma Assert (Node_Valid (H, I));
         pragma Loop_Invariant
           (for all J in 1 .. I => Node_Valid (H, J));
      end loop;

      for P in H.First_Key .. H.Last_Key loop
         pragma Assert (Bucket_Valid (Old_H, P));

         if H.Counts (P) = 0 then
            if P = K then
               pragma Assert (Old_H.Counts (P) = 1);
            else
               pragma Assert (Old_H.Counts (P) = 0);
            end if;
            pragma Assert (H.Heads (P) = 0);
         else
            if P = K then
               pragma Assert (H.Heads (P) = Next or else H.Heads (P) = Removed);
            elsif Removed /= Old_Last and then P = Moved_Key then
               pragma Assert
                 (H.Heads (P) = Removed or else H.Heads (P) = Old_H.Heads (P));
            else
               pragma Assert (H.Heads (P) = Old_H.Heads (P));
            end if;
            pragma Assert (H.Heads (P) in 1 .. H.Last);
            pragma Assert (H.Keys (H.Heads (P)) = P);
            pragma Assert (H.Links (H.Heads (P)).Prev = 0);
            pragma Assert
              (H.Links (H.Heads (P)).Length = H.Counts (P));
         end if;
         pragma Assert (Bucket_Valid (H, P));
         pragma Loop_Invariant
           (for all Q in H.First_Key .. P => Bucket_Valid (H, Q));
      end loop;

      if H.Last = 0 then
         H.Has_Min := False;
         H.Minimum := H.First_Key;
      elsif H.Counts (K) > 0 then
         H.Minimum := K;
      else
         declare
            Upper : constant Key_Type := H.Keys (1);
         begin
            pragma Assert (Node_Valid (H, 1));
            pragma Assert (H.Counts (Upper) > 0);
            pragma Assert (Upper > K);
            H.Minimum := Upper;

            for Candidate in K + 1 .. Upper loop
               if H.Counts (Candidate) > 0 then
                  H.Minimum := Candidate;
                  exit;
               end if;

               pragma Loop_Invariant
                 (for all P in K + 1 .. Candidate => H.Counts (P) = 0);
            end loop;
         end;
      end if;

      Lemma_Total_Increment (H, Old_H, K, H.First_Key);

      pragma Assert (Is_Heap (H));

      Models.Lemma_Same_Prefix (Remaining_Keys, H.Keys, H.Last);
      pragma Assert (Model (H) = Remaining_Model);
      Models.Lemma_Add_Congruent (Model (H), Remaining_Model, K);
   end Extract_Min;

end Heaps.Bucket;
