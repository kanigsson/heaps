--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Unsorted with SPARK_Mode is

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
   end Peek_Min;

   --------------
   -- Peek_Max --
   --------------

   function Peek_Max (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) > Result then
            Result := H.Keys (I);
         end if;

         pragma Loop_Invariant (for all J in 1 .. I => H.Keys (J) <= Result);
         pragma Loop_Invariant (for some J in 1 .. I => Result = H.Keys (J));
      end loop;

      return Result;
   end Peek_Max;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;
   begin
      H.Last := H.Last + 1;
      H.Keys (H.Last) := K;

      --  Appending at the end is the one case the definition of Occurrences
      --  handles directly: all that is needed is that the prefix below the
      --  new slot has not moved.

      Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Before, H.Last - 1),
         Models.Occurrences (H.Keys, H.Last - 1),
         K);
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Before : constant Key_Array := Into.Keys with Ghost;
      Base   : constant Extended_Index := Into.Last;
      Cap    : constant Extended_Index := Into.Capacity;

      Prev : Key_Array (1 .. Cap) with Ghost;
      --  Into's keys at the top of the current iteration, which the invariant
      --  established by the previous one speaks about. It is a variable
      --  outside the loop rather than a constant inside it because SPARK does
      --  not accept a non-scalar declaration ahead of a loop invariant. It is
      --  left to the default value of its component type, since the first
      --  statement of every iteration overwrites it.
   begin
      for I in 1 .. From.Last loop
         Prev := Into.Keys;

         Into.Keys (Base + I) := From.Keys (I);
         Into.Last := Base + I;

         --  Storing into slot Base + I leaves everything below it alone, so
         --  the model carried by the previous iteration still describes the
         --  prefix; the new key is then one Add on top of it.

         Models.Lemma_Same_Prefix (Prev, Into.Keys, Base + I - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (Prev, Base + I - 1),
            Models.Occurrences (Into.Keys, Base + I - 1),
            From.Keys (I));

         --  On the other side of the equation, one more key of From joins the
         --  sum. Carrying that Add out through the sum is the whole content of
         --  the step, and the first iteration starts from an empty
         --  contribution.

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

      --  With no keys to copy the sum is Into's own model.

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (Models.Occurrences (Before, Base));
      end if;

      From.Last := 0;
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;

      Min_At : Index := 1;
      --  Index of the smallest key seen so far
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) < H.Keys (Min_At) then
            Min_At := I;
         end if;

         pragma Loop_Invariant (Min_At <= I);
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (Min_At) <= H.Keys (J));
      end loop;

      K := H.Keys (Min_At);

      --  Plug the gap with the last key, which is the only move that keeps
      --  the operation O(1) once the minimum has been located.

      H.Keys (Min_At) := H.Keys (H.Last);

      if Min_At < H.Last then
         Models.Lemma_Set (Before, H.Keys, Min_At, H.Last - 1);
      else
         --  The store was a self-assignment; nothing moved at all.
         Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (H.Keys, H.Last - 1),
            Models.Occurrences (Before, H.Last - 1),
            K);
      end if;

      H.Last := H.Last - 1;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;

      Max_At : Index := 1;
      --  Index of the largest key seen so far
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) > H.Keys (Max_At) then
            Max_At := I;
         end if;

         pragma Loop_Invariant (Max_At <= I);
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (J) <= H.Keys (Max_At));
      end loop;

      K := H.Keys (Max_At);
      H.Keys (Max_At) := H.Keys (H.Last);

      if Max_At < H.Last then
         Models.Lemma_Set (Before, H.Keys, Max_At, H.Last - 1);
      else
         Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (H.Keys, H.Last - 1),
            Models.Occurrences (Before, H.Last - 1),
            K);
      end if;

      H.Last := H.Last - 1;
   end Extract_Max;

end Heaps.Unsorted;
