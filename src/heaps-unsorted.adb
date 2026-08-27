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

end Heaps.Unsorted;
