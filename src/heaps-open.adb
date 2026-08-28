--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

package body Heaps.Open is

   function Total_Size (H : Heap) return Extended_Index;

   procedure Append_Staged (H : in out Heap; K : Key_Type);
   procedure Remove_Staged
     (H : in out Heap; Position : Index; K : out Key_Type);
   procedure Build_Base (H : in out Heap);
   procedure Flush_Pending (H : in out Heap);
   procedure Activate (H : in out Heap);
   procedure Append_All (Into : in out Heap; From : Heap);
   procedure Insert_All (Into : in out Heap; From : Heap);

   ----------------
   -- Total_Size --
   ----------------

   function Total_Size (H : Heap) return Extended_Index is
     (if H.Mode = Initial
      then H.Staged_Last
      else H.Base.Last + H.Pending.Last);

   -------------------
   -- Append_Staged --
   -------------------

   procedure Append_Staged (H : in out Heap; K : Key_Type) is
   begin
      H.Staged_Last := H.Staged_Last + 1;
      H.Staged (H.Staged_Last) := K;

      if H.Staged_Last = 1 then
         H.Staged_Min := 1;
         H.Staged_Max := 1;
      else
         if K < H.Staged (H.Staged_Min) then
            H.Staged_Min := H.Staged_Last;
         end if;
         if K > H.Staged (H.Staged_Max) then
            H.Staged_Max := H.Staged_Last;
         end if;
      end if;
   end Append_Staged;

   -------------------
   -- Remove_Staged --
   -------------------

   procedure Remove_Staged
     (H : in out Heap; Position : Index; K : out Key_Type)
   is
   begin
      K := H.Staged (Position);
      H.Staged (Position) := H.Staged (H.Staged_Last);
      H.Staged_Last := H.Staged_Last - 1;

      if H.Staged_Last = 0 then
         H.Staged_Min := 0;
         H.Staged_Max := 0;
      else
         H.Staged_Min := 1;
         H.Staged_Max := 1;
         for I in 2 .. H.Staged_Last loop
            if H.Staged (I) < H.Staged (H.Staged_Min) then
               H.Staged_Min := I;
            end if;
            if H.Staged (I) > H.Staged (H.Staged_Max) then
               H.Staged_Max := I;
            end if;
         end loop;
      end if;
   end Remove_Staged;

   ----------
   -- Swap --
   ----------

   procedure Swap (H : in out Interval.Heap; Left, Right : Index) is
      Temporary : constant Key_Type := H.Keys (Left);
   begin
      H.Keys (Left) := H.Keys (Right);
      H.Keys (Right) := Temporary;
   end Swap;

   ----------
   -- Slot --
   ----------

   function Slot
     (H : Interval.Heap; Min_Side : Boolean; Node : Index) return Index is
     (if Min_Side or else 2 * Node > H.Last
      then 2 * Node - 1
      else 2 * Node);

   ---------------
   -- Sift_Down --
   ---------------

   procedure Sift_Down
     (H : in out Interval.Heap; Start : Index; Min_Side : Boolean)
   is
      I          : Index := Start;
      Child      : Index;
      Right      : Index;
      Node_Count : constant Extended_Index := (H.Last + 1) / 2;
   begin
      while 2 * I <= Node_Count loop
         Child := 2 * I;
         Right := Child + 1;

         if Right <= Node_Count
           and then
             (if Min_Side
              then H.Keys (Slot (H, True, Right))
                     < H.Keys (Slot (H, True, Child))
              else H.Keys (Slot (H, False, Right))
                     > H.Keys (Slot (H, False, Child)))
         then
            Child := Right;
         end if;

         exit when
           (if Min_Side
            then H.Keys (Slot (H, True, Child))
                   >= H.Keys (Slot (H, True, I))
            else H.Keys (Slot (H, False, Child))
                   <= H.Keys (Slot (H, False, I)));

         Swap (H, Slot (H, Min_Side, I), Slot (H, Min_Side, Child));

         if H.Keys (Slot (H, True, Child))
           > H.Keys (Slot (H, False, Child))
         then
            Swap (H, Slot (H, True, Child), Slot (H, False, Child));
         end if;

         I := Child;
      end loop;
   end Sift_Down;

   ----------------
   -- Build_Base --
   ----------------

   procedure Build_Base (H : in out Heap) is
      Node_Count : Extended_Index;
   begin
      H.Base.Last := H.Staged_Last;
      H.Base.Keys (1 .. H.Staged_Last) := H.Staged (1 .. H.Staged_Last);
      Node_Count := (H.Base.Last + 1) / 2;

      --  Form the intervals first, then heapify their low and high sides.

      for Node in 1 .. Node_Count loop
         if 2 * Node <= H.Base.Last
           and then H.Base.Keys (2 * Node - 1) > H.Base.Keys (2 * Node)
         then
            Swap (H.Base, 2 * Node - 1, 2 * Node);
         end if;
      end loop;

      for Node in reverse 1 .. Node_Count loop
         Sift_Down (H.Base, Node, True);
         Sift_Down (H.Base, Node, False);
      end loop;

      H.Staged_Last := 0;
      H.Staged_Min := 0;
      H.Staged_Max := 0;
      H.Mode := Active;
   end Build_Base;

   -------------------
   -- Flush_Pending --
   -------------------

   procedure Flush_Pending (H : in out Heap) is
   begin
      if H.Pending.Last = 0 then
         return;
      end if;

      --  Rebuilding is worthwhile only when the pending batch is a material
      --  fraction of the base. For a small batch, preserve the base and pay
      --  for logarithmic insertions instead. This is a size-only cost rule.

      if H.Base.Last = 0 or else 8 * H.Pending.Last >= H.Base.Last then
         Interval.Meld (H.Base, H.Pending);
      else
         for I in 1 .. H.Pending.Last loop
            Interval.Insert (H.Base, H.Pending.Keys (I));
         end loop;
         Interval.Clear (H.Pending);
      end if;
   end Flush_Pending;

   --------------
   -- Activate --
   --------------

   procedure Activate (H : in out Heap) is
   begin
      if H.Mode = Initial then
         if H.Staged_Last = 0 then
            H.Mode := Active;
         else
            Build_Base (H);
         end if;
      end if;
      Flush_Pending (H);
   end Activate;

   ----------------
   -- Append_All --
   ----------------

   procedure Append_All (Into : in out Heap; From : Heap) is
   begin
      if From.Mode = Initial then
         for I in 1 .. From.Staged_Last loop
            Append_Staged (Into, From.Staged (I));
         end loop;
      else
         for I in 1 .. From.Base.Last loop
            Append_Staged (Into, From.Base.Keys (I));
         end loop;
         for I in 1 .. From.Pending.Last loop
            Append_Staged (Into, From.Pending.Keys (I));
         end loop;
      end if;
   end Append_All;

   ----------------
   -- Insert_All --
   ----------------

   procedure Insert_All (Into : in out Heap; From : Heap) is
   begin
      if From.Mode = Initial then
         for I in 1 .. From.Staged_Last loop
            Insert (Into, From.Staged (I));
         end loop;
      else
         for I in 1 .. From.Base.Last loop
            Insert (Into, From.Base.Keys (I));
         end loop;
         for I in 1 .. From.Pending.Last loop
            Insert (Into, From.Pending.Keys (I));
         end loop;
      end if;
   end Insert_All;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      Interval.Clear (H.Base);
      Interval.Clear (H.Pending);
      H.Staged_Last := 0;
      H.Staged_Min := 0;
      H.Staged_Max := 0;
      H.Mode := Initial;
   end Clear;

   ----------
   -- Size --
   ----------

   function Size (H : Heap) return Extended_Index is (Total_Size (H));

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (H : Heap) return Boolean is (Total_Size (H) = 0);

   -------------
   -- Is_Full --
   -------------

   function Is_Full (H : Heap) return Boolean is
     (Total_Size (H) = H.Capacity);

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
   begin
      if H.Mode = Initial then
         return H.Staged (H.Staged_Min);
      elsif H.Base.Last = 0 then
         return Interval.Peek_Min (H.Pending);
      elsif H.Pending.Last = 0 then
         return Interval.Peek_Min (H.Base);
      else
         return Key_Type'Min
           (Interval.Peek_Min (H.Base), Interval.Peek_Min (H.Pending));
      end if;
   end Peek_Min;

   --------------
   -- Peek_Max --
   --------------

   function Peek_Max (H : Heap) return Key_Type is
   begin
      if H.Mode = Initial then
         return H.Staged (H.Staged_Max);
      elsif H.Base.Last = 0 then
         return Interval.Peek_Max (H.Pending);
      elsif H.Pending.Last = 0 then
         return Interval.Peek_Max (H.Base);
      else
         return Key_Type'Max
           (Interval.Peek_Max (H.Base), Interval.Peek_Max (H.Pending));
      end if;
   end Peek_Max;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
   begin
      if H.Mode = Initial then
         Append_Staged (H, K);
      else
         if H.Pending.Last = Pending_Limit then
            Flush_Pending (H);
         end if;
         Interval.Insert (H.Pending, K);
      end if;
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      From_Size : constant Extended_Index := Total_Size (From);
   begin
      if From_Size = 0 then
         Clear (From);

      elsif Into.Mode = Initial then
         --  Nothing has required an ordered representation yet. Preserve
         --  that state and concatenate the source's physical keys.

         Append_All (Into, From);
         Clear (From);

      elsif From_Size <= Total_Size (Into) / 8 then
         --  Rebuilding a much larger active heap would cost more than adding
         --  the smaller source through its buffered insertion path.

         Insert_All (Into, From);
         Clear (From);

      else
         --  For comparable heaps, consolidate both representations and use
         --  the interval heap's linear destructive meld.

         Activate (Into);
         Activate (From);
         Interval.Meld (Into.Base, From.Base);
         Clear (From);
      end if;
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
   begin
      if H.Mode = Initial then
         if H.Staged_Last <= Small_Limit then
            Remove_Staged (H, H.Staged_Min, K);
            return;
         else
            Build_Base (H);
         end if;
      end if;

      if H.Base.Last = 0 then
         Interval.Extract_Min (H.Pending, K);
      elsif H.Pending.Last = 0
        or else Interval.Peek_Min (H.Base) <= Interval.Peek_Min (H.Pending)
      then
         Interval.Extract_Min (H.Base, K);
      else
         Interval.Extract_Min (H.Pending, K);
      end if;

      if H.Base.Last = 0 and then H.Pending.Last = 0 then
         H.Mode := Initial;
      end if;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
   begin
      if H.Mode = Initial then
         if H.Staged_Last <= Small_Limit then
            Remove_Staged (H, H.Staged_Max, K);
            return;
         else
            Build_Base (H);
         end if;
      end if;

      if H.Base.Last = 0 then
         Interval.Extract_Max (H.Pending, K);
      elsif H.Pending.Last = 0
        or else Interval.Peek_Max (H.Base) >= Interval.Peek_Max (H.Pending)
      then
         Interval.Extract_Max (H.Base, K);
      else
         Interval.Extract_Max (H.Pending, K);
      end if;

      if H.Base.Last = 0 and then H.Pending.Last = 0 then
         H.Mode := Initial;
      end if;
   end Extract_Max;

end Heaps.Open;
