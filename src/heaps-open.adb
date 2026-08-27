--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Interfaces; use Interfaces;

package body Heaps.Open is

   procedure Build_Min_Heap (H : in out Heap);
   procedure Build_Max_Heap (H : in out Heap);
   procedure Insert_Min_Heap (H : in out Heap; K : Key_Type);
   procedure Insert_Max_Heap (H : in out Heap; K : Key_Type);
   procedure Extract_Min_Heap (H : in out Heap; K : out Key_Type);
   procedure Extract_Max_Heap (H : in out Heap; K : out Key_Type);
   procedure Extract_Buffer
     (H : in out Heap; Min_Side : Boolean; K : out Key_Type);
   procedure Radix_Sort (H : in out Heap);

   -------------------
   -- Sift_Down_Min --
   -------------------

   procedure Sift_Down_Min (H : in out Heap; Root : Index) is
      I     : Index := Root;
      Child : Index;
      Moved : constant Key_Type := H.Keys (Root);
   begin
      while I <= H.Count / 2 loop
         Child := 2 * I;
         if Child < H.Count and then H.Keys (Child + 1) < H.Keys (Child) then
            Child := Child + 1;
         end if;
         exit when H.Keys (Child) >= Moved;
         H.Keys (I) := H.Keys (Child);
         I := Child;
      end loop;
      H.Keys (I) := Moved;
   end Sift_Down_Min;

   -------------------
   -- Sift_Down_Max --
   -------------------

   procedure Sift_Down_Max (H : in out Heap; Root : Index) is
      I     : Index := Root;
      Child : Index;
      Moved : constant Key_Type := H.Keys (Root);
   begin
      while I <= H.Count / 2 loop
         Child := 2 * I;
         if Child < H.Count and then H.Keys (Child + 1) > H.Keys (Child) then
            Child := Child + 1;
         end if;
         exit when H.Keys (Child) <= Moved;
         H.Keys (I) := H.Keys (Child);
         I := Child;
      end loop;
      H.Keys (I) := Moved;
   end Sift_Down_Max;

   --------------------
   -- Build_Min_Heap --
   --------------------

   procedure Build_Min_Heap (H : in out Heap) is
   begin
      for I in reverse 1 .. H.Count / 2 loop
         Sift_Down_Min (H, I);
      end loop;
      H.Mode := Min_Heap;
   end Build_Min_Heap;

   --------------------
   -- Build_Max_Heap --
   --------------------

   procedure Build_Max_Heap (H : in out Heap) is
   begin
      for I in reverse 1 .. H.Count / 2 loop
         Sift_Down_Max (H, I);
      end loop;
      H.Mode := Max_Heap;
   end Build_Max_Heap;

   ---------------------
   -- Insert_Min_Heap --
   ---------------------

   procedure Insert_Min_Heap (H : in out Heap; K : Key_Type) is
      Hole : Index;
   begin
      H.Count := H.Count + 1;
      Hole := H.Count;
      while Hole > 1 and then H.Keys (Hole / 2) > K loop
         H.Keys (Hole) := H.Keys (Hole / 2);
         Hole := Hole / 2;
      end loop;
      H.Keys (Hole) := K;
   end Insert_Min_Heap;

   ---------------------
   -- Insert_Max_Heap --
   ---------------------

   procedure Insert_Max_Heap (H : in out Heap; K : Key_Type) is
      Hole : Index;
   begin
      H.Count := H.Count + 1;
      Hole := H.Count;
      while Hole > 1 and then H.Keys (Hole / 2) < K loop
         H.Keys (Hole) := H.Keys (Hole / 2);
         Hole := Hole / 2;
      end loop;
      H.Keys (Hole) := K;
   end Insert_Max_Heap;

   ----------------------
   -- Extract_Min_Heap --
   ----------------------

   procedure Extract_Min_Heap (H : in out Heap; K : out Key_Type) is
   begin
      K := H.Keys (1);
      H.Keys (1) := H.Keys (H.Count);
      H.Count := H.Count - 1;
      if H.Count > 0 then
         Sift_Down_Min (H, 1);
      else
         H.Mode := Buffer;
      end if;
   end Extract_Min_Heap;

   ----------------------
   -- Extract_Max_Heap --
   ----------------------

   procedure Extract_Max_Heap (H : in out Heap; K : out Key_Type) is
   begin
      K := H.Keys (1);
      H.Keys (1) := H.Keys (H.Count);
      H.Count := H.Count - 1;
      if H.Count > 0 then
         Sift_Down_Max (H, 1);
      else
         H.Mode := Buffer;
      end if;
   end Extract_Max_Heap;

   --------------------
   -- Extract_Buffer --
   --------------------

   procedure Extract_Buffer
     (H : in out Heap; Min_Side : Boolean; K : out Key_Type)
   is
      Best : Index := 1;
   begin
      for I in 2 .. H.Count loop
         if (if Min_Side then H.Keys (I) < H.Keys (Best)
             else H.Keys (I) > H.Keys (Best))
         then
            Best := I;
         end if;
      end loop;

      K := H.Keys (Best);
      H.Keys (Best) := H.Keys (H.Count);
      H.Count := H.Count - 1;
      if H.Count = 0 then
         H.Mode := Buffer;
      elsif Min_Side then
         H.Mode := Probe_Min;
      else
         H.Mode := Probe_Max;
      end if;
   end Extract_Buffer;

   -------------------
   -- Counting_Pass --
   -------------------

   procedure Counting_Pass
     (Source : Key_Array;
      Target : in out Key_Array;
      Count  : Extended_Index;
      Amount : Natural)
   is
      subtype Bucket is Natural range 0 .. 255;
      type Counter_Array is array (Bucket) of Extended_Index;

      Frequency : Counter_Array := [others => 0];
      Position  : Counter_Array;

      function Bucket_Of (K : Key_Type) return Bucket is
         Bits : Unsigned_64;
      begin
         --  Flipping the sign bit turns signed order into unsigned
         --  lexicographic order. Use four byte passes on the usual 32-bit
         --  Integer and eight if a target provides a wider Integer.

         if Integer'Size <= 32 then
            Bits := Unsigned_64
              (Unsigned_32'Mod (Integer (K)) xor 16#8000_0000#);
         else
            Bits := Unsigned_64'Mod (Long_Long_Integer (K))
              xor 16#8000_0000_0000_0000#;
         end if;
         return Bucket (Shift_Right (Bits, Amount) and 16#FF#);
      end Bucket_Of;

      Next : Extended_Index := 1;
   begin
      for I in 1 .. Count loop
         declare
            B : constant Bucket := Bucket_Of (Source (I));
         begin
            Frequency (B) := Frequency (B) + 1;
         end;
      end loop;

      for B in Bucket loop
         Position (B) := Next;
         Next := Next + Frequency (B);
      end loop;

      for I in 1 .. Count loop
         declare
            B : constant Bucket := Bucket_Of (Source (I));
         begin
            Target (Position (B)) := Source (I);
            Position (B) := Position (B) + 1;
         end;
      end loop;
   end Counting_Pass;

   ----------------
   -- Radix_Sort --
   ----------------

   procedure Radix_Sort (H : in out Heap) is
   begin
      Counting_Pass (H.Keys, H.Scratch, H.Count, 0);
      Counting_Pass (H.Scratch, H.Keys, H.Count, 8);
      Counting_Pass (H.Keys, H.Scratch, H.Count, 16);
      Counting_Pass (H.Scratch, H.Keys, H.Count, 24);

      if Integer'Size > 32 then
         Counting_Pass (H.Keys, H.Scratch, H.Count, 32);
         Counting_Pass (H.Scratch, H.Keys, H.Count, 40);
         Counting_Pass (H.Keys, H.Scratch, H.Count, 48);
         Counting_Pass (H.Scratch, H.Keys, H.Count, 56);
      end if;

      H.First := 1;
      H.Last := H.Count;
      H.Mode := Sorted;
   end Radix_Sort;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Count := 0;
      H.First := 1;
      H.Last := 0;
      H.Mode := Buffer;
   end Clear;

   ----------
   -- Size --
   ----------

   function Size (H : Heap) return Extended_Index is (H.Count);

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (H : Heap) return Boolean is (H.Count = 0);

   -------------
   -- Is_Full --
   -------------

   function Is_Full (H : Heap) return Boolean is (H.Count = H.Capacity);

   ----------------
   -- Best_Value --
   ----------------

   function Best_Value (H : Heap; Min_Side : Boolean) return Key_Type is
      Best : Index;
   begin
      if H.Mode = Sorted then
         return H.Keys (if Min_Side then H.First else H.Last);
      elsif (H.Mode = Min_Heap and then Min_Side)
        or else (H.Mode = Max_Heap and then not Min_Side)
      then
         return H.Keys (1);
      end if;

      Best := 1;
      for I in 2 .. H.Count loop
         if (if Min_Side then H.Keys (I) < H.Keys (Best)
             else H.Keys (I) > H.Keys (Best))
         then
            Best := I;
         end if;
      end loop;
      return H.Keys (Best);
   end Best_Value;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is (Best_Value (H, True));

   --------------
   -- Peek_Max --
   --------------

   function Peek_Max (H : Heap) return Key_Type is (Best_Value (H, False));

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
   begin
      case H.Mode is
         when Buffer =>
            H.Count := H.Count + 1;
            H.Keys (H.Count) := K;

         when Probe_Min =>
            H.Count := H.Count + 1;
            H.Keys (H.Count) := K;
            Build_Min_Heap (H);

         when Probe_Max =>
            H.Count := H.Count + 1;
            H.Keys (H.Count) := K;
            Build_Max_Heap (H);

         when Min_Heap =>
            Insert_Min_Heap (H, K);

         when Max_Heap =>
            Insert_Max_Heap (H, K);

         when Sorted =>
            --  A drain has turned back into mixed traffic. Compact the live
            --  sorted range and let the next removal reveal the favored end.

            if H.Count > 0 and then H.First /= 1 then
               H.Keys (1 .. H.Count) := H.Keys (H.First .. H.Last);
            end if;
            H.Count := H.Count + 1;
            H.Keys (H.Count) := K;
            H.First := 1;
            H.Last := 0;
            H.Mode := Buffer;
      end case;
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
   begin
      case H.Mode is
         when Buffer =>
            Extract_Buffer (H, True, K);

         when Probe_Min | Probe_Max =>
            Radix_Sort (H);
            K := H.Keys (H.First);
            if H.Count > 1 then
               H.First := H.First + 1;
            end if;
            H.Count := H.Count - 1;

         when Min_Heap =>
            Extract_Min_Heap (H, K);

         when Max_Heap =>
            Radix_Sort (H);
            K := H.Keys (H.First);
            if H.Count > 1 then
               H.First := H.First + 1;
            end if;
            H.Count := H.Count - 1;

         when Sorted =>
            K := H.Keys (H.First);
            if H.Count > 1 then
               H.First := H.First + 1;
            end if;
            H.Count := H.Count - 1;
      end case;

      if H.Count = 0 then
         H.First := 1;
         H.Last := 0;
         H.Mode := Buffer;
      end if;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
   begin
      case H.Mode is
         when Buffer =>
            Extract_Buffer (H, False, K);

         when Probe_Min | Probe_Max =>
            Radix_Sort (H);
            K := H.Keys (H.Last);
            H.Last := H.Last - 1;
            H.Count := H.Count - 1;

         when Max_Heap =>
            Extract_Max_Heap (H, K);

         when Min_Heap =>
            Radix_Sort (H);
            K := H.Keys (H.Last);
            H.Last := H.Last - 1;
            H.Count := H.Count - 1;

         when Sorted =>
            K := H.Keys (H.Last);
            H.Last := H.Last - 1;
            H.Count := H.Count - 1;
      end case;

      if H.Count = 0 then
         H.First := 1;
         H.Last := 0;
         H.Mode := Buffer;
      end if;
   end Extract_Max;

end Heaps.Open;
