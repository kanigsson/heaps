--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Radix with SPARK_Mode is

   package KM renames Key_Multisets;

   function Bucket_Of (K, Base : Key_Type) return Bucket_Index is
      Distance : constant Key_Type := K - Base;
      Power    : Key_Type := 2 ** (Bucket_Index'Last - 1);
   begin
      if Distance = 0 then
         return 0;
      end if;

      --  A non-negative machine integer has at most Size - 1 value bits.
      --  Walking the powers from high to low avoids a shifting overflow at
      --  the sign bit and returns the bit length of K - Base.
      for B in reverse Bucket_Index'First .. Bucket_Index'Last - 1 loop
         pragma Loop_Invariant (Power = Power_Of_Two (B));
         pragma Loop_Invariant
           (if B < Bucket_Index'Last - 1
            then Distance < 2 * Power);
         if Distance >= Power then
            return B + 1;
         end if;
         Power := Power / 2;
      end loop;

      return 1;
   end Bucket_Of;

   procedure Lemma_Power_Monotonic (Left, Right : Value_Bit)
     with Ghost,
          Pre  => Left <= Right,
          Post => Power_Of_Two (Left) <= Power_Of_Two (Right),
          Subprogram_Variant => (Decreases => Right - Left);

   procedure Lemma_Power_Monotonic (Left, Right : Value_Bit) is
   begin
      if Left < Right then
         Lemma_Power_Monotonic (Left + 1, Right);
      end if;
   end Lemma_Power_Monotonic;

   procedure Lemma_Earlier_Bucket (Base, A, B : Key_Type)
     with Ghost,
          Pre  => Base >= 0
                  and then A >= Base
                  and then B >= Base
                  and then Bucket_Of (A, Base) < Bucket_Of (B, Base),
          Post => A < B;

   procedure Lemma_Earlier_Bucket (Base, A, B : Key_Type) is
      BA : constant Bucket_Index := Bucket_Of (A, Base);
      BB : constant Bucket_Index := Bucket_Of (B, Base);
   begin
      if BA > 0 then
         Lemma_Power_Monotonic (BA, BB - 1);
      end if;
   end Lemma_Earlier_Bucket;

   procedure Lemma_Minima_Equal (H : Heap; A, B : Key_Type)
     with Ghost,
          Pre  => Is_Minimum (H, A)
                  and then Is_Minimum (H, B)
                  and then (for some I in 1 .. H.Last => A = H.Keys (I))
                  and then (for some I in 1 .. H.Last => B = H.Keys (I)),
          Post => A = B;

   procedure Lemma_Minima_Equal (H : Heap; A, B : Key_Type) is
   begin
      for I in 1 .. H.Last loop
         if H.Keys (I) = A then
            pragma Assert (B <= A);
         end if;
         if H.Keys (I) = B then
            pragma Assert (A <= B);
         end if;
      end loop;
   end Lemma_Minima_Equal;

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
      H.Base := 0;
   end Clear;

   function Minimum_At (H : Heap) return Index
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Minimum_At'Result <= H.Last
                  and then Is_Minimum (H, H.Keys (Minimum_At'Result));

   function Minimum_At (H : Heap) return Index is
      Best : Index := 1;
   begin
      for I in 2 .. H.Last loop
         if H.Bucket (I) < H.Bucket (Best) then
            Lemma_Earlier_Bucket (H.Base, H.Keys (I), H.Keys (Best));
            Best := I;
         elsif H.Bucket (I) = H.Bucket (Best)
           and then H.Keys (I) < H.Keys (Best)
         then
            Best := I;
         else
            if H.Bucket (Best) < H.Bucket (I) then
               Lemma_Earlier_Bucket (H.Base, H.Keys (Best), H.Keys (I));
            end if;
         end if;

         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (Best) <= H.Keys (J));
      end loop;
      return Best;
   end Minimum_At;

   function Peek_Min (H : Heap) return Key_Type is
   begin
      return H.Keys (Minimum_At (H));
   end Peek_Min;

   procedure Insert (H : in out Heap; K : Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;
   begin
      H.Last := H.Last + 1;
      H.Keys (H.Last) := K;
      H.Bucket (H.Last) := Bucket_Of (K, H.Base);

      pragma Assert (Is_Heap (H));
      Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Before, H.Last - 1),
         Models.Occurrences (H.Keys, H.Last - 1), K);
   end Insert;

   procedure Meld (Into : in out Heap; From : in out Heap) is
      M0   : constant KM.Multiset := Model (Into) with Ghost;
      Base : constant Extended_Index := Into.Last;
   begin
      for I in 1 .. From.Last loop
         pragma Assert (From.Keys (I) >= From.Base);
         pragma Assert (From.Keys (I) >= Into.Base);
         Insert (Into, From.Keys (I));
         Models.Lemma_Sum_Add
           (M0, Models.Occurrences (From.Keys, I - 1), From.Keys (I));
         Models.Lemma_Sum_Empty (M0);

         pragma Loop_Invariant (Is_Heap (Into));
         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant (Into.Base = Into.Base'Loop_Entry);
         pragma Loop_Invariant
           (Model (Into) = M0 + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (M0);
      end if;

      Clear (From);
   end Meld;

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Before          : constant Key_Array := H.Keys with Ghost;
      Old_Model       : constant KM.Multiset := Model (H) with Ghost;
      Old_Base        : constant Key_Type := H.Base;
      Old_Last        : constant Index := H.Last;
      Expected        : constant Key_Type := Peek_Min (H) with Ghost;
      Min_At          : constant Index := Minimum_At (H);
      Remaining_Model : KM.Multiset with Ghost;
   begin
      K := H.Keys (Min_At);
      Lemma_Minima_Equal (H, K, Expected);
      pragma Assert (K >= Old_Base);

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
      pragma Assert (Old_Model = KM.Add (Remaining_Model, K));
      pragma Assert (for all I in 1 .. H.Last => K <= H.Keys (I));

      --  Moving Base changes every bucket boundary. The dense representation
      --  makes redistribution one linear pass over the surviving keys.
      H.Base := K;
      for I in 1 .. H.Last loop
         H.Bucket (I) := Bucket_Of (H.Keys (I), H.Base);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              H.Keys (J) >= H.Base
              and then H.Bucket (J) = Bucket_Of (H.Keys (J), H.Base));
      end loop;

      pragma Assert (Is_Heap (H));
      Models.Lemma_Add_Congruent (Model (H), Remaining_Model, K);
   end Extract_Min;

end Heaps.Radix;
