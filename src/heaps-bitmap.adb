--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

package body Heaps.Bitmap with SPARK_Mode is

   package KM renames Key_Multisets;
   package BI renames SPARK.Big_Integers;

   subtype Count is Extended_Index range 1 .. Max_Capacity;

   function Big (N : Extended_Index) return BI.Big_Integer is
     (BI.To_Big_Integer (N))
     with Ghost;

   ------------------
   -- Model lemmas --
   ------------------

   procedure Lemma_Occ (C : Count_Array; From : Key_Bound)
     with Ghost,
          Post => (for all E in Key_Type =>
                     KM.Nb_Occurence (Model_From (C, From), E)
                     = (if E in From .. Key_Range'Last then Big (C (E))
                        else 0)),
          Subprogram_Variant => (Increases => From);
   --  The model counts every key as many times as its count says

   procedure Lemma_Empty_Model (C : Count_Array; From : Key_Bound)
     with Ghost,
          Pre  => (for all E in From .. Key_Range'Last => C (E) = 0),
          Post => KM.Is_Empty (Model_From (C, From)),
          Subprogram_Variant => (Increases => From);

   procedure Lemma_Count_Bounded (H : Heap; K : Key_Range)
     with Ghost,
          Pre  => Is_Heap (H),
          Post => H.Counts (K) <= H.Size;

   procedure Lemma_No_Counts (H : Heap)
     with Ghost,
          Pre  => Is_Heap (H) and then H.Size = 0,
          Post => (for all E in Key_Range => H.Counts (E) = 0);

   procedure Lemma_Model_Raise
     (Old_C, New_C : Count_Array; K : Key_Range; N : Count)
     with Ghost,
          Pre  => Old_C (K) <= Max_Capacity - N
                  and then New_C (K) = Old_C (K) + N
                  and then (for all E in Key_Range =>
                              (if E /= K then New_C (E) = Old_C (E))),
          Post => Model_From (New_C, 0)
                  = KM.Add (Model_From (Old_C, 0), K, Big (N));

   procedure Lemma_Model_Sum (C, A, B : Count_Array)
     with Ghost,
          Pre  => (for all E in Key_Range =>
                     Natural (C (E)) = Natural (A (E)) + Natural (B (E))),
          Post => Model_From (C, 0)
                  = Model_From (A, 0) + Model_From (B, 0);

   --------------------
   -- Summary lemmas --
   --------------------

   procedure Lemma_Update
     (Up_Old, Up_New, Low_Old, Low_New : Word_Array; J : Natural)
     with Ghost,
          Pre  => Summarizes (Up_Old, Low_Old)
                  and then Up_New'First = 0
                  and then Up_New'Last = Up_Old'Last
                  and then Low_New'First = 0
                  and then Low_New'Last = Low_Old'Last
                  and then J <= Low_Old'Last
                  and then (for all L in Low_Old'Range =>
                              (if L /= J then Low_New (L) = Low_Old (L)))
                  and then (for all I in Up_Old'Range =>
                              (if I /= J / 64 then Up_New (I) = Up_Old (I)))
                  and then (for all B in Bit =>
                              (if B /= J mod 64
                               then Is_Set (Up_New (J / 64), B)
                                    = Is_Set (Up_Old (J / 64), B)))
                  and then Is_Set (Up_New (J / 64), J mod 64)
                           = (Low_New (J) /= 0),
          Post => Summarizes (Up_New, Low_New);
   --  Changing one word of a level, and the one bit above it to match,
   --  keeps the summary

   procedure Lemma_Update_Counts
     (Up_Old, Up_New : Word_Array; C_Old, C_New : Count_Array; K : Key_Range)
     with Ghost,
          Pre  => Summarizes_Counts (Up_Old, C_Old)
                  and then Up_New'First = 0
                  and then Up_New'Last = Up_Old'Last
                  and then (for all E in Key_Range =>
                              (if E /= K then C_New (E) = C_Old (E)))
                  and then (for all I in Up_Old'Range =>
                              (if I /= Natural (K) / 64
                               then Up_New (I) = Up_Old (I)))
                  and then (for all B in Bit =>
                              (if B /= Natural (K) mod 64
                               then Is_Set (Up_New (Natural (K) / 64), B)
                                    = Is_Set (Up_Old (Natural (K) / 64), B)))
                  and then Is_Set (Up_New (Natural (K) / 64),
                                   Natural (K) mod 64)
                           = (C_New (K) /= 0),
          Post => Summarizes_Counts (Up_New, C_New);

   procedure Lemma_Set_Above (Up, Low : Word_Array; J : Natural)
     with Ghost,
          Pre  => Summarizes (Up, Low)
                  and then J <= Low'Last
                  and then Low (J) /= 0,
          Post => Is_Set (Up (J / 64), J mod 64);

   procedure Lemma_Set_Above_Counts (Up : Word_Array; C : Count_Array;
                                     K : Key_Range)
     with Ghost,
          Pre  => Summarizes_Counts (Up, C) and then C (K) /= 0,
          Post => Is_Set (Up (Natural (K) / 64), Natural (K) mod 64);

   procedure Lemma_All_Zero (Up, Low : Word_Array)
     with Ghost,
          Pre  => Summarizes (Up, Low)
                  and then (for all I in Up'Range => Up (I) = 0),
          Post => (for all J in Low'Range => Low (J) = 0);

   procedure Lemma_All_Zero_Counts (Up : Word_Array; C : Count_Array)
     with Ghost,
          Pre  => Summarizes_Counts (Up, C)
                  and then (for all I in Up'Range => Up (I) = 0),
          Post => (for all E in Key_Range => C (E) = 0);

   procedure Lemma_Nonempty (H : Heap)
     with Ghost,
          Pre  => Is_Heap (H) and then H.Size > 0,
          Post => H.Top (0) /= 0;

   procedure Lemma_Descend (Up, Low : Word_Array; I : Natural; B : Bit)
     with Ghost,
          Pre  => Summarizes (Up, Low)
                  and then I <= Up'Last
                  and then (for all L in 0 .. I - 1 => Up (L) = 0)
                  and then Is_Set (Up (I), B)
                  and then (for all D in 0 .. B - 1 =>
                              not Is_Set (Up (I), D)),
          Post => 64 * I + B <= Low'Last
                  and then Low (64 * I + B) /= 0
                  and then (for all L in 0 .. 64 * I + B - 1 =>
                              Low (L) = 0);
   --  The lowest set bit of the first nonzero word of a level leads to the
   --  first nonzero word of the level below

   procedure Lemma_Descend_Counts
     (Up : Word_Array; C : Count_Array; I : Natural; B : Bit)
     with Ghost,
          Pre  => Summarizes_Counts (Up, C)
                  and then I <= Up'Last
                  and then (for all L in 0 .. I - 1 => Up (L) = 0)
                  and then Is_Set (Up (I), B)
                  and then (for all D in 0 .. B - 1 =>
                              not Is_Set (Up (I), D)),
          Post => 64 * I + B < Universe
                  and then C (Key_Type (64 * I + B)) /= 0
                  and then (for all E in 0 .. Key_Type (64 * I + B) - 1 =>
                              C (E) = 0);

   -------------------------
   -- Internal operations --
   -------------------------

   function Min_Key (H : Heap) return Key_Range
     with Pre  => Is_Heap (H) and then H.Size > 0,
          Post => H.Counts (Min_Key'Result) > 0
                  and then (for all E in 0 .. Min_Key'Result - 1 =>
                              H.Counts (E) = 0);

   procedure Lemma_Min_Model (H : Heap; K : Key_Range)
     with Ghost,
          Pre  => H.Counts (K) > 0
                  and then (for all E in 0 .. K - 1 => H.Counts (E) = 0),
          Post => KM.Contains (Model (H), K) and then Is_Minimum (H, K);

   procedure Raise_Count (H : in out Heap; K : Key_Range; N : Count)
     with Pre  => Is_Heap (H) and then N <= H.Capacity - H.Size,
          Post => Is_Heap (H)
                  and H.Size = H.Size'Old + N
                  and Model (H) = KM.Add (Model (H)'Old, K, Big (N))
                  and H.Counts (K) = H'Old.Counts (K) + N
                  and (for all E in Key_Range =>
                         (if E /= K
                          then H.Counts (E) = H'Old.Counts (E)));

   procedure Lower_Count (H : in out Heap; K : Key_Range; N : Count)
     with Pre  => Is_Heap (H) and then N <= H.Counts (K),
          Post => Is_Heap (H)
                  and H.Size = H.Size'Old - N
                  and Model (H)'Old = KM.Add (Model (H), K, Big (N))
                  and H.Counts (K) = H'Old.Counts (K) - N
                  and (for all E in Key_Range =>
                         (if E /= K
                          then H.Counts (E) = H'Old.Counts (E)));

   ---------------
   -- Lemma_Occ --
   ---------------

   procedure Lemma_Occ (C : Count_Array; From : Key_Bound) is
   begin
      if From < Key_Bound'Last then
         Lemma_Occ (C, From + 1);
      end if;
   end Lemma_Occ;

   -----------------------
   -- Lemma_Empty_Model --
   -----------------------

   procedure Lemma_Empty_Model (C : Count_Array; From : Key_Bound) is
   begin
      if From < Key_Bound'Last then
         Lemma_Empty_Model (C, From + 1);
      end if;
   end Lemma_Empty_Model;

   -------------------------
   -- Lemma_Count_Bounded --
   -------------------------

   procedure Lemma_Count_Bounded (H : Heap; K : Key_Range) is
   begin
      Lemma_Occ (H.Counts, 0);
      if H.Counts (K) > 0 then
         pragma Assert (KM.Contains (Model (H), K));
      end if;
   end Lemma_Count_Bounded;

   ---------------------
   -- Lemma_No_Counts --
   ---------------------

   procedure Lemma_No_Counts (H : Heap) is
   begin
      for E in Key_Range loop
         Lemma_Count_Bounded (H, E);
         pragma Loop_Invariant (for all F in 0 .. E => H.Counts (F) = 0);
      end loop;
   end Lemma_No_Counts;

   -----------------------
   -- Lemma_Model_Raise --
   -----------------------

   procedure Lemma_Model_Raise
     (Old_C, New_C : Count_Array; K : Key_Range; N : Count)
   is
      pragma Unreferenced (K, N);
   begin
      Lemma_Occ (Old_C, 0);
      Lemma_Occ (New_C, 0);
   end Lemma_Model_Raise;

   ---------------------
   -- Lemma_Model_Sum --
   ---------------------

   procedure Lemma_Model_Sum (C, A, B : Count_Array) is
   begin
      Lemma_Occ (C, 0);
      Lemma_Occ (A, 0);
      Lemma_Occ (B, 0);
   end Lemma_Model_Sum;

   ------------------
   -- Lemma_Update --
   ------------------

   procedure Lemma_Update
     (Up_Old, Up_New, Low_Old, Low_New : Word_Array; J : Natural)
   is
      pragma Unreferenced (Up_Old, Up_New, Low_Old, Low_New, J);
   begin
      null;
   end Lemma_Update;

   -------------------------
   -- Lemma_Update_Counts --
   -------------------------

   procedure Lemma_Update_Counts
     (Up_Old, Up_New : Word_Array; C_Old, C_New : Count_Array; K : Key_Range)
   is
      pragma Unreferenced (Up_Old, Up_New, C_Old, C_New, K);
   begin
      null;
   end Lemma_Update_Counts;

   ---------------------
   -- Lemma_Set_Above --
   ---------------------

   procedure Lemma_Set_Above (Up, Low : Word_Array; J : Natural) is
      pragma Unreferenced (Up, Low);
   begin
      pragma Assert (64 * (J / 64) + J mod 64 = J);
   end Lemma_Set_Above;

   ----------------------------
   -- Lemma_Set_Above_Counts --
   ----------------------------

   procedure Lemma_Set_Above_Counts (Up : Word_Array; C : Count_Array;
                                     K : Key_Range)
   is
      pragma Unreferenced (Up, C);
   begin
      pragma Assert (64 * (Natural (K) / 64) + Natural (K) mod 64
                     = Natural (K));
   end Lemma_Set_Above_Counts;

   --------------------
   -- Lemma_All_Zero --
   --------------------

   procedure Lemma_All_Zero (Up, Low : Word_Array) is
   begin
      for J in Low'Range loop
         if Low (J) /= 0 then
            Lemma_Set_Above (Up, Low, J);
         end if;
         pragma Loop_Invariant (for all L in 0 .. J => Low (L) = 0);
      end loop;
   end Lemma_All_Zero;

   ---------------------------
   -- Lemma_All_Zero_Counts --
   ---------------------------

   procedure Lemma_All_Zero_Counts (Up : Word_Array; C : Count_Array) is
   begin
      for E in Key_Range loop
         if C (E) /= 0 then
            Lemma_Set_Above_Counts (Up, C, E);
         end if;
         pragma Loop_Invariant (for all F in 0 .. E => C (F) = 0);
      end loop;
   end Lemma_All_Zero_Counts;

   --------------------
   -- Lemma_Nonempty --
   --------------------

   procedure Lemma_Nonempty (H : Heap) is
   begin
      if H.Top (0) = 0 then
         Lemma_All_Zero (H.Top, H.Upper);
         Lemma_All_Zero (H.Upper, H.Middle);
         Lemma_All_Zero (H.Middle, H.Bottom);
         Lemma_All_Zero_Counts (H.Bottom, H.Counts);
         Lemma_Empty_Model (H.Counts, 0);
         pragma Assert (KM.Cardinality (Model (H)) = 0);
      end if;
   end Lemma_Nonempty;

   -------------------
   -- Lemma_Descend --
   -------------------

   procedure Lemma_Descend (Up, Low : Word_Array; I : Natural; B : Bit) is
   begin
      for L in 0 .. 64 * I + B - 1 loop
         pragma Assert (L / 64 <= I);
         if Low (L) /= 0 then
            Lemma_Set_Above (Up, Low, L);
         end if;
         pragma Loop_Invariant (for all M in 0 .. L => Low (M) = 0);
      end loop;
   end Lemma_Descend;

   --------------------------
   -- Lemma_Descend_Counts --
   --------------------------

   procedure Lemma_Descend_Counts
     (Up : Word_Array; C : Count_Array; I : Natural; B : Bit)
   is
   begin
      for E in 0 .. Key_Type (64 * I + B) - 1 loop
         pragma Assert (Natural (E) / 64 <= I);
         if C (E) /= 0 then
            Lemma_Set_Above_Counts (Up, C, E);
         end if;
         pragma Loop_Invariant (for all F in 0 .. E => C (F) = 0);
      end loop;
   end Lemma_Descend_Counts;

   ---------------------
   -- Lemma_Min_Model --
   ---------------------

   procedure Lemma_Min_Model (H : Heap; K : Key_Range) is
      pragma Unreferenced (K);
   begin
      Lemma_Occ (H.Counts, 0);
   end Lemma_Min_Model;

   -------------
   -- Min_Key --
   -------------

   function Min_Key (H : Heap) return Key_Range is
      I1, I2, I3 : Natural;
      B          : Bit;
   begin
      Lemma_Nonempty (H);

      I1 := Lowest (H.Top (0));
      Lemma_Descend (H.Top, H.Upper, 0, I1);

      B := Lowest (H.Upper (I1));
      Lemma_Descend (H.Upper, H.Middle, I1, B);
      I2 := 64 * I1 + B;

      B := Lowest (H.Middle (I2));
      Lemma_Descend (H.Middle, H.Bottom, I2, B);
      I3 := 64 * I2 + B;

      B := Lowest (H.Bottom (I3));
      Lemma_Descend_Counts (H.Bottom, H.Counts, I3, B);
      return Key_Type (64 * I3 + B);
   end Min_Key;

   -----------------
   -- Raise_Count --
   -----------------

   procedure Raise_Count (H : in out Heap; K : Key_Range; N : Count) is
      Old : constant Heap := H with Ghost;
      J3  : constant Natural := Natural (K);
      J2  : constant Natural := J3 / 64;
      J1  : constant Natural := J2 / 64;
      J0  : constant Natural := J1 / 64;
   begin
      Lemma_Count_Bounded (H, K);

      H.Counts (K) := H.Counts (K) + N;
      H.Size := H.Size + N;
      H.Bottom (J2) := With_Bit (H.Bottom (J2), J3 mod 64);
      H.Middle (J1) := With_Bit (H.Middle (J1), J2 mod 64);
      H.Upper (J0) := With_Bit (H.Upper (J0), J1 mod 64);
      H.Top (0) := With_Bit (H.Top (0), J0);

      Lemma_Update_Counts (Old.Bottom, H.Bottom, Old.Counts, H.Counts, K);
      Lemma_Update (Old.Middle, H.Middle, Old.Bottom, H.Bottom, J2);
      Lemma_Update (Old.Upper, H.Upper, Old.Middle, H.Middle, J1);
      Lemma_Update (Old.Top, H.Top, Old.Upper, H.Upper, J0);
      Lemma_Model_Raise (Old.Counts, H.Counts, K, N);
   end Raise_Count;

   -----------------
   -- Lower_Count --
   -----------------

   procedure Lower_Count (H : in out Heap; K : Key_Range; N : Count) is
      Old : constant Heap := H with Ghost;
      J3  : constant Natural := Natural (K);
      J2  : constant Natural := J3 / 64;
      J1  : constant Natural := J2 / 64;
      J0  : constant Natural := J1 / 64;
   begin
      Lemma_Count_Bounded (H, K);
      Lemma_Set_Above_Counts (H.Bottom, H.Counts, K);
      Lemma_Set_Above (H.Middle, H.Bottom, J2);
      Lemma_Set_Above (H.Upper, H.Middle, J1);
      Lemma_Set_Above (H.Top, H.Upper, J0);

      H.Counts (K) := H.Counts (K) - N;
      H.Size := H.Size - N;

      if H.Counts (K) = 0 then
         H.Bottom (J2) := Without_Bit (H.Bottom (J2), J3 mod 64);
         if H.Bottom (J2) = 0 then
            H.Middle (J1) := Without_Bit (H.Middle (J1), J2 mod 64);
            if H.Middle (J1) = 0 then
               H.Upper (J0) := Without_Bit (H.Upper (J0), J1 mod 64);
               if H.Upper (J0) = 0 then
                  H.Top (0) := Without_Bit (H.Top (0), J0);
               end if;
            end if;
         end if;
      end if;

      Lemma_Update_Counts (Old.Bottom, H.Bottom, Old.Counts, H.Counts, K);
      Lemma_Update (Old.Middle, H.Middle, Old.Bottom, H.Bottom, J2);
      Lemma_Update (Old.Upper, H.Upper, Old.Middle, H.Middle, J1);
      Lemma_Update (Old.Top, H.Top, Old.Upper, H.Upper, J0);
      Lemma_Model_Raise (H.Counts, Old.Counts, K, N);
   end Lower_Count;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : out Heap) is
   begin
      H.Size := 0;
      H.Top := [others => 0];
      H.Upper := [others => 0];
      H.Middle := [others => 0];
      H.Bottom := [others => 0];
      H.Counts := [others => 0];
      Lemma_Empty_Model (H.Counts, 0);
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
      K : constant Key_Range := Min_Key (H);
   begin
      Lemma_Min_Model (H, K);
      return K;
   end Peek_Min;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
   begin
      Raise_Count (H, K, 1);
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Old : constant Heap := H with Ghost;
   begin
      K := Min_Key (H);
      Lemma_Min_Model (H, K);
      pragma Assert (Peek_Min (Old) = K);
      Lower_Count (H, K, 1);
   end Extract_Min;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Into_0 : constant Heap := Into with Ghost;
      From_0 : constant Heap := From with Ghost;
      K      : Key_Range;
      N      : Count;
   begin
      while From.Size > 0 loop
         pragma Loop_Invariant (Is_Heap (Into) and then Is_Heap (From));
         pragma Loop_Invariant
           (Into.Size + From.Size = Into_0.Size + From_0.Size);
         pragma Loop_Invariant
           (for all E in Key_Range =>
              Natural (Into.Counts (E)) + Natural (From.Counts (E))
              = Natural (Into_0.Counts (E)) + Natural (From_0.Counts (E)));
         pragma Loop_Variant (Decreases => From.Size);

         K := Min_Key (From);
         N := From.Counts (K);
         Lemma_Count_Bounded (From, K);
         Raise_Count (Into, K, N);
         Lower_Count (From, K, N);
      end loop;

      Lemma_No_Counts (From);
      Lemma_Model_Sum (Into.Counts, Into_0.Counts, From_0.Counts);
   end Meld;

end Heaps.Bitmap;
