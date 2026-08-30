--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Open_Proved with SPARK_Mode is

   procedure Activate (H : in out Heap)
     with Pre  => Valid (H),
          Post => Valid (H)
                  and H.Mode = Active
                  and Size (H) = Size (H)'Old
                  and Model (H) = Model (H)'Old;

   -----------
   -- Valid --
   -----------

   function Valid (H : Heap) return Boolean is
     (if H.Mode = Lazy
      then Interval.Is_Empty (H.Base)
      else Unsorted.Is_Empty (H.Staged) and then Interval.Is_Heap (H.Base));

   -----------
   -- Model --
   -----------

   function Model (H : Heap) return Key_Multisets.Multiset is
     (if H.Mode = Lazy
      then Unsorted.Model (H.Staged)
      else Interval.Model (H.Base));

   ----------------
   -- Is_Minimum --
   ----------------

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (if H.Mode = Lazy
      then Unsorted.Is_Minimum (H.Staged, K)
      else Interval.Is_Minimum (H.Base, K));

   ----------------
   -- Is_Maximum --
   ----------------

   function Is_Maximum (H : Heap; K : Key_Type) return Boolean is
     (if H.Mode = Lazy
      then Unsorted.Is_Maximum (H.Staged, K)
      else Interval.Is_Maximum (H.Base, K));

   ----------
   -- Size --
   ----------

   function Size (H : Heap) return Extended_Index is
     (if H.Mode = Lazy
      then Unsorted.Size (H.Staged)
      else Interval.Size (H.Base));

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (H : Heap) return Boolean is (Size (H) = 0);

   -------------
   -- Is_Full --
   -------------

   function Is_Full (H : Heap) return Boolean is (Size (H) = H.Capacity);

   --------------
   -- Activate --
   --------------

   procedure Activate (H : in out Heap) is
   begin
      if H.Mode = Lazy then
         H.Base.Last := H.Staged.Last;
         H.Base.Keys := H.Staged.Keys;
         Interval.Build (H.Base);
         Unsorted.Clear (H.Staged);
         H.Mode := Active;
      end if;
   end Activate;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      Unsorted.Clear (H.Staged);
      Interval.Clear (H.Base);
      H.Mode := Lazy;
   end Clear;

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (H : Heap) return Key_Type is
   begin
      if H.Mode = Lazy then
         return Unsorted.Peek_Min (H.Staged);
      else
         Interval.Lemma_Root_Is_Minimum (H.Base);
         return Interval.Peek_Min (H.Base);
      end if;
   end Peek_Min;

   --------------
   -- Peek_Max --
   --------------

   function Peek_Max (H : Heap) return Key_Type is
   begin
      if H.Mode = Lazy then
         return Unsorted.Peek_Max (H.Staged);
      else
         Interval.Lemma_Root_Is_Maximum (H.Base);
         return Interval.Peek_Max (H.Base);
      end if;
   end Peek_Max;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
   begin
      if H.Mode = Lazy then
         Unsorted.Insert (H.Staged, K);
      else
         Interval.Insert (H.Base, K);
      end if;
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
   begin
      if Into.Mode = Lazy and then From.Mode = Lazy then
         Unsorted.Meld (Into.Staged, From.Staged);
      else
         Activate (Into);
         Activate (From);
         Interval.Meld (Into.Base, From.Base);
      end if;
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
   begin
      if H.Mode = Lazy then
         Unsorted.Extract_Min (H.Staged, K);
         Activate (H);
      else
         Interval.Extract_Min (H.Base, K);
      end if;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
   begin
      if H.Mode = Lazy then
         Unsorted.Extract_Max (H.Staged, K);
         Activate (H);
      else
         Interval.Extract_Max (H.Base, K);
      end if;
   end Extract_Max;

end Heaps.Open_Proved;
