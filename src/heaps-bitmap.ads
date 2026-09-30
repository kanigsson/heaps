--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Hierarchical bitmap queue for the integer keys 0 .. Universe - 1.
--
--  Every key has a count. Above the counts sit four levels of 64-bit words:
--  bit B of bottom word I is set when key 64 * I + B has a nonzero count, bit
--  B of a word on any higher level is set when word 64 * I + B of the level
--  below is nonzero, and the top level is a single word. The minimum is found
--  by taking the lowest set bit on each level in turn, four trailing-zero
--  counts from the top, whatever the number of keys held.
--
--  Insertion sets one bit on every level, unconditionally. Extraction clears
--  a bit from the bottom up and stops at the first word that stays nonzero.
--
--  No key is stored: the counts are the contents, and the model is built
--  from them.

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

with Heaps.Key_Multisets;
with Heaps.Words;
with SPARK.Big_Integers;

generic
   Universe : Index;
   --  The number of distinct keys. Four levels of 64 cover up to 2 ** 24.

package Heaps.Bitmap with SPARK_Mode, Always_Terminates is

   use type Key_Multisets.Multiset;
   use type SPARK.Big_Integers.Big_Integer;
   use Heaps.Words;
   use type Word;

   subtype Key_Range is Key_Type range 0 .. Key_Type (Universe) - 1;

   subtype Key_Bound is Key_Type range 0 .. Key_Type (Universe);
   --  A key or one past the last one

   Bottom_Words : constant Positive := (Universe + 63) / 64;
   Middle_Words : constant Positive := (Bottom_Words + 63) / 64;
   Upper_Words  : constant Positive := (Middle_Words + 63) / 64;
   --  At most 2 ** 18, 2 ** 12 and 64 words. The top level is one word.

   type Word_Array is array (Natural range <>) of Word
     with Default_Component_Value => 0;

   type Count_Array is array (Key_Range) of Extended_Index
     with Default_Component_Value => 0;

   type Heap (Capacity : Extended_Index) is record
      Size   : Extended_Index := 0;
      Top    : Word_Array (0 .. 0);
      Upper  : Word_Array (0 .. Upper_Words - 1);
      Middle : Word_Array (0 .. Middle_Words - 1);
      Bottom : Word_Array (0 .. Bottom_Words - 1);
      Counts : Count_Array;
   end record
     with Predicate => Size <= Capacity;

   -----------
   -- Model --
   -----------

   function Model_From (C : Count_Array; From : Key_Bound)
                        return Key_Multisets.Multiset is
     (if From = Key_Bound'Last then Key_Multisets.Empty_Multiset
      elsif C (From) = 0 then Model_From (C, From + 1)
      else Key_Multisets.Add
             (Model_From (C, From + 1), From,
              SPARK.Big_Integers.To_Big_Integer (C (From))))
     with Ghost,
          Subprogram_Variant => (Increases => From);
   --  The keys From and above, each as many times as it is counted

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Model_From (H.Counts, 0))
     with Ghost;

   -----------------------
   -- Summary structure --
   -----------------------

   function Summarizes (Up, Low : Word_Array) return Boolean is
     (Up'First = 0
      and then Low'First = 0
      and then Low'Last / 64 <= Up'Last
      and then Up'Last < 2 ** 18
      and then
        (for all I in Up'Range =>
           (for all B in Bit =>
              Is_Set (Up (I), B)
              = (64 * I + B <= Low'Last and then Low (64 * I + B) /= 0))))
     with Ghost;
   --  Every bit of Up says whether the word of Low it stands for is nonzero,
   --  and the bits past the end of Low are clear

   function Summarizes_Counts (Up : Word_Array; C : Count_Array)
                               return Boolean is
     (Up'First = 0
      and then Up'Last = Bottom_Words - 1
      and then
        (for all I in Up'Range =>
           (for all B in Bit =>
              Is_Set (Up (I), B)
              = (64 * I + B < Universe
                 and then C (Key_Type (64 * I + B)) /= 0))))
     with Ghost;
   --  The same, for the bottom level over the counts

   function Is_Heap (H : Heap) return Boolean is
     (SPARK.Big_Integers.To_Big_Integer (H.Size)
        = Key_Multisets.Cardinality (Model (H))
      and then Summarizes (H.Top, H.Upper)
      and then Summarizes (H.Upper, H.Middle)
      and then Summarizes (H.Middle, H.Bottom)
      and then Summarizes_Counts (H.Bottom, H.Counts))
     with Ghost;

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all E of Model (H) => K <= E)
     with Ghost;

   ----------------
   -- Operations --
   ----------------

   function Size (H : Heap) return Extended_Index is (H.Size);

   function Is_Empty (H : Heap) return Boolean is (H.Size = 0);

   function Is_Full (H : Heap) return Boolean is (H.Size = H.Capacity);

   procedure Clear (H : out Heap)
     with Post => Is_Empty (H)
                  and Is_Heap (H)
                  and Key_Multisets.Is_Empty (Model (H));
   --  Linear in the universe

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Key_Multisets.Contains (Model (H), Peek_Min'Result)
                  and then Is_Minimum (H, Peek_Min'Result);

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H)
                  and then Is_Heap (H)
                  and then K in Key_Range,
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Is_Heap (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Moves the keys of From one distinct key at a time, in increasing order

end Heaps.Bitmap;
