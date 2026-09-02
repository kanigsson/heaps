--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Monotone radix heap for non-negative integer keys.
--
--  Bucket 0 contains keys equal to Base. Bucket B > 0 contains keys whose
--  distance from Base has bit length B. Insertions must not go backwards:
--  K >= Base. Extraction advances Base to the minimum key and redistributes
--  the dense bucket tags of the surviving keys.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Radix with SPARK_Mode is

   use type Key_Multisets.Multiset;
   subtype Bucket_Index is Natural range 0 .. Key_Type'Size - 1;
   subtype Value_Bit is Natural range 0 .. Bucket_Index'Last - 1;

   function Power_Of_Two (B : Value_Bit) return Key_Type is (2 ** B);

   type Bucket_Tag_Array is array (Index range <>) of Bucket_Index;

   type Heap (Capacity : Extended_Index) is record
      Last   : Extended_Index := 0;
      Base   : Key_Type := 0;
      Keys   : Key_Array (1 .. Capacity);
      Bucket : Bucket_Tag_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity and Base >= 0;

   function Bucket_Of (K, Base : Key_Type) return Bucket_Index
     with Pre  => Base >= 0 and then K >= Base,
          Post => (Bucket_Of'Result = 0) = (K = Base)
                  and then
                    (if Bucket_Of'Result > 0
                     then K - Base >=
                            Power_Of_Two (Bucket_Of'Result - 1))
                  and then
                    (if Bucket_Of'Result < Bucket_Index'Last
                     then K - Base < Power_Of_Two (Bucket_Of'Result));

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
     with Ghost;

   function Is_Heap (H : Heap) return Boolean is
     (for all I in 1 .. H.Last =>
        H.Keys (I) >= H.Base
        and then H.Bucket (I) = Bucket_Of (H.Keys (I), H.Base))
     with Ghost;

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => K <= H.Keys (I))
     with Ghost;

   function Size (H : Heap) return Extended_Index is (H.Last);
   function Is_Empty (H : Heap) return Boolean is (H.Last = 0);
   function Is_Full (H : Heap) return Boolean is (H.Last = H.Capacity);

   procedure Clear (H : in out Heap)
     with Post => Is_Empty (H)
                  and Is_Heap (H)
                  and H.Base = 0
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, Peek_Min'Result)
                  and then (for some I in 1 .. H.Last =>
                              Peek_Min'Result = H.Keys (I));

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H)
                  and then Is_Heap (H)
                  and then K >= H.Base,
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and H.Base = H.Base'Old
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into)
                  and then (for all I in 1 .. From.Last =>
                              From.Keys (I) >= Into.Base),
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Into.Base = Into.Base'Old
                  and Is_Empty (From)
                  and Is_Heap (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and H.Base = K
                  and H.Base >= H.Base'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Radix;
