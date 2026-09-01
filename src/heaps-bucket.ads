--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Bucket priority queue for a bounded interval of integer keys.
--
--  One doubly linked chain is kept for every key in First_Key .. Last_Key.
--  Nodes occupy a dense prefix, so removing a bucket head moves the physical
--  last node into the hole and repairs at most three links. Insert and peek
--  are O(1); extraction is O(1) unless the minimum bucket becomes empty, in
--  which case it scans forward over empty priorities.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;
with SPARK.Big_Integers;

package Heaps.Bucket with SPARK_Mode is

   use type Key_Multisets.Multiset;
   use type SPARK.Big_Integers.Big_Integer;

   type Link is record
      Prev   : Extended_Index := 0;
      Next   : Extended_Index := 0;
      Length : Extended_Index := 0;
   end record;

   type Link_Array is array (Index range <>) of Link;
   type Bucket_Array is array (Key_Type range <>) of Extended_Index
     with Default_Component_Value => 0;

   type Heap
     (Capacity            : Extended_Index;
      First_Key, Last_Key : Key_Type)
   is record
      Last     : Extended_Index := 0;
      Minimum  : Key_Type := First_Key;
      Has_Min  : Boolean := False;
      Keys     : Key_Array (1 .. Capacity);
      Links    : Link_Array (1 .. Capacity);
      Heads    : Bucket_Array (First_Key .. Last_Key);
      Counts   : Bucket_Array (First_Key .. Last_Key);
   end record
     with Predicate => Last <= Capacity and First_Key <= Last_Key;

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
     with Ghost;

   function Total_From (H : Heap; K : Key_Type)
                        return SPARK.Big_Integers.Big_Natural is
     (SPARK.Big_Integers.To_Big_Integer (H.Counts (K))
      + (if K = H.Last_Key
         then 0
         else Total_From (H, Key_Type'Succ (K))))
     with Ghost,
          Pre => K in H.First_Key .. H.Last_Key,
          Subprogram_Variant => (Increases => K);

   function Bucket_Valid (H : Heap; K : Key_Type) return Boolean is
     ((if H.Counts (K) = 0
         then H.Heads (K) = 0
         else H.Heads (K) in 1 .. H.Last
              and then H.Keys (H.Heads (K)) = K
              and then H.Links (H.Heads (K)).Prev = 0
              and then H.Links (H.Heads (K)).Length = H.Counts (K)))
     with Ghost,
          Pre => K in H.First_Key .. H.Last_Key;

   function Node_Valid (H : Heap; I : Index) return Boolean is
     (H.Keys (I) in H.First_Key .. H.Last_Key
      and then H.Links (I).Length in 1 .. H.Counts (H.Keys (I))
      and then H.Links (I).Prev in 0 .. H.Last
      and then H.Links (I).Next in 0 .. H.Last
      and then
        (if H.Links (I).Prev = 0
         then H.Heads (H.Keys (I)) = I
              and then H.Links (I).Length = H.Counts (H.Keys (I))
         else H.Keys (H.Links (I).Prev) = H.Keys (I)
              and then H.Links (H.Links (I).Prev).Next = I
              and then H.Links (H.Links (I).Prev).Length
                         = H.Links (I).Length + 1)
      and then
        (if H.Links (I).Next = 0
         then H.Links (I).Length = 1
         else H.Keys (H.Links (I).Next) = H.Keys (I)
              and then H.Links (H.Links (I).Next).Prev = I
              and then H.Links (H.Links (I).Next).Length + 1
                         = H.Links (I).Length))
     with Ghost,
          Pre => I <= H.Last;

   function Is_Heap (H : Heap) return Boolean is
     ((H.Last = 0) = (not H.Has_Min)
      and then (for all K in H.First_Key .. H.Last_Key => Bucket_Valid (H, K))
      and then (for all I in 1 .. H.Last => Node_Valid (H, I))
      and then Total_From (H, H.First_Key)
                 = SPARK.Big_Integers.To_Big_Integer (H.Last)
      and then
        (if H.Has_Min
         then H.Minimum in H.First_Key .. H.Last_Key
              and then H.Counts (H.Minimum) > 0
              and then
                (if H.Minimum > H.First_Key
                 then (for all K in H.First_Key .. Key_Type'Pred (H.Minimum) =>
                         H.Counts (K) = 0))))
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
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Peek_Min'Result = H.Minimum
                  and then Is_Minimum (H, Peek_Min'Result);

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H)
                  and then Is_Heap (H)
                  and then K in H.First_Key .. H.Last_Key,
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into)
                  and then From.First_Key >= Into.First_Key
                  and then From.Last_Key <= Into.Last_Key,
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Is_Heap (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Bucket;
