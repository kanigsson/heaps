--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Sorted linked list in a bounded array-backed node pool.
--
--  Active nodes occupy a dense prefix of the arrays, while Prev and Next
--  encode their nondecreasing key order. Position and Order are inverse rank
--  certificates for that list: they make link integrity and ordering flat
--  predicates, rather than recursive reachability properties. Insertion is
--  linear, and minimum lookup and extraction are constant-time.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Sorted_Linked with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Link is record
      Prev     : Extended_Index := 0;
      Next     : Extended_Index := 0;
      Position : Extended_Index := 0;
   end record;

   type Link_Array is array (Index range <>) of Link;
   type Position_Array is array (Index range <>) of Extended_Index;

   type Heap (Capacity : Extended_Index) is record
      Last  : Extended_Index := 0;
      Head  : Extended_Index := 0;
      Keys  : Key_Array (1 .. Capacity);
      Links : Link_Array (1 .. Capacity);
      Order    : Position_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Node_Valid (H : Heap; I : Index) return Boolean is
     (H.Links (I).Position in 1 .. H.Last
      and then H.Order (H.Links (I).Position) = I)
     with Ghost,
          Pre => I <= H.Last;

   function Position_Valid (H : Heap; P : Index) return Boolean is
     (H.Order (P) in 1 .. H.Last
      and then H.Links (H.Order (P)).Position = P
      and then H.Links (H.Order (P)).Prev
        = (if P = H.Last then 0 else H.Order (P + 1))
      and then H.Links (H.Order (P)).Next
        = (if P = 1 then 0 else H.Order (P - 1)))
     with Ghost,
          Pre => P <= H.Last;

   function Is_Sorted (H : Heap) return Boolean is
     ((H.Last = 0) = (H.Head = 0)
      and then (if H.Last > 0 then H.Head = H.Order (H.Last))
      and then
        (for all I in 1 .. H.Last => Node_Valid (H, I))
      and then
        (for all P in 1 .. H.Last => Position_Valid (H, P))
      and then
        (for all P in 2 .. H.Last =>
           H.Keys (H.Order (P)) <= H.Keys (H.Order (P - 1))))
     with Ghost;

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => K <= H.Keys (I))
     with Ghost;

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
     with Ghost;

   ----------------
   -- Operations --
   ----------------

   function Size (H : Heap) return Extended_Index is (H.Last);

   function Is_Empty (H : Heap) return Boolean is (H.Last = 0);

   function Is_Full (H : Heap) return Boolean is (H.Last = H.Capacity);

   procedure Clear (H : in out Heap)
     with Post => Is_Empty (H)
                  and Is_Sorted (H)
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H) and then Is_Sorted (H),
          Post => Peek_Min'Result = H.Keys (H.Head)
                  and then Is_Minimum (H, Peek_Min'Result);

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H) and then Is_Sorted (H),
          Post => Is_Sorted (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Sorted (Into)
                  and then Is_Sorted (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Is_Sorted (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Is_Sorted (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Destructive meld. Keys are removed from From in order and inserted into
   --  Into, so no temporary capacity-sized array is needed. With m source
   --  keys and n destination keys this implementation is O(m (n + m)).

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Sorted (H),
          Post => Is_Sorted (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Sorted_Linked;
