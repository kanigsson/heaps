--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Priority queue backed by an unsorted key array and a directory containing
--  one minimum per fixed-size block.
--
--  Insertion appends a key and updates one directory entry. Extraction first
--  scans the directory, then scans only the winning block; removing the key
--  can require rebuilding two block entries. With block size B and n keys,
--  insertion is O(1), while peek and extraction are O(n / B) and
--  O(n / B + B), respectively. The fixed B = 256 is a practical compromise
--  for the capacities exercised by this collection.
--
--  Verification level: silver, gold and platinum -- see README.md.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Block_Min with SPARK_Mode is

   use type Key_Multisets.Multiset;

   Block_Size : constant Index := 256;

   function Blocks_For (N : Extended_Index) return Extended_Index is
     (if N = 0 then 0 else 1 + (N - 1) / Block_Size);

   function Block_Number (I : Index) return Index is
     (1 + (I - 1) / Block_Size)
     with Post => Block_Number'Result <= I;

   function Block_First (B : Index) return Index is
     (1 + (B - 1) * Block_Size)
     with Pre  => B <= Blocks_For (Max_Capacity),
          Post => Block_Number (Block_First'Result) = B;

   function Block_Last
     (B : Index; Last : Extended_Index) return Index is
     (Index'Min (B * Block_Size, Last))
     with Pre  => Last > 0 and then B <= Blocks_For (Last),
          Post => Block_Number (Block_Last'Result) = B
                  and then Block_Last'Result <= Last;

   type Winner_Array is array (Index range <>) of Extended_Index;

   type Heap
     (Capacity           : Extended_Index;
      Directory_Capacity : Extended_Index)
   is record
      Last    : Extended_Index := 0;
      Keys    : Key_Array (1 .. Capacity);
      Winners : Winner_Array (1 .. Directory_Capacity);
   end record
     with Predicate => Last <= Capacity
                       and Directory_Capacity = Blocks_For (Capacity);

   function Block_Valid (H : Heap; B : Index) return Boolean is
     (H.Winners (B) in Block_First (B) .. Block_Last (B, H.Last)
      and then
        (for all I in Block_First (B) .. Block_Last (B, H.Last) =>
           H.Keys (H.Winners (B)) <= H.Keys (I)))
     with Ghost,
          Pre => B <= Blocks_For (H.Last);

   function Is_Heap (H : Heap) return Boolean is
     (for all B in 1 .. Blocks_For (H.Last) => Block_Valid (H, B))
     with Ghost;

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean is
     (for all I in 1 .. H.Last => K <= H.Keys (I))
     with Ghost;

   function Model (H : Heap) return Key_Multisets.Multiset is
     (Models.Occurrences (H.Keys, H.Last))
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
          Post => Is_Minimum (H, Peek_Min'Result)
                  and then (for some I in 1 .. H.Last =>
                              Peek_Min'Result = H.Keys (I));

   function Min_Of (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Minimum (H, Min_Of'Result)
                  and then (for some I in 1 .. H.Last =>
                              Min_Of'Result = H.Keys (I));

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Block_Min;
