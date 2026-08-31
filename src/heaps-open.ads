--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Buffered, unrestricted priority queue used by the open benchmark entry.
--
--  This package is not analyzed or proved with SPARK and makes no promise
--  about one fixed representation. It delays the initial build, keeps small
--  queues in an unsorted array, and batches later insertions around an
--  interval heap. Every policy decision depends only on the current
--  representation and size.

with Heaps.Interval;

package Heaps.Open with SPARK_Mode => Off is

   type Heap (Capacity : Extended_Index) is private;

   function Size (H : Heap) return Extended_Index;
   function Is_Empty (H : Heap) return Boolean;
   function Is_Full (H : Heap) return Boolean;

   procedure Clear (H : in out Heap)
     with Post => Is_Empty (H);

   function Peek_Min (H : Heap) return Key_Type
     with Pre => not Is_Empty (H);

   function Peek_Max (H : Heap) return Key_Type
     with Pre => not Is_Empty (H);

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H),
          Post => Size (H) = Size (H)'Old + 1;

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Size (From) <= Into.Capacity - Size (Into),
          Post => Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From);
   --  Destructive meld. Two lazy heaps remain lazy; otherwise a size-based
   --  rule chooses between buffered insertion and an interval-heap rebuild.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H),
          Post => Size (H) = Size (H)'Old - 1;

   procedure Extract_Max (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H),
          Post => Size (H) = Size (H)'Old - 1;

private

   Small_Limit   : constant Extended_Index := 32;
   Pending_Limit : constant Extended_Index := 256;

   type Mode_Kind is (Initial, Active);

   type Heap (Capacity : Extended_Index) is record
      Base : Interval.Heap (Capacity);
      Pending : Interval.Heap (Pending_Limit);

      --  Before the first removal, insertion is genuinely lazy. Staged holds
      --  that initial wave and caches both extremes so Peek remains O(1).

      Staged      : Key_Array (1 .. Capacity);
      Staged_Last : Extended_Index := 0;
      Staged_Min  : Extended_Index := 0;
      Staged_Max  : Extended_Index := 0;
      Mode        : Mode_Kind := Initial;
   end record;

end Heaps.Open;
