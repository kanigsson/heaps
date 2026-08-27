--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Adaptive, unrestricted priority queue used by the open benchmark entry.
--
--  Unlike the canonical heaps in this collection, this package is not
--  currently analyzed or proved with SPARK and makes no promise about one
--  fixed representation. It obeys the same online min/max queue semantics for
--  arbitrary Key_Type values, but adapts to the operations already observed
--  and uses a second Capacity-sized array as scratch storage.

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

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H),
          Post => Size (H) = Size (H)'Old - 1;

   procedure Extract_Max (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H),
          Post => Size (H) = Size (H)'Old - 1;

private

   type Mode_Kind is
     (Buffer, Probe_Min, Probe_Max, Min_Heap, Max_Heap, Sorted);

   type Heap (Capacity : Extended_Index) is record
      Keys    : Key_Array (1 .. Capacity);
      Scratch : Key_Array (1 .. Capacity);
      Count   : Extended_Index := 0;
      Mode    : Mode_Kind := Buffer;

      --  Only Sorted uses Keys (First .. Last). Every other representation
      --  uses Keys (1 .. Count).

      First : Index := 1;
      Last  : Extended_Index := 0;
   end record
     with Predicate => Count <= Capacity;

end Heaps.Open;
