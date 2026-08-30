--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Platinum-proved open benchmark entry.
--
--  The strategy is deliberately not tied to a textbook heap. Insertions are
--  staged in an unsorted array until an extraction first requires order. That
--  extraction is performed by the proved linear-scan queue, then the remaining
--  keys are bulk-built into an interval heap in linear time. Later operations
--  use the interval heap directly. Thus an insertion-only phase costs one
--  append per key while mixed and double-ended traffic gets logarithmic
--  extraction after a single materialization step.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Interval;
with Heaps.Key_Multisets;
with Heaps.Unsorted;

package Heaps.Open_Proved with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is private;

   function Valid (H : Heap) return Boolean with Ghost;

   function Model (H : Heap) return Key_Multisets.Multiset with Ghost;

   function Is_Minimum (H : Heap; K : Key_Type) return Boolean with Ghost;

   function Is_Maximum (H : Heap; K : Key_Type) return Boolean with Ghost;

   function Size (H : Heap) return Extended_Index;

   function Is_Empty (H : Heap) return Boolean;

   function Is_Full (H : Heap) return Boolean;

   procedure Clear (H : in out Heap)
     with Post => Valid (H)
                  and Is_Empty (H)
                  and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => Valid (H) and then not Is_Empty (H),
          Post => Is_Minimum (H, Peek_Min'Result);

   function Peek_Max (H : Heap) return Key_Type
     with Pre  => Valid (H) and then not Is_Empty (H),
          Post => Is_Maximum (H, Peek_Max'Result);

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => Valid (H) and then not Is_Full (H),
          Post => Valid (H)
                  and Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Valid (Into)
                  and then Valid (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Valid (Into)
                  and Valid (From)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => Valid (H) and then not Is_Empty (H),
          Post => Valid (H)
                  and Size (H) = Size (H)'Old - 1
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

   procedure Extract_Max (H : in out Heap; K : out Key_Type)
     with Pre  => Valid (H) and then not Is_Empty (H),
          Post => Valid (H)
                  and Size (H) = Size (H)'Old - 1
                  and Is_Maximum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

private

   type Mode_Kind is (Lazy, Active);

   type Heap (Capacity : Extended_Index) is record
      Staged : Unsorted.Heap (Capacity);
      Base   : Interval.Heap (Capacity);
      Mode   : Mode_Kind := Lazy;
   end record;

end Heaps.Open_Proved;
