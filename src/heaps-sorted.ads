--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Sorted array "heap": the other degenerate priority queue.
--
--  Keys are kept in non-increasing order, so the minimum sits at the end of
--  the array and extraction is a decrement; insertion has to shift the tail
--  to open a slot. Decreasing rather than increasing order is what makes
--  removal free: dropping the last slot needs no shifting.

--  The ghost model cannot reasonably be evaluated at run time, and the
--  contracts are discharged by proof, so assertions are disabled here.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Sorted with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Is_Sorted (H : Heap) return Boolean is
     (for all I in 2 .. H.Last => H.Keys (I - 1) >= H.Keys (I))
     with Ghost;
   --  Keys (1 .. Last) is non-increasing, so the smallest key is the last one

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

   function Peek_Min (H : Heap) return Key_Type is (H.Keys (H.Last))
     with Pre => not Is_Empty (H);

   procedure Lemma_Last_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Sorted (H),
          Post => Is_Minimum (H, Peek_Min (H));
   --  Is_Sorted only relates neighbours; that the last key is a lower bound
   --  of the whole array is the induction that walks the chain backwards.

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
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Destructive meld: Into receives every key of From, which is left empty.
   --
   --  This is the one entry whose meld is neither an append and a rebuild nor
   --  a splice, but the merge of two sorted runs, in O(n + m). It runs
   --  backwards -- taking the smaller of the two remaining minima and writing
   --  it at the far end of the array, working towards the front -- because
   --  the output slot then always sits above the part of Into's own run that
   --  is still to be read, and no key has to be copied out of the way.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Sorted (H),
          Post => Is_Sorted (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Sorted;
