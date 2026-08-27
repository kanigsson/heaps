--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Unsorted array "heap": the degenerate priority queue.
--
--  Keys are simply appended, in whatever order they arrive. There is no
--  structural invariant at all -- any array is a valid state -- so insertion
--  is a single store and extraction has to scan. It is the O(1) / O(n) corner
--  of the design space, and the baseline the real heaps have to beat.
--
--  It is also the cleanest illustration of what the platinum contracts buy:
--  since the type has no invariant to speak of, the multiset equations below
--  are the *entire* specification of the unit.
--
--  Verification level: silver, gold and platinum -- see README.md.

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every operation into a quadratic one. Since the contracts are
--  discharged by proof, run-time checking of them is redundant, so assertions
--  are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Unsorted with SPARK_Mode is

   use type Key_Multisets.Multiset;

   type Heap (Capacity : Extended_Index) is record
      Last : Extended_Index := 0;
      Keys : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;

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
     with Post => Is_Empty (H) and Key_Multisets.Is_Empty (Model (H));

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H),
          Post => Is_Minimum (H, Peek_Min'Result)
                  and then (for some I in 1 .. H.Last =>
                              Peek_Min'Result = H.Keys (I));

   procedure Insert (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H),
          Post => Size (H) = Size (H)'Old + 1
                  and Model (H) = Key_Multisets.Add (Model (H)'Old, K);

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H),
          Post => Size (H) = Size (H)'Old - 1
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);
   --  Unlike the binary heap, the result is not tied to Peek_Min: when
   --  several keys are minimal, which one is removed is not observable, and
   --  the two conjuncts above already pin down everything that is. K is a
   --  lower bound of the old contents, and the old contents are exactly the
   --  new contents plus one occurrence of K.

end Heaps.Unsorted;
