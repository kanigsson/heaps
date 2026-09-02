--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Monotone radix heap for non-negative integer keys.
--
--  Bucket B holds the keys in Bound (B - 1) + 1 .. Bound (B), and bucket 0
--  holds exactly Base. The boundaries are state rather than a function of
--  Base: extracting the minimum recomputes only the boundaries below the
--  bucket it empties, so every bucket above that one keeps both its range
--  and its contents. Redistribution therefore touches one bucket, not the
--  whole queue, and a key can only ever move to a lower bucket.
--
--  The buckets are contiguous runs of one dense key array delimited by
--  Starts, so membership is a range property rather than a reachability one
--  and redistributing an emptied bucket is a partition of a single run.
--
--  Insertions must not go backwards: K >= Base.

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
   --  One bucket per bit length of the distance from the base, plus a top
   --  bucket that runs to the end of the key range.

   subtype Start_Index is Natural range 0 .. Bucket_Index'Last + 1;
   --  Run B occupies Starts (B) .. Starts (B + 1) - 1, so the delimiters run
   --  one past the last bucket.

   subtype Split_Bit is Natural range 0 .. Bucket_Index'Last - 1;

   function Power_Of_Two (B : Split_Bit) return Key_Type is (2 ** B)
     with Post => Power_Of_Two'Result >= 1
                  and then Power_Of_Two'Result <= 2 ** Split_Bit'Last;

   subtype Delimiter is Positive range 1 .. Max_Capacity + 1;
   --  A run delimiter is one past the end of the dense prefix at most.

   type Bound_Array is array (Bucket_Index) of Key_Type;
   type Start_Array is array (Start_Index) of Delimiter;

   Initial_Bound : constant Bound_Array :=
     [for B in Bucket_Index =>
        (if B = Bucket_Index'Last then Key_Type'Last else 2 ** B - 1)];
   --  The layout of an empty heap, whose base is zero: bucket B ends at
   --  2 ** B - 1, so its width is 2 ** (B - 1), and the top bucket absorbs
   --  everything above.

   type Heap (Capacity : Extended_Index) is record
      Last   : Extended_Index := 0;
      Base   : Key_Type := 0;
      Bound  : Bound_Array := Initial_Bound;
      Starts : Start_Array := [others => 1];
      Keys   : Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity and Base >= 0;

   ---------------------------
   -- Structural properties --
   ---------------------------

   function Starts_Sorted (H : Heap) return Boolean is
     (for all A in Start_Index =>
        (for all B in Start_Index =>
           (if A <= B then H.Starts (A) <= H.Starts (B))))
     with Ghost;

   function Bounds_Sorted (H : Heap) return Boolean is
     (for all A in Bucket_Index =>
        (for all B in Bucket_Index =>
           (if A <= B then H.Bound (A) <= H.Bound (B))))
     with Ghost;
   --  Stated over every pair rather than over adjacent ones: the ordering of
   --  two arbitrary buckets is what the minimum argument needs, and lifting
   --  it from the adjacent form at each use would cost a lemma call there
   --  instead of once at each update.

   function Runs_Delimited (H : Heap) return Boolean is
     (H.Starts (0) = 1
      and then H.Starts (Start_Index'Last) = H.Last + 1
      and then Starts_Sorted (H))
     with Ghost;
   --  The runs tile 1 .. Last in bucket order.

   function Is_Heap (H : Heap) return Boolean is
     (Runs_Delimited (H)
      and then H.Bound (0) = H.Base
      and then H.Bound (Bucket_Index'Last) = Key_Type'Last
      and then Bounds_Sorted (H)
      and then
        (for all B in Bucket_Index =>
           (for all I in H.Starts (B) .. H.Starts (B + 1) - 1 =>
              H.Keys (I) <= H.Bound (B)
              and then (if B = 0
                        then H.Keys (I) = H.Base
                        else H.Keys (I) > H.Bound (B - 1)))))
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

   function Bucket_For (H : Heap; K : Key_Type) return Bucket_Index
     with Pre  => Is_Heap (H) and then K >= H.Base,
          Post => K <= H.Bound (Bucket_For'Result)
                  and then (if Bucket_For'Result > 0
                            then K > H.Bound (Bucket_For'Result - 1));
   --  The bucket K belongs to under the current boundaries.

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
   --  O(Bucket_Index'Last): the key joins its bucket, and every run above
   --  that bucket slides up by one slot, which moves one key per run.

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
   --  Amortized O(Bucket_Index'Last): the lowest non-empty bucket is scanned
   --  for its minimum, that key becomes the new base, and only that one
   --  bucket is redistributed over the buckets below it. Every other bucket
   --  keeps its range, so a key descends at most once per bucket over its
   --  whole life in the queue.

end Heaps.Radix;
