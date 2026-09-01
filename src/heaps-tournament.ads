--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Winner tree with the keys at the leaves and one cached winner at every
--  internal node. Updating a leaf replays only its path to the root.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;
with Heaps.Models;

package Heaps.Tournament with SPARK_Mode is

   use type Key_Multisets.Multiset;

   subtype Tree_Index_Base is Natural range 0 .. 2 * Max_Capacity - 1;
   subtype Tree_Index is Tree_Index_Base range 1 .. Tree_Index_Base'Last;

   type Winner_Array is array (Index range <>) of Extended_Index;
   type Winner_Key_Array is array (Index range <>) of Key_Type;

   type Heap (Capacity : Extended_Index) is record
      Last        : Extended_Index := 0;
      Keys        : Key_Array (1 .. Capacity);
      Winners     : Winner_Array (1 .. Capacity) := [others => 0];
      Winner_Keys : Winner_Key_Array (1 .. Capacity);
   end record
     with Predicate => Last <= Capacity;

   function Leaf_Node (H : Heap; Position : Index) return Tree_Index is
     (Tree_Index (H.Capacity + Position - 1))
     with Pre  => Position <= H.Capacity,
          Post => Leaf_Node'Result in H.Capacity .. 2 * H.Capacity - 1;

   function Position_At (H : Heap; Node : Tree_Index) return Extended_Index is
     (if Node < H.Capacity then H.Winners (Node)
      elsif Node - H.Capacity + 1 <= H.Last
      then Node - H.Capacity + 1
      else 0)
     with Pre => H.Capacity > 0 and then Node <= 2 * H.Capacity - 1;

   function Key_At (H : Heap; Node : Tree_Index) return Key_Type is
     (if Node < H.Capacity then H.Winner_Keys (Node)
      else H.Keys (Node - H.Capacity + 1))
     with Pre => H.Capacity > 0
                 and then Node <= 2 * H.Capacity - 1
                 and then Position_At (H, Node) > 0;

   function Node_Valid (H : Heap; Node : Index) return Boolean is
     (declare
         Left  : constant Tree_Index := 2 * Node;
         Right : constant Tree_Index := Left + 1;
         LP    : constant Extended_Index := Position_At (H, Left);
         RP    : constant Extended_Index := Position_At (H, Right);
      begin
        (if LP = 0 then
            (if RP = 0 then H.Winners (Node) = 0
             else H.Winners (Node) = RP
                    and then H.Winner_Keys (Node) = Key_At (H, Right))
         elsif RP = 0 then
            H.Winners (Node) = LP
              and then H.Winner_Keys (Node) = Key_At (H, Left)
         elsif Key_At (H, Left) <= Key_At (H, Right) then
            H.Winners (Node) = LP
              and then H.Winner_Keys (Node) = Key_At (H, Left)
         else
            H.Winners (Node) = RP
              and then H.Winner_Keys (Node) = Key_At (H, Right)))
     with Ghost,
          Pre => H.Capacity > 1 and then Node < H.Capacity;

   function Internal_Last (H : Heap) return Extended_Index is
     (if H.Capacity = 0 then 0 else H.Capacity - 1);

   function Valid_Range
     (H : Heap; First, Last_Node : Extended_Index) return Boolean is
     (if Last_Node < First then True
      else Node_Valid (H, Index (Last_Node))
        and then Valid_Range (H, First, Last_Node - 1))
     with Ghost,
          Pre => First > 0 and then Last_Node <= Internal_Last (H),
          Subprogram_Variant => (Decreases => Last_Node);

   function Is_Heap (H : Heap) return Boolean is
     (Valid_Range (H, 1, Internal_Last (H)))
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

   function Root_Position (H : Heap) return Extended_Index is
     (if H.Capacity = 1 then 1 else H.Winners (1))
     with Pre => not Is_Empty (H) and then Is_Heap (H);

   function Peek_Min (H : Heap) return Key_Type
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Minimum (H, Peek_Min'Result)
                  and then Peek_Min'Result = H.Keys (Root_Position (H));

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

   procedure Meld (Into : in out Heap; From : in out Heap)
     with Pre  => Is_Heap (Into)
                  and then Is_Heap (From)
                  and then Size (From) <= Into.Capacity - Size (Into),
          Post => Is_Heap (Into)
                  and Size (Into) = Size (Into)'Old + Size (From)'Old
                  and Is_Empty (From)
                  and Model (Into) = Model (Into)'Old + Model (From)'Old;
   --  Destructive meld. The leaf runs are concatenated and both fixed-size
   --  tournament arrays are rebuilt bottom-up, in O(Into.Capacity +
   --  From.Capacity) time.

   procedure Extract_Min (H : in out Heap; K : out Key_Type)
     with Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Is_Heap (H)
                  and Size (H) = Size (H)'Old - 1
                  and K = Peek_Min (H)'Old
                  and Is_Minimum (H'Old, K)
                  and Model (H)'Old = Key_Multisets.Add (Model (H), K);

end Heaps.Tournament;
