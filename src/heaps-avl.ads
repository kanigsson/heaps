--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  AVL trees used as priority queues, sharing one fixed-capacity node arena.
--
--  A tree is a binary search tree whose minimum is its leftmost node, kept
--  balanced by rotations: every node caches its height, and a node whose two
--  subtrees differ in height by more than one is rotated back into balance on
--  the way up from an insertion or a removal. Insert and Extract_Min walk one
--  path from the root, so both are logarithmic, and Peek_Min walks the left
--  spine. Equal keys are allowed on either side of a node.
--
--  The arena is package state and a tree is named by its root, as in the
--  leftist unit, and a meld moves the nodes of one tree into the other one at
--  a time, without allocating or freeing any.
--
--  Only the links, sizes and heights are executable. The cached model of
--  every subtree is ghost, and so is the free chain's bookkeeping.

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

with Heaps.Key_Multisets;

generic
   Capacity : Index;

package Heaps.AVL with SPARK_Mode, Always_Terminates is

   use type Key_Multisets.Multiset;

   subtype Tree is Extended_Index range 0 .. Capacity;
   subtype Slot is Tree range 1 .. Capacity;

   type Snapshot is private with Ghost;

   function Snap return Snapshot with Ghost;
   function Valid (S : Snapshot) return Boolean with Ghost;
   function In_Use (S : Snapshot; I : Slot) return Boolean with Ghost;
   function Is_Root (S : Snapshot; T : Tree) return Boolean with Ghost;
   function Model (S : Snapshot; T : Tree)
     return Key_Multisets.Multiset with Ghost;
   function Size_In (S : Snapshot; T : Tree) return Extended_Index
     with Ghost;
   function Room_In (S : Snapshot) return Extended_Index with Ghost;
   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type)
     return Boolean with Ghost;

   function Valid return Boolean is (Valid (Snap)) with Ghost;
   function Is_Root (T : Tree) return Boolean is (Is_Root (Snap, T))
     with Ghost;
   function Model (T : Tree) return Key_Multisets.Multiset is
     (Model (Snap, T)) with Ghost;

   Nodes : constant Extended_Index := Capacity;

   function Room return Extended_Index;

   function Size_Of (T : Tree) return Extended_Index
     with Pre  => Valid and then Is_Root (T),
          Post => (Size_Of'Result = 0) = (T = 0)
                  and then Size_Of'Result = Size_In (Snap, T);

   function Is_Empty (T : Tree) return Boolean is (T = 0);

   procedure Clear
     with Post => Valid and Room = Capacity;

   function Peek_Min (T : Tree) return Key_Type
     with Pre  => Valid and then Is_Root (T) and then T /= 0,
          Post => Is_Minimum (Snap, T, Peek_Min'Result)
                  and then Key_Multisets.Contains (Model (T), Peek_Min'Result);
   --  Walks the left spine

   procedure Insert (T : in out Tree; K : Key_Type)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Room >= 1
                  and then Size_Of (T) < Capacity,
          Post => Valid
                  and Is_Root (T)
                  and Room = Room'Old - 1
                  and Size_In (Snap, T) = Size_In (Snap'Old, T'Old) + 1
                  and Model (Snap, T)
                      = Key_Multisets.Add (Model (Snap'Old, T'Old), K)
                  and (for all U in Tree =>
                         (if U /= T'Old and then Is_Root (Snap'Old, U)
                          then Is_Root (Snap, U)
                               and then Model (Snap, U)
                                         = Model (Snap'Old, U)));

   procedure Extract_Min (T : in out Tree; K : out Key_Type)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then T /= 0
                  and then Room < Capacity,
          Post => Valid
                  and Is_Root (T)
                  and Room = Room'Old + 1
                  and Size_In (Snap, T) = Size_In (Snap'Old, T'Old) - 1
                  and K = Peek_Min (T)'Old
                  and Is_Minimum (Snap'Old, T'Old, K)
                  and Model (Snap'Old, T'Old)
                      = Key_Multisets.Add (Model (Snap, T), K)
                  and (for all U in Tree =>
                         (if U /= T'Old and then Is_Root (Snap'Old, U)
                          then Is_Root (Snap, U)
                               and then Model (Snap, U)
                                         = Model (Snap'Old, U)));
   --  Room < Capacity says the arena is not wholly empty, which T /= 0
   --  implies, but only through a counting argument the flat invariant
   --  avoids; it is asked of the caller, as in the leftist unit.

   procedure Meld (T : in out Tree; U : in out Tree)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Is_Root (U)
                  and then (if T /= 0 and then U /= 0 then T /= U)
                  and then Size_Of (T) + Size_Of (U) <= Capacity,
          Post => Valid
                  and Is_Root (T)
                  and U = 0
                  and Room = Room'Old
                  and Size_In (Snap, T)
                      = Size_In (Snap'Old, T'Old) + Size_In (Snap'Old, U'Old)
                  and Model (Snap, T)
                      = Model (Snap'Old, T'Old) + Model (Snap'Old, U'Old)
                  and (for all W in Tree =>
                         (if W /= T'Old
                             and then W /= U'Old
                             and then Is_Root (Snap'Old, W)
                          then Is_Root (Snap, W)
                               and then Model (Snap, W)
                                         = Model (Snap'Old, W)));
   --  Moves the nodes of U into T one at a time, smallest first: O(m log n)
   --  for m = Size_Of (U), with no node allocated or freed.

private

   type Link is record
      Left   : Extended_Index := 0;
      Right  : Extended_Index := 0;
      Parent : Extended_Index := 0;
      Size   : Extended_Index := 0;
      Height : Extended_Index := 0;
   end record;
   --  For a node on the free chain, Left is the next free node and the rest
   --  is irrelevant.

   type Link_Array is array (Index range <>) of Link;

   type Model_Array is array (Index range <>) of Key_Multisets.Multiset
     with Ghost;
   type Chain_Array is array (Index range <>) of Extended_Index with Ghost;

   type Snapshot is record
      Keys       : Key_Array (1 .. Capacity);
      Links      : Link_Array (1 .. Capacity);
      Free       : Extended_Index := 0;
      Free_Count : Extended_Index := 0;
      Sub        : Model_Array (1 .. Capacity);
      Chain_Pos  : Chain_Array (1 .. Capacity);
      Chain_At   : Chain_Array (1 .. Capacity);
   end record;

   Keys       : Key_Array (1 .. Capacity);
   Links      : Link_Array (1 .. Capacity);
   Free       : Extended_Index := 0;
   Free_Count : Extended_Index := 0;

   Sub : Model_Array (1 .. Capacity) with Ghost;
   Chain_At : Chain_Array (1 .. Capacity) with Ghost;
   Chain_Pos : Chain_Array (1 .. Capacity) with Ghost;

   function Snap return Snapshot is
     ((Keys       => Keys,
       Links      => Links,
       Free       => Free,
       Free_Count => Free_Count,
       Sub        => Sub,
       Chain_Pos  => Chain_Pos,
       Chain_At   => Chain_At));

   function In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Chain_Pos (I) = 0);

   function Sub_Of (S : Snapshot; I : Tree)
     return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else S.Sub (I))
     with Ghost;

   function Size_Of_Node (S : Snapshot; I : Tree) return Extended_Index is
     (if I = 0 then 0 else S.Links (I).Size)
     with Ghost;

   function Height_Of (S : Snapshot; I : Tree) return Extended_Index is
     (if I = 0 then 0 else S.Links (I).Height)
     with Ghost;

   function Size_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Size);

   function Height_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Height);

   function Sub_Now (I : Tree) return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else Sub (I))
     with Ghost;

   function Node_In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Left in 0 .. Capacity
      and then S.Links (I).Right in 0 .. Capacity
      and then S.Links (I).Parent in 0 .. Capacity
      and then (if S.Links (I).Left /= 0 then In_Use (S, S.Links (I).Left))
      and then (if S.Links (I).Right /= 0 then In_Use (S, S.Links (I).Right))
      and then (if S.Links (I).Parent /= 0
                then In_Use (S, S.Links (I).Parent))
      and then S.Links (I).Size
               = 1 + Size_Of_Node (S, S.Links (I).Left)
                   + Size_Of_Node (S, S.Links (I).Right)
      and then S.Links (I).Size <= Capacity
      and then S.Links (I).Height
               = 1 + Extended_Index'Max
                       (Height_Of (S, S.Links (I).Left),
                        Height_Of (S, S.Links (I).Right))
      and then S.Links (I).Height <= S.Links (I).Size
      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum (Sub_Of (S, S.Links (I).Left),
                                       Sub_Of (S, S.Links (I).Right)),
                    S.Keys (I))
      and then (for all E of Sub_Of (S, S.Links (I).Left) =>
                   E <= S.Keys (I))
      and then (for all E of Sub_Of (S, S.Links (I).Right) =>
                   S.Keys (I) <= E)
      and then (if S.Links (I).Left /= 0
                then S.Links (S.Links (I).Left).Parent = I
                     and then S.Links (I).Left /= S.Links (I).Right)
      and then (if S.Links (I).Right /= 0
                then S.Links (S.Links (I).Right).Parent = I)
      and then (if S.Links (I).Parent /= 0
                then S.Links (S.Links (I).Parent).Left = I
                     or else S.Links (S.Links (I).Parent).Right = I))
     with Ghost;
   --  Every clause is about one node and its two children. The height is
   --  exact, which is what bounds it by the size without any balance
   --  clause: balance is what the rotations aim at, and nothing in the proof
   --  depends on it. Search order is stated against the children's cached
   --  models, so it holds for the whole subtree without a walk.

   function Node_Free (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Left in 0 .. Capacity
      and then S.Chain_Pos (I) in 1 .. Capacity
      and then S.Chain_Pos (I) <= S.Free_Count
      and then S.Chain_At (S.Chain_Pos (I)) = I
      and then (if S.Chain_Pos (I) = 1
                then S.Links (I).Left = 0
                else S.Links (I).Left /= 0
                     and then S.Chain_Pos (S.Links (I).Left)
                              = S.Chain_Pos (I) - 1))
     with Ghost;

   function Chain_Sound (S : Snapshot) return Boolean is
     (S.Free in 0 .. Capacity
      and then S.Free_Count <= Capacity
      and then (S.Free = 0) = (S.Free_Count = 0)
      and then (if S.Free /= 0 then S.Chain_Pos (S.Free) = S.Free_Count)
      and then (for all K in 1 .. Capacity =>
                  (if K <= S.Free_Count
                   then S.Chain_At (K) in 1 .. Capacity
                        and then S.Chain_Pos (S.Chain_At (K)) = K)))
     with Ghost;

   function Nodes_Sound (S : Snapshot) return Boolean is
     (for all I in 1 .. Capacity =>
        (if In_Use (S, I) then Node_In_Use (S, I) else Node_Free (S, I)))
     with Ghost;

   function Valid (S : Snapshot) return Boolean is
     (Chain_Sound (S) and then Nodes_Sound (S));

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0 or else (In_Use (S, T) and then S.Links (T).Parent = 0));

   function Model (S : Snapshot; T : Tree)
     return Key_Multisets.Multiset is (Sub_Of (S, T));

   function Size_In (S : Snapshot; T : Tree) return Extended_Index is
     (Size_Of_Node (S, T));

   function Room_In (S : Snapshot) return Extended_Index is
     (S.Free_Count);

   function Room return Extended_Index is (Free_Count);

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type)
     return Boolean is
     (for all E of Sub_Of (S, T) => K <= E);

end Heaps.AVL;
