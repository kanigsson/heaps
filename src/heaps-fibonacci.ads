--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Fibonacci heaps sharing one fixed-capacity node arena.
--
--  A heap is a list of heap-ordered trees whose head is its minimum. Insert
--  and meld concatenate root lists without touching any tree, and extraction
--  pays for them: it moves the children of the minimum onto the root list,
--  links trees of equal rank through a table until no two share a rank, and
--  picks the new minimum while relinking the survivors.
--
--  The collection has no decrease-key, so no node is ever cut from its
--  parent. Every tree is then a binomial tree, and the children of a rank-r
--  node have ranks r - 1 down to 0, exactly as in a binomial heap.
--
--  Only the links, the ranks and the tail of each root list are executable.
--  Parent backlinks, the cached sizes and models, and the list membership
--  that lets a concatenation be described without walking the list are
--  ghost, so the executable concatenation stays constant time.

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

with Heaps.Key_Multisets;
with SPARK.Big_Integers;

generic
   Capacity : Index;

package Heaps.Fibonacci with SPARK_Mode, Always_Terminates is

   use type Key_Multisets.Multiset;
   use type SPARK.Big_Integers.Big_Integer;

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
   --  Walks the root list, so it costs one step per root

   function Is_Empty (T : Tree) return Boolean is (T = 0);

   procedure Clear
     with Post => Valid and Room = Capacity;

   function Peek_Min (T : Tree) return Key_Type
     with Pre => Valid and then Is_Root (T) and then T /= 0,
          Post => Is_Minimum (Snap, T, Peek_Min'Result)
                  and then Key_Multisets.Contains (Model (T), Peek_Min'Result);

   function Min_Of (T : Tree) return Key_Type
     with Pre  => Valid and then Is_Root (T) and then T /= 0,
          Post => Is_Minimum (Snap, T, Min_Of'Result);

   procedure Insert (T : in out Tree; K : Key_Type)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Room >= 1,
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
                  and then T /= 0,
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
   --  No bound on Room is needed: a nonempty heap holds a node, so the
   --  arena's accounting already puts one slot outside the free list.

   procedure Meld (T : in out Tree; U : in out Tree)
     with Pre  => Valid
                  and then Is_Root (T)
                  and then Is_Root (U)
                  and then (if T /= 0 and then U /= 0 then T /= U),
          Post => Valid
                  and Is_Root (T)
                  and U = 0
                  and Room = Room'Old
                  and Size_In (Snap, T)
                      = Size_In (Snap'Old, T'Old) + Size_In (Snap'Old, U'Old)
                  and Model (Snap, T)
                      = Model (Snap'Old, T'Old)
                        + Model (Snap'Old, U'Old)
                  and (for all W in Tree =>
                         (if W /= T'Old
                             and then W /= U'Old
                             and then Is_Root (Snap'Old, W)
                          then Is_Root (Snap, W)
                               and then Model (Snap, W)
                                         = Model (Snap'Old, W)));

private

   Max_Rank : constant := 24;
   --  A rank-r tree holds 2**r nodes; Max_Capacity is 2**24.
   subtype Rank_Type is Natural range 0 .. Max_Rank;

   type Link is record
      Child   : Extended_Index := 0;
      Sibling : Extended_Index := 0;
      Last    : Extended_Index := 0;
      Rank    : Rank_Type := 0;
   end record;
   --  Last is the tail of the root list, and means something only at the
   --  head of one.

   type Link_Array is array (Index range <>) of Link;

   type Meta_Data is record
      Parent : Extended_Index := 0;
      Size   : Extended_Index := 0;
      Owner  : Extended_Index := 0;
      Pos    : SPARK.Big_Integers.Big_Natural := 0;
   end record
     with Ghost;
   --  Parent is the node whose child or sibling link points here. Size
   --  counts the node, its descendants and its sibling suffix. Owner is the
   --  head of the root list the node is on, or 0 in a child list. Pos is
   --  the 1-based position on a root list. It is unbounded because nothing
   --  bounds it cheaply: a list can hold as many trees as nodes, and the
   --  flat invariant has no way to count them.

   type Meta_Array is array (Index range <>) of Meta_Data with Ghost;
   type Model_Array is array (Index range <>) of Key_Multisets.Multiset
     with Ghost;
   type Chain_Array is array (Index range <>) of Extended_Index with Ghost;

   type Snapshot is record
      Keys       : Key_Array (1 .. Capacity);
      Links      : Link_Array (1 .. Capacity);
      Free       : Extended_Index := 0;
      Free_Count : Extended_Index := 0;
      Meta       : Meta_Array (1 .. Capacity);
      Sub        : Model_Array (1 .. Capacity);
      Chain_Pos  : Chain_Array (1 .. Capacity);
      Chain_At   : Chain_Array (1 .. Capacity);
   end record;

   Keys       : Key_Array (1 .. Capacity);
   Links      : Link_Array (1 .. Capacity);
   Free       : Extended_Index := 0;
   Free_Count : Extended_Index := 0;

   Meta : Meta_Array (1 .. Capacity) with Ghost;
   Sub : Model_Array (1 .. Capacity) with Ghost;
   Chain_At : Chain_Array (1 .. Capacity) with Ghost;
   Chain_Pos : Chain_Array (1 .. Capacity) with Ghost;

   function Snap return Snapshot is
     ((Keys       => Keys,
       Links      => Links,
       Free       => Free,
       Free_Count => Free_Count,
       Meta       => Meta,
       Sub        => Sub,
       Chain_Pos  => Chain_Pos,
       Chain_At   => Chain_At));

   function In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Chain_Pos (I) = 0);

   function Sub_Of (S : Snapshot; I : Tree)
     return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else S.Sub (I))
     with Ghost;

   function Size_Of_Node (S : Snapshot; I : Tree)
     return Extended_Index is
     (if I = 0 then 0 else S.Meta (I).Size)
     with Ghost;

   function Size_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Meta (I).Size)
     with Ghost;

   function Sub_Now (I : Tree) return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else Sub (I))
     with Ghost;

   function Weight (R : Rank_Type) return Index is (2 ** R)
     with Ghost,
          Post => (if R = 0 then Weight'Result = 1)
                  and then (if R = Max_Rank
                            then Weight'Result = Max_Capacity),
          Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");
   --  Keep exponentiation out of structural VCs. A lemma in the body exposes
   --  and proves the doubling and ordering laws where they are needed.

   --  The links of a node, whichever list it is on

   function Links_Sound (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Child in 0 .. Capacity
      and then S.Links (I).Sibling in 0 .. Capacity
      and then S.Meta (I).Parent in 0 .. Capacity
      and then S.Meta (I).Owner in 0 .. Capacity
      and then (if S.Links (I).Child /= 0
                then In_Use (S, S.Links (I).Child))
      and then (if S.Links (I).Sibling /= 0
                then In_Use (S, S.Links (I).Sibling))
      and then (if S.Meta (I).Parent /= 0
                then In_Use (S, S.Meta (I).Parent))
      and then S.Meta (I).Size
               = 1 + Size_Of_Node (S, S.Links (I).Child)
                   + Size_Of_Node (S, S.Links (I).Sibling)
      and then S.Meta (I).Size <= Capacity
      and then Size_Of_Node (S, S.Links (I).Child)
                 = Weight (S.Links (I).Rank) - 1
      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum
                      (Sub_Of (S, S.Links (I).Child),
                       Sub_Of (S, S.Links (I).Sibling)),
                    S.Keys (I))
      and then (for all E of Sub_Of (S, S.Links (I).Child) =>
                   S.Keys (I) <= E)
      and then (if S.Links (I).Child /= 0
                then S.Meta (S.Links (I).Child).Parent = I
                     and then S.Meta (S.Links (I).Child).Owner = 0
                     and then S.Links (I).Child /= S.Links (I).Sibling
                     and then S.Links (S.Links (I).Child).Rank + 1
                                = S.Links (I).Rank)
      and then (if S.Links (I).Sibling /= 0
                then S.Meta (S.Links (I).Sibling).Parent = I
                     and then S.Meta (S.Links (I).Sibling).Owner
                                = S.Meta (I).Owner)
      and then (if S.Meta (I).Parent /= 0
                then S.Links (S.Meta (I).Parent).Child = I
                     or else S.Links (S.Meta (I).Parent).Sibling = I))
     with Ghost;
   --  The child forest of a rank-r node has exactly 2**r - 1 nodes and
   --  starts at rank r - 1. Parent backlinks give unique incoming links;
   --  decreasing sizes exclude cycles. Sub mirrors the links and enforces
   --  heap order below I. A sibling is on the same list as the node.

   --  A node of a child list: its siblings have decreasing ranks, so the
   --  list has fewer than 2**(r + 1) nodes from a rank-r node on.

   function Child_Sound (S : Snapshot; I : Slot) return Boolean is
     (S.Meta (I).Parent /= 0
      and then S.Meta (I).Size < 2 * Weight (S.Links (I).Rank)
      and then (if S.Links (I).Sibling in 1 .. Capacity
                then S.Links (S.Links (I).Sibling).Rank < S.Links (I).Rank))
     with Ghost;

   --  A node of a root list, whose head is its owner. Owner and Pos place
   --  the node on the list without a reachability argument: they are what
   --  lets a concatenation update the whole list at once, and what shows
   --  that a list of one node owns no other node.

   function Top_Sound (S : Snapshot; I : Slot) return Boolean is
     (S.Meta (I).Owner in 1 .. Capacity
      and then In_Use (S, S.Meta (I).Owner)
      and then S.Meta (S.Meta (I).Owner).Owner = S.Meta (I).Owner
      and then (S.Meta (I).Parent = 0) = (S.Meta (I).Owner = I)
      and then (S.Meta (I).Pos = 1) = (S.Meta (I).Owner = I)
      and then S.Meta (I).Pos >= 1
      and then S.Links (S.Meta (I).Owner).Last in 1 .. Capacity
      and then S.Meta (I).Pos
                 <= S.Meta (S.Links (S.Meta (I).Owner).Last).Pos
      and then (if S.Links (I).Sibling in 1 .. Capacity
                then S.Meta (S.Links (I).Sibling).Pos = S.Meta (I).Pos + 1
                else S.Links (S.Meta (I).Owner).Last = I)
      and then (if S.Meta (I).Owner = I
                then S.Links (I).Last in 1 .. Capacity
                     and then In_Use (S, S.Links (I).Last)
                     and then S.Meta (S.Links (I).Last).Owner = I
                     and then S.Links (S.Links (I).Last).Sibling = 0))
     with Ghost;

   function Node_In_Use (S : Snapshot; I : Slot) return Boolean is
     (Links_Sound (S, I)
      and then (if S.Meta (I).Owner = 0
                then Child_Sound (S, I)
                else Top_Sound (S, I)))
     with Ghost;

   function Node_Free (S : Snapshot; I : Slot) return Boolean is
     (S.Chain_Pos (I) in 1 .. Capacity
      and then S.Chain_Pos (I) <= S.Free_Count
      and then S.Chain_At (S.Chain_Pos (I)) = I
      and then (if S.Chain_Pos (I) = 1
                then S.Links (I).Child = 0
                else S.Links (I).Child in 1 .. Capacity
                     and then S.Chain_Pos (S.Links (I).Child)
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

   --  Accounting for all list heads makes the capacity bound follow from
   --  Room, without a size precondition on Insert or Meld. The sum is ghost.
   function Root_Size (S : Snapshot; I : Tree) return Long_Long_Integer is
     (if I /= 0 and then In_Use (S, I) and then S.Meta (I).Parent = 0
      then Long_Long_Integer (S.Meta (I).Size) else 0)
     with Ghost;

   function Total (S : Snapshot; N : Tree) return Long_Long_Integer is
     (if N = 0 then 0 else Total (S, N - 1) + Root_Size (S, N))
     with Ghost,
          Subprogram_Variant => (Decreases => N),
          Post => Total'Result in 0 .. Long_Long_Integer (N) * Max_Capacity;

   function Valid (S : Snapshot) return Boolean is
     (Chain_Sound (S) and then Nodes_Sound (S)
      and then Total (S, Capacity) + Long_Long_Integer (S.Free_Count)
                 = Long_Long_Integer (Capacity));

   function Is_Head (S : Snapshot; T : Tree) return Boolean is
     (T /= 0 and then In_Use (S, T) and then S.Meta (T).Parent = 0)
     with Ghost;
   --  The head of a root list, not necessarily its minimum

   function Is_Minimum (S : Snapshot; T : Tree; K : Key_Type)
     return Boolean is
     (for all E of Sub_Of (S, T) => K <= E);

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0
      or else (Is_Head (S, T) and then Is_Minimum (S, T, S.Keys (T))));

   function Model (S : Snapshot; T : Tree)
     return Key_Multisets.Multiset is (Sub_Of (S, T));

   function Size_In (S : Snapshot; T : Tree) return Extended_Index is
     (Size_Of_Node (S, T));

   function Room_In (S : Snapshot) return Extended_Index is
     (S.Free_Count);

   function Room return Extended_Index is (Free_Count);

end Heaps.Fibonacci;
