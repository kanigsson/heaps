--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Skew binomial heaps sharing one fixed-capacity node arena.
--
--  A heap is a list of heap-ordered trees in increasing rank order, of which
--  only the first two may share a rank. Insertion looks at those two alone:
--  if their ranks are equal, a skew link makes them and the new node one
--  tree of the next rank, and otherwise the new node goes in front as a tree
--  of rank 0. Either way it touches at most three nodes, so insertion is
--  constant time in the worst case rather than amortized.
--
--  A skew link either puts the new node above both trees, or links the two
--  trees and hangs the new node under the winner as a child of rank 0.
--  Meld first links the two front trees of each list if their ranks are
--  equal and then merges the lists as a binomial heap does, carrying from
--  the smallest rank upwards. Extraction removes the tree whose root is the
--  minimum, melds its children of positive rank, in reverse, back into the
--  heap, and inserts its rank-0 children one at a time.
--
--  Parent names the incoming binary link: either the preceding sibling or
--  the node whose first child this is. The cached ghost model includes a
--  node's descendants and the suffix of its list, so the head of a root list
--  is the model of the complete heap.

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Key_Multisets;

generic
   Capacity : Index;

package Heaps.Skew_Binomial with SPARK_Mode, Always_Terminates is

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
   --  Nor is a bound on the two sizes: two distinct heaps share one arena,
   --  so between them they hold no more nodes than it has.

private

   subtype Rank_Type is Extended_Index;
   --  The invariant bounds a rank by the size of the tree below it, which
   --  is linear where the tight bound is logarithmic. Nothing in a contract
   --  depends on the tight one, and the linear one needs no exponentiation.

   type Link is record
      Child   : Extended_Index := 0;
      Sibling : Extended_Index := 0;
      Parent  : Extended_Index := 0;
      Size    : Extended_Index := 0;
      Rank    : Rank_Type := 0;
   end record;

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

   function Size_Of_Node (S : Snapshot; I : Tree)
     return Extended_Index is
     (if I = 0 then 0 else S.Links (I).Size)
     with Ghost;

   function Size_Now (I : Tree) return Extended_Index is
     (if I = 0 then 0 else Links (I).Size);

   function Sub_Now (I : Tree) return Key_Multisets.Multiset is
     (if I = 0 then Key_Multisets.Empty_Multiset else Sub (I))
     with Ghost;

   function Rank_Now (I : Tree) return Integer is
     (if I = 0 then -1 else Links (I).Rank);

   function Node_In_Use (S : Snapshot; I : Slot) return Boolean is
     (S.Links (I).Child in 0 .. Capacity
      and then S.Links (I).Sibling in 0 .. Capacity
      and then S.Links (I).Parent in 0 .. Capacity
      and then (if S.Links (I).Child /= 0
                then In_Use (S, S.Links (I).Child))
      and then (if S.Links (I).Sibling /= 0
                then In_Use (S, S.Links (I).Sibling))
      and then (if S.Links (I).Parent /= 0
                then In_Use (S, S.Links (I).Parent))
      and then S.Links (I).Size
               = 1 + Size_Of_Node (S, S.Links (I).Child)
                   + Size_Of_Node (S, S.Links (I).Sibling)
      and then S.Links (I).Size <= Capacity
      and then S.Links (I).Rank <= Size_Of_Node (S, S.Links (I).Child)
      and then S.Sub (I)
               = Key_Multisets.Add
                   (Key_Multisets.Sum
                      (Sub_Of (S, S.Links (I).Child),
                       Sub_Of (S, S.Links (I).Sibling)),
                    S.Keys (I))
      and then (for all E of Sub_Of (S, S.Links (I).Child) =>
                   S.Keys (I) <= E)
      and then (if S.Links (I).Child /= 0
                then S.Links (S.Links (I).Child).Parent = I
                     and then S.Links (I).Child /= S.Links (I).Sibling)
      and then (if S.Links (I).Sibling /= 0
                then S.Links (S.Links (I).Sibling).Parent = I)
      and then (if S.Links (I).Parent /= 0
                then S.Links (S.Links (I).Parent).Child = I
                     or else S.Links (S.Links (I).Parent).Sibling = I)
      )
     with Ghost;
   --  Size includes the sibling suffix. A tree of rank r holds at least
   --  r + 1 nodes, which is all that keeps a rank in range; the order of the
   --  ranks along a list is the algorithm's business, not the invariant's.
   --  Parent backlinks give unique incoming links; decreasing sizes exclude
   --  cycles. Sub mirrors these same links and enforces heap order below I.

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

   --  Accounting for all forest roots makes the capacity bounds follow from
   --  Room and from the distinctness of two roots, without a size
   --  precondition anywhere. The sum is ghost.
   function Root_Size (S : Snapshot; I : Tree) return Long_Long_Integer is
     (if I /= 0 and then In_Use (S, I) and then S.Links (I).Parent = 0
      then Long_Long_Integer (S.Links (I).Size) else 0)
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

   function Is_Root (S : Snapshot; T : Tree) return Boolean is
     (T = 0
      or else (In_Use (S, T)
               and then S.Links (T).Parent = 0));

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

end Heaps.Skew_Binomial;
