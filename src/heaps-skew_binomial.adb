--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Models;

package body Heaps.Skew_Binomial with SPARK_Mode is

   package KM renames Key_Multisets;

   --  Multiset equality is extensional. These proved algebraic lemmas
   --  compose helper results without unfolding the whole arena again.

   procedure Link_Model (C, D : KM.Multiset; K, L : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Add (KM.Sum (D, C), L), K)
                    = KM.Sum (KM.Add (C, K), KM.Add (D, L));
   procedure Link_Model (C, D : KM.Multiset; K, L : Key_Type) is null;

   procedure Join_Model (Child, Tail, Head, Whole : KM.Multiset; K : Key_Type)
     with Ghost,
          Pre => Head = KM.Add (KM.Sum (Child, KM.Empty_Multiset), K)
                 and then Whole = KM.Add (KM.Sum (Child, Tail), K),
          Post => Whole = KM.Sum (Head, Tail);
   procedure Join_Model (Child, Tail, Head, Whole : KM.Multiset; K : Key_Type)
     is null;

   procedure Sum_Pairs (A, B, C, D, Left, Right, First, Second : KM.Multiset)
     with Ghost,
          Pre => Left = KM.Sum (A, B) and then Right = KM.Sum (C, D)
                 and then First = KM.Sum (A, C)
                 and then Second = KM.Sum (B, D),
          Post => KM.Sum (Left, Right) = KM.Sum (First, Second);
   procedure Sum_Pairs
     (A, B, C, D, Left, Right, First, Second : KM.Multiset) is null;

   procedure Sum_Regroup (A, B, C, Left, Right : KM.Multiset)
     with Ghost,
          Pre => Left = KM.Sum (A, B) and then Right = KM.Sum (B, C),
          Post => KM.Sum (Left, C) = KM.Sum (A, Right);
   procedure Sum_Regroup (A, B, C, Left, Right : KM.Multiset) is null;

   procedure Sum_Middle (A, B, C, Inner_Left, Inner_Right : KM.Multiset)
     with Ghost,
          Pre => Inner_Left = KM.Sum (B, C)
                 and then Inner_Right = KM.Sum (A, C),
          Post => KM.Sum (A, Inner_Left) = KM.Sum (B, Inner_Right);
   procedure Sum_Middle (A, B, C, Inner_Left, Inner_Right : KM.Multiset)
     is null;

   procedure Skew_Model (N, A, B, Inner, Result : KM.Multiset)
     with Ghost,
          Pre => Inner = KM.Sum (N, B) and then Result = KM.Sum (Inner, A),
          Post => Result = KM.Sum (KM.Sum (A, B), N);
   procedure Skew_Model (N, A, B, Inner, Result : KM.Multiset) is null;

   procedure Insert_Model
     (Old_T, A, B, Old_Rest, Rest, N, Linked, Result : KM.Multiset)
     with Ghost,
          Pre => Old_T = KM.Sum (A, Old_Rest)
                 and then Old_Rest = KM.Sum (B, Rest)
                 and then Linked = KM.Sum (KM.Sum (A, B), N)
                 and then Result = KM.Sum (Linked, Rest),
          Post => Result = KM.Sum (Old_T, N);
   procedure Insert_Model
     (Old_T, A, B, Old_Rest, Rest, N, Linked, Result : KM.Multiset) is null;

   procedure Walk_Insert_Model
     (T, A, H, Rest, C, New_T, Final : KM.Multiset)
     with Ghost,
          Pre => C = KM.Sum (H, Rest)
                 and then New_T = KM.Sum (T, H)
                 and then Final = KM.Sum (KM.Sum (New_T, A), Rest),
          Post => Final = KM.Sum (KM.Sum (T, A), C);
   procedure Walk_Insert_Model
     (T, A, H, Rest, C, New_T, Final : KM.Multiset) is null;

   procedure Walk_Keep_Model
     (T, A, H, Rest, C, New_A, Final : KM.Multiset)
     with Ghost,
          Pre => C = KM.Sum (H, Rest)
                 and then New_A = KM.Sum (H, A)
                 and then Final = KM.Sum (KM.Sum (T, New_A), Rest),
          Post => Final = KM.Sum (KM.Sum (T, A), C);
   procedure Walk_Keep_Model
     (T, A, H, Rest, C, New_A, Final : KM.Multiset) is null;

   procedure Extract_Model
     (Whole, Rest, Below, Walked, Result : KM.Multiset; K : Key_Type)
     with Ghost,
          Pre => Whole = KM.Sum (KM.Add (Below, K), Rest)
                 and then Walked
                          = KM.Sum (KM.Sum (Rest, KM.Empty_Multiset), Below)
                 and then Result = Walked,
          Post => Whole = KM.Add (Result, K);
   procedure Extract_Model
     (Whole, Rest, Below, Walked, Result : KM.Multiset; K : Key_Type)
   is null;

   function Part (S : Snapshot; I, N : Tree) return Long_Long_Integer is
     (if I <= N then Root_Size (S, I) else 0) with Ghost;

   --  A local operation changes the contribution of at most two roots.
   --  This induction carries their difference through the global sum.
   procedure Total_Change
     (Before, After : Snapshot; A, B, N : Tree)
     with Ghost,
          Pre => (A /= B or else A = 0)
                 and then (for all X in 1 .. Capacity =>
                    (if X /= A and then X /= B
                     then Root_Size (Before, X) = Root_Size (After, X))),
          Post => Total (After, N) - Total (Before, N)
                    = Part (After, A, N) - Part (Before, A, N)
                      + Part (After, B, N) - Part (Before, B, N),
          Subprogram_Variant => (Decreases => N);

   procedure Total_Change
     (Before, After : Snapshot; A, B, N : Tree) is
   begin
      if N /= 0 then
         Total_Change (Before, After, A, B, N - 1);
      end if;
   end Total_Change;

   procedure Total_Zero (S : Snapshot; N : Tree)
     with Ghost,
          Pre => (for all X in 1 .. Capacity => Root_Size (S, X) = 0),
          Post => Total (S, N) = 0,
          Subprogram_Variant => (Decreases => N);

   procedure Total_Zero (S : Snapshot; N : Tree) is
   begin
      if N /= 0 then
         Total_Zero (S, N - 1);
      end if;
   end Total_Zero;

   procedure Total_Bound_One (S : Snapshot; I : Slot; N : Tree)
     with Ghost, Pre => I <= N,
          Post => Root_Size (S, I) <= Total (S, N),
          Subprogram_Variant => (Decreases => N);

   procedure Total_Bound_One (S : Snapshot; I : Slot; N : Tree) is
   begin
      if I < N then
         Total_Bound_One (S, I, N - 1);
      end if;
   end Total_Bound_One;

   procedure Total_Bound (S : Snapshot; I, J : Slot; N : Tree)
     with Ghost, Pre => I <= N and then J <= N and then I /= J,
          Post => Root_Size (S, I) + Root_Size (S, J) <= Total (S, N),
          Subprogram_Variant => (Decreases => N);
   --  Two distinct roots hold no more nodes between them than the arena

   procedure Total_Bound (S : Snapshot; I, J : Slot; N : Tree) is
   begin
      if I = N then
         Total_Bound_One (S, J, N - 1);
      elsif J = N then
         Total_Bound_One (S, I, N - 1);
      else
         Total_Bound (S, I, J, N - 1);
      end if;
   end Total_Bound;

   procedure Allocate (I : out Slot; K : Key_Type)
     with Pre  => Valid and then Room >= 1,
          Post => Valid
                  and then In_Use (Snap, I)
                  and then Room = Room'Old - 1
                  and then Keys (I) = K
                  and then Sub (I) = KM.Add (KM.Empty_Multiset, K)
                  and then Links (I).Child = 0
                  and then Links (I).Sibling = 0
                  and then Links (I).Parent = 0
                  and then Links (I).Size = 1
                  and then Links (I).Rank = 0
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                               then X /= I
                                    and then In_Use (Snap, X)
                                    and then Keys (X) = Snap'Old.Keys (X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then KM.Multiset_Logic_Equal (Sub (X), Snap'Old.Sub (X))));
   procedure Deallocate (I : Slot)
     with Pre  => Valid
                  and then Room < Capacity
                  and then In_Use (Snap, I)
                  and then Links (I).Child = 0
                  and then Links (I).Sibling = 0
                  and then Links (I).Parent = 0
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap, X) and then X /= I
                               then Links (X).Child /= I
                                    and then Links (X).Sibling /= I
                                    and then Links (X).Parent /= I)),
          Post => Valid
                  and then not In_Use (Snap, I)
                  and then Room = Room'Old + 1
                  and then Keys = Snap'Old.Keys
                  and then (for all X in 1 .. Capacity =>
                              (if Is_Root (Snap, X)
                               then Is_Root (Snap'Old, X) and then X /= I))
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X) and then X /= I
                               then In_Use (Snap, X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then KM.Multiset_Logic_Equal (Sub (X), Snap'Old.Sub (X))));

   function Stable (S : Snapshot) return Boolean is
     (Keys = S.Keys and then Chain_Pos = S.Chain_Pos
      and then Chain_At = S.Chain_At
      and then Free = S.Free and then Free_Count = S.Free_Count) with Ghost;

   --  The roots of S other than the named ones are untouched
   function Frame (S : Snapshot; A, B : Tree; C : Tree := 0) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Is_Root (S, X) and then X /= A and then X /= B and then X /= C
         then Links (X) = S.Links (X)
              and then KM.Multiset_Logic_Equal (Sub (X), S.Sub (X))))
     with Ghost;

   --  Every root but the results R and R2 was a root of S, and none of the
   --  consumed lists A, B and C
   function Origins
     (S : Snapshot; A, B, R : Tree; C, R2 : Tree := 0) return Boolean
   is
     (for all X in 1 .. Capacity =>
        (if Is_Root (Snap, X) and then X /= R and then X /= R2
         then Is_Root (S, X)
              and then X /= A and then X /= B and then X /= C))
     with Ghost;

   --  A result that was already a root of S is one of the lists consumed
   function From (S : Snapshot; R, A, B : Tree; C : Tree := 0) return Boolean
   is
     (if R /= 0 and then Is_Root (S, R) then R = A or else R = B or else R = C)
     with Ghost;

   --  Split, Prepend and Adopt each change one or two roots. All three
   --  preserve Valid, so recursive callers never inherit a broken forest.

   procedure Split (A : Slot; Rest : out Tree)
     with Pre => Valid and then Is_Root (A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (A) and then Is_Root (Rest)
                  and then A /= Rest
                  and then (if Rest /= 0 then not Is_Root (Snap'Old, Rest))
                  and then (for all X in 1 .. Capacity =>
                     (if Is_Root (Snap, X) and then X /= A and then X /= Rest
                      then Is_Root (Snap'Old, X)))
                  and then Rest = Snap'Old.Links (A).Sibling
                  and then Links (A).Sibling = 0
                  and then Links (A).Rank = Snap'Old.Links (A).Rank
                  and then Links (A).Child = Snap'Old.Links (A).Child
                  and then Size_Now (A) + Size_Now (Rest)
                             = Snap'Old.Links (A).Size
                  and then KM.Sum (Sub_Now (A), Sub_Now (Rest))
                             = Snap'Old.Sub (A)
                  and then (for all X in 1 .. Capacity =>
                     (if X /= A and then X /= Rest
                      then Links (X) = Snap'Old.Links (X)
                           and then KM.Multiset_Logic_Equal (Sub (X), Snap'Old.Sub (X))))
                  and then (if Rest /= 0
                            then Links (Rest).Size = Snap'Old.Links (Rest).Size
                                 and then Links (Rest).Rank
                                            = Snap'Old.Links (Rest).Rank
                                 and then Links (Rest).Sibling
                                            = Snap'Old.Links (Rest).Sibling
                                 and then KM.Multiset_Logic_Equal
                                            (Sub (Rest), Snap'Old.Sub (Rest)))
                  and then Frame (Snap'Old, A, 0);

   procedure Prepend (A : Slot; B : Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then A /= B and then Links (A).Sibling = 0,
          Post => Valid and then Stable (Snap'Old) and then Is_Root (A)
                  and then Links (A).Rank = Snap'Old.Links (A).Rank
                  and then Links (A).Size
                             = Snap'Old.Links (A).Size
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub (A)
                             = KM.Sum (Snap'Old.Sub (A), Sub_Of (Snap'Old, B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, A);

   --  C becomes the first child of P, and P takes the rank given. A rank
   --  is bounded by the size of the child forest, so that is the bound on
   --  the new one; the keys need only be in order at the two roots.
   procedure Adopt (P, C : Slot; New_Rank : Rank_Type)
     with Pre => Valid and then Is_Root (P) and then Is_Root (C)
                 and then P /= C
                 and then Links (P).Sibling = 0
                 and then Links (C).Sibling = 0
                 and then Keys (P) <= Keys (C)
                 and then New_Rank
                            <= Size_Now (Links (P).Child) + Links (C).Size,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (P) and then Links (P).Sibling = 0
                  and then Links (P).Rank = New_Rank
                  and then Links (P).Size
                             = Snap'Old.Links (P).Size
                               + Snap'Old.Links (C).Size
                  and then Size_Now (Links (P).Child)
                             = Snap'Old.Links (P).Size
                               + Snap'Old.Links (C).Size - 1
                  and then Sub (P)
                             = KM.Sum (Snap'Old.Sub (P), Snap'Old.Sub (C))
                  and then Frame (Snap'Old, P, C)
                  and then Origins (Snap'Old, P, C, P);

   procedure Link_Equal (A, B : Slot; R : out Slot)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then A /= B
                 and then Links (A).Sibling = 0
                 and then Links (B).Sibling = 0
                 and then Links (A).Rank = Links (B).Rank,
          Post => Valid and then Stable (Snap'Old)
                  and then (R = A or else R = B)
                  and then Keys (R) <= Keys (A) and then Keys (R) <= Keys (B)
                  and then Is_Root (R) and then Links (R).Sibling = 0
                  and then Links (R).Rank = Snap'Old.Links (A).Rank + 1
                  and then Links (R).Size
                             = Snap'Old.Links (A).Size
                               + Snap'Old.Links (B).Size
                  and then Sub (R)
                             = KM.Sum (Snap'Old.Sub (A), Snap'Old.Sub (B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R);

   --  Two trees of one rank and a third tree, normally a single node, make
   --  one tree of the next rank.
   procedure Skew_Link (N, A, B : Slot; R : out Slot)
     with Pre => Valid and then Is_Root (N) and then Is_Root (A)
                 and then Is_Root (B)
                 and then N /= A and then N /= B and then A /= B
                 and then Links (N).Sibling = 0
                 and then Links (A).Sibling = 0
                 and then Links (B).Sibling = 0
                 and then Links (A).Rank = Links (B).Rank,
          Post => Valid and then Stable (Snap'Old)
                  and then (R = N or else R = A or else R = B)
                  and then Is_Root (R) and then Links (R).Sibling = 0
                  and then Links (R).Size
                             = Snap'Old.Links (N).Size
                               + Snap'Old.Links (A).Size
                               + Snap'Old.Links (B).Size
                  and then Sub (R)
                             = KM.Sum (KM.Sum (Snap'Old.Sub (A),
                                               Snap'Old.Sub (B)),
                                       Snap'Old.Sub (N))
                  and then Frame (Snap'Old, N, A, B)
                  and then Origins (Snap'Old, N, A, R, B);

   --  Insert the tree A into the list L, linking as long as the front of
   --  L has A's rank
   procedure Ins_Tree (A : Slot; L : Tree; R : out Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (L)
                 and then A /= L and then Links (A).Sibling = 0,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (R) and then R /= 0
                  and then Size_Now (R)
                             = Snap'Old.Links (A).Size
                               + Size_Of_Node (Snap'Old, L)
                  and then Sub_Now (R)
                             = KM.Sum (Snap'Old.Sub (A), Sub_Of (Snap'Old, L))
                  and then From (Snap'Old, R, A, L)
                  and then Frame (Snap'Old, A, L)
                  and then Origins (Snap'Old, A, L, R),
          Subprogram_Variant => (Decreases => Size_Now (L));

   procedure Merge_Trees (A, B : Tree; R : out Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then (if A /= 0 then A /= B),
          Post => Valid and then Stable (Snap'Old) and then Is_Root (R)
                  and then Size_Now (R)
                             = Size_Of_Node (Snap'Old, A)
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub_Now (R)
                             = KM.Sum (Sub_Of (Snap'Old, A),
                                       Sub_Of (Snap'Old, B))
                  and then From (Snap'Old, R, A, B)
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R),
          Subprogram_Variant => (Decreases => Size_Now (A) + Size_Now (B));

   --  Link the two front trees of a list if they share a rank, so that
   --  every rank along it is distinct
   procedure Normalize (A : Tree; R : out Tree)
     with Pre => Valid and then Is_Root (A),
          Post => Valid and then Stable (Snap'Old) and then Is_Root (R)
                  and then Size_Now (R) = Size_Of_Node (Snap'Old, A)
                  and then Sub_Now (R) = Sub_Of (Snap'Old, A)
                  and then From (Snap'Old, R, A, 0)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, A, 0, R);

   procedure Meld_Lists (A, B : Tree; R : out Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then (if A /= 0 then A /= B),
          Post => Valid and then Stable (Snap'Old) and then Is_Root (R)
                  and then Size_Now (R)
                             = Size_Of_Node (Snap'Old, A)
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub_Now (R)
                             = KM.Sum (Sub_Of (Snap'Old, A),
                                       Sub_Of (Snap'Old, B))
                  and then From (Snap'Old, R, A, B)
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R);

   --  Put the tree N in front of T, or skew-link it with T's two front
   --  trees if they share a rank. Constant time either way.
   procedure Skew_Insert (T : in out Tree; N : Slot)
     with Pre => Valid and then Is_Root (T) and then Is_Root (N)
                 and then N /= T and then Links (N).Sibling = 0,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (T) and then T /= 0
                  and then Size_Now (T)
                             = Size_Of_Node (Snap'Old, T'Old)
                               + Snap'Old.Links (N).Size
                  and then Sub_Now (T)
                             = KM.Sum (Sub_Of (Snap'Old, T'Old),
                                       Snap'Old.Sub (N))
                  and then From (Snap'Old, T, T'Old, N)
                  and then Frame (Snap'Old, T'Old, N)
                  and then Origins (Snap'Old, T'Old, N, T);

   function Minimum (T : Slot) return Slot
     with Pre => Valid and then In_Use (Snap, T),
          Post => In_Use (Snap, Minimum'Result)
                  and then Is_Minimum (Snap, T, Keys (Minimum'Result))
                  and then KM.Contains (Sub_Now (T), Keys (Minimum'Result)),
          Subprogram_Variant => (Decreases => Size_Now (T));

   --  Take the first root holding K off the list T, as a tree of its own
   procedure Detach (T : in out Tree; K : Key_Type; M : out Slot)
     with Pre => Valid and then Is_Root (T) and then T /= 0
                 and then Is_Minimum (Snap, T, K)
                 and then KM.Contains (Sub_Now (T), K),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (T) and then Is_Root (M) and then M /= T
                  and then Links (M).Sibling = 0 and then Keys (M) = K
                  and then Size_Now (M) + Size_Now (T)
                             = Snap'Old.Links (T'Old).Size
                  and then KM.Sum (Sub_Now (M), Sub_Now (T))
                             = Snap'Old.Sub (T'Old)
                  and then From (Snap'Old, T, T'Old, 0)
                  and then From (Snap'Old, M, T'Old, 0)
                  and then Frame (Snap'Old, T'Old, 0)
                  and then Origins (Snap'Old, T'Old, 0, T, 0, M),
          Subprogram_Variant => (Decreases => Size_Now (T));

   --  Put the children of an extracted root back: rank-0 children into T
   --  one at a time, and the others onto Acc, which reverses their order
   procedure Walk (C : Tree; T, Acc : in out Tree)
     with Pre => Valid and then Is_Root (C) and then Is_Root (T)
                 and then Is_Root (Acc)
                 and then (if C /= 0 then C /= T and then C /= Acc)
                 and then (if T /= 0 then T /= Acc),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (T) and then Is_Root (Acc)
                  and then (if T /= 0 then T /= Acc)
                  and then Size_Now (T) + Size_Now (Acc)
                             = Size_Of_Node (Snap'Old, T'Old)
                               + Size_Of_Node (Snap'Old, Acc'Old)
                               + Size_Of_Node (Snap'Old, C)
                  and then KM.Sum (Sub_Now (T), Sub_Now (Acc))
                             = KM.Sum (KM.Sum (Sub_Of (Snap'Old, T'Old),
                                               Sub_Of (Snap'Old, Acc'Old)),
                                       Sub_Of (Snap'Old, C))
                  and then From (Snap'Old, T, C, T'Old, Acc'Old)
                  and then From (Snap'Old, Acc, C, T'Old, Acc'Old)
                  and then Frame (Snap'Old, C, T'Old, Acc'Old)
                  and then Origins (Snap'Old, C, T'Old, T, Acc'Old, Acc),
          Subprogram_Variant => (Decreases => Size_Now (C));

   -----------
   -- Split --
   -----------

   procedure Split (A : Slot; Rest : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      Rest := Links (A).Sibling;
      if Rest /= 0 then
         Links (Rest).Parent := 0;
      end if;
      Links (A).Sibling := 0;
      Links (A).Size := 1 + Size_Now (Links (A).Child);
      Sub (A) := KM.Add (KM.Sum (Sub_Now (Links (A).Child),
                                 KM.Empty_Multiset), Keys (A));
      Models.Lemma_Sum_Empty (Sub_Now (Links (A).Child));
      Models.Lemma_Sum_Add_Left
        (Sub_Now (Links (A).Child), Sub_Now (Rest), Keys (A));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if Rest /= 0 then Node_In_Use (Snap, Rest));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= Rest
            then Node_In_Use (Snap, X)));
      Total_Change (Before, Snap, A, Rest, Capacity);
   end Split;

   -------------
   -- Prepend --
   -------------

   procedure Prepend (A : Slot; B : Tree) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      if B /= 0 then
         Total_Bound (Snap, A, B, Capacity);
         Links (B).Parent := A;
      end if;
      Links (A).Sibling := B;
      Links (A).Size := 1 + Size_Now (Links (A).Child) + Size_Now (B);
      Sub (A) := KM.Add (KM.Sum (Sub_Now (Links (A).Child),
                                 Sub_Now (B)), Keys (A));
      Models.Lemma_Sum_Empty (Sub_Now (Links (A).Child));
      Models.Lemma_Sum_Add_Left
        (Sub_Now (Links (A).Child), Sub_Now (B), Keys (A));
      Join_Model (Sub_Now (Links (A).Child), Sub_Now (B),
                  Before.Sub (A), Sub (A), Keys (A));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if B /= 0 then Node_In_Use (Snap, B));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= B
            then Node_In_Use (Snap, X)));
      Total_Change (Before, Snap, A, B, Capacity);
   end Prepend;

   -----------
   -- Adopt --
   -----------

   procedure Adopt (P, C : Slot; New_Rank : Rank_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Kid : constant Tree := Links (P).Child;
      Below_P, Below_C : KM.Multiset with Ghost;
   begin
      Total_Bound (Snap, P, C, Capacity);
      Below_P := Sub_Now (Kid);
      Below_C := Sub_Now (Links (C).Child);
      Models.Lemma_Sum_Empty (Below_P);
      Models.Lemma_Sum_Empty (Below_C);
      Models.Lemma_Add_Congruent
        (KM.Sum (Below_P, KM.Empty_Multiset), Below_P, Keys (P));
      Models.Lemma_Add_Congruent
        (KM.Sum (Below_C, KM.Empty_Multiset), Below_C, Keys (C));
      pragma Assert (Sub (P) = KM.Add (Below_P, Keys (P)));
      pragma Assert (Sub (C) = KM.Add (Below_C, Keys (C)));
      pragma Assert (Kid /= P and then Kid /= C);
      pragma Assert
        (Links (C).Child /= P and then Links (C).Child /= C
         and then (if Kid /= 0 then Links (Kid).Child /= P
                   and then Links (Kid).Child /= C));
      if Kid /= 0 then
         Links (Kid).Parent := C;
      end if;
      --  C heads P's children. Its own children stay put; its new sibling
      --  is P's former child list.
      Links (C).Sibling := Kid;
      Links (C).Parent := P;
      Links (C).Size := 1 + Size_Now (Links (C).Child) + Size_Now (Kid);
      Sub (C) :=
        KM.Add (KM.Sum (Sub_Now (Links (C).Child), Sub_Now (Kid)), Keys (C));
      Links (P).Child := C;
      Links (P).Rank := New_Rank;
      Links (P).Size := 1 + Size_Now (C);
      Sub (P) := KM.Add (KM.Sum (Sub_Now (C), KM.Empty_Multiset), Keys (P));
      pragma Assert
        (Size_Now (Links (C).Child)
           = Size_Of_Node (Before, Before.Links (C).Child));
      pragma Assert (for all E of Below_C => Keys (C) <= E);
      pragma Assert (for all E of Below_P => Keys (P) <= E);
      pragma Assert (for all E of Sub_Now (C) => Keys (P) <= E);
      pragma Assert (Node_In_Use (Snap, C));
      pragma Assert (Node_In_Use (Snap, P));
      pragma Assert (if Kid /= 0 then Node_In_Use (Snap, Kid));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= P and then X /= C
               and then X /= Kid
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Node_In_Use (Snap, X)));
      pragma Assert (Nodes_Sound (Snap));
      Models.Lemma_Sum_Empty (Sub_Now (C));
      Models.Lemma_Add_Congruent
        (KM.Sum (Sub_Now (C), KM.Empty_Multiset), Sub_Now (C), Keys (P));
      pragma Assert
        (Sub (P) = KM.Add (KM.Add (KM.Sum (Below_C, Below_P),
                                    Keys (C)), Keys (P)));
      Link_Model (Below_P, Below_C, Keys (P), Keys (C));
      pragma Assert
        (Sub (P) = KM.Sum (Sub_Of (Before, P), Sub_Of (Before, C)));
      Total_Change (Before, Snap, P, C, Capacity);
   end Adopt;

   ----------------
   -- Link_Equal --
   ----------------

   procedure Link_Equal (A, B : Slot; R : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      if Keys (A) <= Keys (B) then
         Adopt (A, B, Links (A).Rank + 1);
         R := A;
      else
         Adopt (B, A, Links (B).Rank + 1);
         R := B;
         Models.Lemma_Sum_Symmetric (Sub_Of (Before, B), Sub_Of (Before, A));
      end if;
   end Link_Equal;

   ---------------
   -- Skew_Link --
   ---------------

   procedure Skew_Link (N, A, B : Slot; R : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
      Top : Slot;
      Mid : Snapshot with Ghost;
   begin
      if Keys (N) <= Keys (A) and then Keys (N) <= Keys (B) then
         --  N goes above both trees, and takes the rank they make together
         Adopt (N, B, Links (N).Rank);
         Mid := Snap;
         pragma Assert (Links (A) = Before.Links (A));
         pragma Assert (Before.Links (B).Rank
                          <= Size_Of_Node (Before, Before.Links (B).Child));
         pragma Assert (Before.Links (B).Size
                          = 1 + Size_Of_Node (Before, Before.Links (B).Child));
         pragma Assert (Links (A).Rank + 1 <= Size_Now (Links (N).Child));
         Adopt (N, A, Links (A).Rank + 1);
         R := N;
         Skew_Model (Before.Sub (N), Before.Sub (A), Before.Sub (B),
                     Mid.Sub (N), Sub (N));
      else
         --  The two trees link, and N hangs under the winner with rank 0
         Link_Equal (A, B, Top);
         pragma Assert (Links (N) = Before.Links (N));
         pragma Assert (Keys (Top) <= Keys (N));
         Adopt (Top, N, Links (Top).Rank);
         R := Top;
      end if;
   end Skew_Link;

   --------------
   -- Ins_Tree --
   --------------

   procedure Ins_Tree (A : Slot; L : Tree; R : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      Rest : Tree;
      Linked : Slot;
      M_Front, M_Rest : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      if L = 0 then
         R := A;
         Models.Lemma_Sum_Empty (Sub (A));
      elsif Links (A).Rank /= Links (L).Rank then
         Prepend (A, L);
         R := A;
      else
         Split (L, Rest);
         M_Front := Sub_Now (L);
         M_Rest := Sub_Now (Rest);
         pragma Assert (Links (A) = Before.Links (A));
         Link_Equal (A, L, Linked);
         pragma Assert (Frame (Before, A, L));
         Call_State := Snap;
         Ins_Tree (Linked, Rest, R);
         pragma Assert (Frame (Before, A, L));
         Sum_Regroup (Before.Sub (A), M_Front, M_Rest,
                      Sub_Of (Call_State, Linked), Before.Sub (L));
         pragma Assert
           (for all X in 1 .. Capacity =>
              (if Is_Root (Before, X) and then X /= A and then X /= L
               then X /= Rest));
      end if;
   end Ins_Tree;

   -----------------
   -- Merge_Trees --
   -----------------

   procedure Merge_Trees (A, B : Tree; R : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      A_Rest, B_Rest, Joined : Tree;
      Linked : Slot;
      M_A, M_B, M_A_Rest, M_B_Rest : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      if A = 0 then
         R := B;
         Models.Lemma_Sum_Empty_Left (Sub_Now (B));
      elsif B = 0 then
         R := A;
         Models.Lemma_Sum_Empty (Sub_Now (A));
      elsif Links (A).Rank < Links (B).Rank then
         Split (A, A_Rest);
         M_A := Sub_Now (A);
         M_A_Rest := Sub_Now (A_Rest);
         Merge_Trees (A_Rest, B, Joined);
         pragma Assert (Frame (Before, A, B));
         Call_State := Snap;
         Prepend (A, Joined);
         pragma Assert (Frame (Before, A, B));
         R := A;
         Sum_Regroup (M_A, M_A_Rest, Before.Sub (B),
                      Before.Sub (A), Sub_Of (Call_State, Joined));
      elsif Links (B).Rank < Links (A).Rank then
         Split (B, B_Rest);
         M_B := Sub_Now (B);
         M_B_Rest := Sub_Now (B_Rest);
         Merge_Trees (A, B_Rest, Joined);
         pragma Assert (Frame (Before, A, B));
         Call_State := Snap;
         Prepend (B, Joined);
         pragma Assert (Frame (Before, A, B));
         R := B;
         Sum_Middle (M_B, Before.Sub (A), M_B_Rest,
                     Sub_Of (Call_State, Joined), Before.Sub (B));
      else
         --  Equal ranks: link the two fronts, merge what follows them, and
         --  carry the linked tree into the result.
         Split (A, A_Rest);
         M_A := Sub_Now (A);
         M_A_Rest := Sub_Now (A_Rest);
         Split (B, B_Rest);
         M_B := Sub_Now (B);
         M_B_Rest := Sub_Now (B_Rest);
         Link_Equal (A, B, Linked);
         pragma Assert (Frame (Before, A, B));
         Merge_Trees (A_Rest, B_Rest, Joined);
         pragma Assert (Frame (Before, A, B));
         Call_State := Snap;
         Ins_Tree (Linked, Joined, R);
         pragma Assert (Frame (Before, A, B));
         Sum_Pairs (M_A, M_A_Rest, M_B, M_B_Rest,
                    Before.Sub (A), Before.Sub (B),
                    Sub_Of (Call_State, Linked), Sub_Of (Call_State, Joined));
      end if;
   end Merge_Trees;

   ---------------
   -- Normalize --
   ---------------

   procedure Normalize (A : Tree; R : out Tree) is
      Rest : Tree;
   begin
      if A /= 0
        and then Links (A).Sibling /= 0
        and then Links (A).Rank = Links (Links (A).Sibling).Rank
      then
         Split (A, Rest);
         Ins_Tree (A, Rest, R);
      else
         R := A;
      end if;
   end Normalize;

   ----------------
   -- Meld_Lists --
   ----------------

   procedure Meld_Lists (A, B : Tree; R : out Tree) is
      A_Front, B_Front : Tree;
   begin
      Normalize (A, A_Front);
      Normalize (B, B_Front);
      Merge_Trees (A_Front, B_Front, R);
   end Meld_Lists;

   -----------------
   -- Skew_Insert --
   -----------------

   procedure Skew_Insert (T : in out Tree; N : Slot) is
      Before : constant Snapshot := Snap with Ghost;
      A, B : Slot;
      Rest, Beyond : Tree;
      R : Slot;
      M_A, M_B, M_Rest, M_Beyond : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      if T /= 0
        and then Links (T).Sibling /= 0
        and then Links (T).Rank = Links (Links (T).Sibling).Rank
      then
         A := T;
         Split (A, Rest);
         B := Rest;
         M_A := Sub_Now (A);
         M_Rest := Sub_Now (Rest);
         Split (B, Beyond);
         M_B := Sub_Now (B);
         M_Beyond := Sub_Now (Beyond);
         Skew_Link (N, A, B, R);
         Call_State := Snap;
         Prepend (R, Beyond);
         T := R;
         Insert_Model (Before.Sub (A), M_A, M_B, M_Rest, M_Beyond,
                       Before.Sub (N), Sub_Of (Call_State, R), Sub (R));
      else
         Prepend (N, T);
         Models.Lemma_Sum_Symmetric (Sub_Of (Before, T), Before.Sub (N));
         T := N;
      end if;
   end Skew_Insert;

   function Size_Of (T : Tree) return Extended_Index is (Size_Now (T));

   -------------
   -- Minimum --
   -------------

   function Minimum (T : Slot) return Slot is
      R : Slot := T;
      S : Slot;
   begin
      if Links (T).Sibling /= 0 then
         S := Minimum (Links (T).Sibling);
         if Keys (S) < Keys (T) then
            R := S;
         end if;
      end if;
      return R;
   end Minimum;

   function Peek_Min (T : Tree) return Key_Type is (Keys (Minimum (T)));

   function Min_Of (T : Tree) return Key_Type is (Peek_Min (T));

   ----------
   -- Meld --
   ----------

   procedure Meld (T : in out Tree; U : in out Tree) is
      R : Tree;
   begin
      Meld_Lists (T, U, R);
      T := R;
      U := 0;
   end Meld;

   ------------
   -- Insert --
   ------------

   procedure Insert (T : in out Tree; K : Key_Type) is
      Node : Slot;
      Before : constant Tree := T;
   begin
      Allocate (Node, K);
      Skew_Insert (T, Node);
      Models.Lemma_Sum_Empty (Sub_Now (Before));
      Models.Lemma_Sum_Add (Sub_Now (Before), KM.Empty_Multiset, K);
   end Insert;

   ------------
   -- Detach --
   ------------

   procedure Detach (T : in out Tree; K : Key_Type; M : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
      Head : constant Slot := T;
      Rest : Tree;
      M_Head, M_Rest : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      Split (Head, Rest);
      M_Head := Sub_Now (Head);
      M_Rest := Sub_Now (Rest);
      if Keys (Head) = K then
         M := Head;
         T := Rest;
      else
         pragma Assert (Rest /= 0);
         pragma Assert (KM.Contains (Sub_Now (Rest), K));
         Detach (Rest, K, M);
         pragma Assert (Frame (Before, Head, 0));
         Call_State := Snap;
         Prepend (Head, Rest);
         pragma Assert (Frame (Before, Head, 0));
         T := Head;
         Sum_Middle (Sub (M), M_Head, Sub_Of (Call_State, Rest),
                     Sub (Head), M_Rest);
      end if;
   end Detach;

   ----------
   -- Walk --
   ----------

   procedure Walk (C : Tree; T, Acc : in out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      T0 : constant Tree := T with Ghost;
      A0 : constant Tree := Acc with Ghost;
      T1 : Tree with Ghost;
      Rest : Tree;
      M_Head, M_Rest : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      if C = 0 then
         Models.Lemma_Sum_Empty (KM.Sum (Sub_Now (T), Sub_Now (Acc)));
         return;
      end if;
      Split (C, Rest);
      M_Head := Sub_Now (C);
      M_Rest := Sub_Now (Rest);
      if Links (C).Rank = 0 then
         Skew_Insert (T, C);
         Call_State := Snap;
         T1 := T;
         pragma Assert (Frame (Before, C, T0, A0));
         Walk (Rest, T, Acc);
         Walk_Insert_Model
           (Sub_Of (Before, T0), Sub_Of (Before, A0), M_Head, M_Rest,
            Sub_Of (Before, C), Sub_Of (Call_State, T1),
            KM.Sum (Sub_Now (T), Sub_Now (Acc)));
      else
         Prepend (C, Acc);
         Acc := C;
         Call_State := Snap;
         pragma Assert (Frame (Before, C, T0, A0));
         Walk (Rest, T, Acc);
         Walk_Keep_Model
           (Sub_Of (Before, T0), Sub_Of (Before, A0), M_Head, M_Rest,
            Sub_Of (Before, C), Sub_Of (Call_State, C),
            KM.Sum (Sub_Now (T), Sub_Now (Acc)));
      end if;
      pragma Assert (Frame (Before, C, T0, A0));
   end Walk;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      T0 : constant Tree := T with Ghost;
      M : Slot;
      C : Tree;
      Acc : Tree := 0;
      R : Tree;
      M_Below, M_Rest : KM.Multiset with Ghost;
      S1, S3 : Snapshot with Ghost;
      W_T, W_Acc : Tree with Ghost;
   begin
      K := Peek_Min (T);
      Detach (T, K, M);
      S1 := Snap;
      M_Rest := Sub_Now (T);

      --  Cut the children of M loose, then release M itself
      C := Links (M).Child;
      M_Below := Sub_Now (C);
      Models.Lemma_Sum_Empty (M_Below);
      Models.Lemma_Add_Congruent
        (KM.Sum (M_Below, KM.Empty_Multiset), M_Below, K);
      pragma Assert (Sub (M) = KM.Add (M_Below, K));
      if C /= 0 then
         Links (C).Parent := 0;
      end if;
      Links (M) :=
        (Child => 0, Sibling => 0, Parent => 0, Size => 1, Rank => 0);
      Sub (M) := KM.Add (KM.Empty_Multiset, K);
      Total_Change (S1, Snap, M, C, Capacity);
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);
      pragma Assert (Node_In_Use (Snap, M));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= M and then X /= C
            then Node_In_Use (Snap, X)));
      pragma Assert (Nodes_Sound (Snap));
      pragma Assert (Chain_Sound (Snap));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S1, X) and then X /= M
            then X /= C
                 and then Links (X) = S1.Links (X)
                 and then Sub (X) = S1.Sub (X)));
      Total_Bound_One (Snap, M, Capacity);
      Deallocate (M);
      pragma Assert (Sub_Now (T) = M_Rest);
      pragma Assert (Sub_Now (C) = M_Below);

      --  Rank-0 children go back in one at a time; the others, reversed,
      --  are melded with what is left of the heap.
      Walk (C, T, Acc);
      S3 := Snap;
      W_T := T;
      W_Acc := Acc;
      Meld_Lists (T, Acc, R);
      T := R;
      Extract_Model (Entry_State.Sub (T0), M_Rest, M_Below,
                     KM.Sum (Sub_Of (S3, W_T), Sub_Of (S3, W_Acc)),
                     Sub_Now (T), K);
   end Extract_Min;

   --------------
   -- Allocate --
   --------------

   procedure Allocate (I : out Slot; K : Key_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Head : constant Slot := Free;
      Next : constant Tree := Links (Head).Child;
   begin
      I := Head;
      Free := Next;
      Free_Count := Free_Count - 1;
      Chain_Pos (Head) := 0;
      Keys (Head) := K;
      Links (Head) :=
        (Child => 0, Sibling => 0, Parent => 0,
         Size => 1, Rank => 0);
      Sub (Head) := KM.Add (KM.Empty_Multiset, K);
      Total_Change (Before, Snap, Head, 0, Capacity);
      pragma Assert
        (Total (Snap, Capacity) + Long_Long_Integer (Free_Count)
           = Long_Long_Integer (Capacity));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X)
            then X /= Head and then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) then Node_In_Use (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not In_Use (Snap, X) then Node_Free (Snap, X)));
      pragma Assert (Chain_Sound (Snap));
      pragma Assert (Nodes_Sound (Snap));
   end Allocate;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (I : Slot) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      Links (I) :=
        (Child => Free, Sibling => 0, Parent => 0,
         Size => 0, Rank => 0);
      Free_Count := Free_Count + 1;
      Chain_Pos (I) := Free_Count;
      Chain_At (Free_Count) := I;
      Free := I;
      Total_Change (Before, Snap, I, 0, Capacity);

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not In_Use (Before, X)
            then Chain_Pos (X) = Before.Chain_Pos (X)
                 and then Chain_Pos (X) <= Free_Count - 1));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) and then X /= I
            then Links (X) = Before.Links (X)
                 and then Node_In_Use (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not In_Use (Snap, X) then Node_Free (Snap, X)));
   end Deallocate;

   -----------
   -- Clear --
   -----------

   procedure Clear is
   begin
      Chain_Pos := [for J in 1 .. Capacity => J];
      Chain_At := [for J in 1 .. Capacity => J];
      Sub := [for J in 1 .. Capacity => KM.Empty_Multiset];

      for I in 1 .. Capacity loop
         Links (I) :=
           (Child => (if I = 1 then 0 else I - 1),
            Sibling => 0, Parent => 0,
            Size => 0, Rank => 0);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Links (J) =
                (Child   => (if J = 1 then 0 else J - 1),
                 Sibling => 0,
                 Parent  => 0,
                 Size    => 0,
                 Rank    => 0));
      end loop;

      Free := Capacity;
      Free_Count := Capacity;

      pragma Assert (Chain_Pos (Free) = Free_Count);
      pragma Assert (for all I in 1 .. Capacity => not In_Use (Snap, I));
      pragma Assert
        (for all K in 1 .. Capacity =>
           Chain_At (K) in 1 .. Capacity
           and then Chain_Pos (Chain_At (K)) = K);
      pragma Assert
        (for all I in 1 .. Capacity =>
           Chain_Pos (I) in 1 .. Capacity
           and then Chain_Pos (I) <= Free_Count
           and then Chain_At (Chain_Pos (I)) = I);
      pragma Assert
        (for all I in 1 .. Capacity =>
           (if Chain_Pos (I) = 1
            then Links (I).Child = 0
            else Links (I).Child /= 0
                 and then Chain_Pos (Links (I).Child)
                              = Chain_Pos (I) - 1));
      pragma Assert (for all I in 1 .. Capacity => Node_Free (Snap, I));
      pragma Assert (Chain_Sound (Snap));
      pragma Assert (Nodes_Sound (Snap));
      Total_Zero (Snap, Capacity);
   end Clear;

end Heaps.Skew_Binomial;
