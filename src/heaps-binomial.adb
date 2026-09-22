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

package body Heaps.Binomial with SPARK_Mode is

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

   procedure Sum_Result (A, B, C, D, Result : KM.Multiset)
     with Ghost,
          Pre => A = C and then B = D and then Result = KM.Sum (A, B),
          Post => Result = KM.Sum (C, D);
   procedure Sum_Result (A, B, C, D, Result : KM.Multiset) is null;

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

   procedure Remove_Model
     (Old, Head, Rest, New_Rest, Result : KM.Multiset; K : Key_Type)
     with Ghost,
          Pre => Old = KM.Sum (Head, Rest)
                 and then Rest = KM.Add (New_Rest, K)
                 and then Result = KM.Sum (Head, New_Rest),
          Post => Old = KM.Add (Result, K);
   procedure Remove_Model
     (Old, Head, Rest, New_Rest, Result : KM.Multiset; K : Key_Type) is null;

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

   procedure Total_Bound (S : Snapshot; I : Slot; N : Tree)
     with Ghost, Pre => I <= N,
          Post => Root_Size (S, I) <= Total (S, N),
          Subprogram_Variant => (Decreases => N);

   procedure Total_Bound (S : Snapshot; I : Slot; N : Tree) is
   begin
      if I < N then
         Total_Bound (S, I, N - 1);
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
                                    and then Sub (X) = Snap'Old.Sub (X)));
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
                                    and then Sub (X) = Snap'Old.Sub (X)));

   function Stable (S : Snapshot) return Boolean is
     (Keys = S.Keys and then Chain_Pos = S.Chain_Pos
      and then Chain_At = S.Chain_At
      and then Free = S.Free and then Free_Count = S.Free_Count) with Ghost;

   function Frame (S : Snapshot; A, B : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Is_Root (S, X) and then X /= A and then X /= B
         then Links (X) = S.Links (X) and then Sub (X) = S.Sub (X)))
     with Ghost;

   function Origins (S : Snapshot; A, B, R : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Is_Root (Snap, X) and then X /= R
         then Is_Root (S, X) and then X /= A and then X /= B))
     with Ghost;

   procedure Weight_Laws (A, B : Rank_Type)
     with Ghost,
          Post => (Weight (A) < Weight (B)) = (A < B)
                  and then (if A < Max_Rank
                            then Weight (A + 1) = 2 * Weight (A));

   procedure Weight_Laws (A, B : Rank_Type) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Weight);
      pragma Unreferenced (A, B);
   begin
      for R in Rank_Type loop
         pragma Loop_Invariant
           (for all J in 0 .. R =>
              Weight (J) = 2 ** J
              and then (if J < Max_Rank
                        then Weight (J + 1) = 2 * Weight (J)));
      end loop;
   end Weight_Laws;

   --  Split and Prepend change only the first root and the incoming link
   --  of its successor. Link_Equal combines two isolated trees. All three
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
                           and then Sub (X) = Snap'Old.Sub (X)))
                  and then (if Rest /= 0
                            then Links (Rest).Size = Snap'Old.Links (Rest).Size
                                 and then Links (Rest).Rank
                                            = Snap'Old.Links (Rest).Rank
                                 and then Sub (Rest) = Snap'Old.Sub (Rest))
                  and then Frame (Snap'Old, A, 0);

   procedure Prepend (A : Slot; B : Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then A /= B and then Links (A).Sibling = 0
                 and then Rank_Now (B) < Rank_Now (A)
                 and then Size_Now (A) + Size_Now (B) <= Capacity,
          Post => Valid and then Stable (Snap'Old) and then Is_Root (A)
                  and then Links (A).Rank = Snap'Old.Links (A).Rank
                  and then Links (A).Size
                             = Snap'Old.Links (A).Size
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub (A)
                             = KM.Sum (Snap'Old.Sub (A), Sub_Of (Snap'Old, B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, A);

   procedure Link_Equal (A, B : Slot; R : out Slot)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then A /= B
                 and then Links (A).Sibling = 0
                 and then Links (B).Sibling = 0
                 and then Links (A).Rank = Links (B).Rank
                 and then Size_Now (A) + Size_Now (B) <= Capacity,
          Post => Valid and then Stable (Snap'Old)
                  and then (R = A or else R = B)
                  and then Is_Root (R) and then Links (R).Sibling = 0
                  and then Links (R).Rank = Snap'Old.Links (A).Rank + 1
                  and then Links (R).Size
                             = Snap'Old.Links (A).Size
                               + Snap'Old.Links (B).Size
                  and then Sub (R)
                             = KM.Sum (Snap'Old.Sub (A), Snap'Old.Sub (B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R);

   procedure Merge (A, B : Tree; R : out Tree)
     with Pre => Valid and then Is_Root (A) and then Is_Root (B)
                 and then (if A /= 0 then A /= B)
                 and then Size_Now (A) + Size_Now (B) <= Capacity,
          Post => Valid and then Stable (Snap'Old) and then Is_Root (R)
                  and then Size_Now (R)
                             = Size_Of_Node (Snap'Old, A)
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub_Now (R)
                             = KM.Sum (Sub_Of (Snap'Old, A),
                                       Sub_Of (Snap'Old, B))
                  and then Rank_Now (R)
                             <= Integer'Max
                                  ((if A = 0 then -1
                                    else Snap'Old.Links (A).Rank),
                                   (if B = 0 then -1
                                   else Snap'Old.Links (B).Rank)) + 1
                  and then (if R /= 0 and then Is_Root (Snap'Old, R)
                            then R = A or else R = B)
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R),
          Subprogram_Variant =>
            (Decreases => Integer'Max (Rank_Now (A), Rank_Now (B)));

   function Minimum (T : Slot) return Slot
     with Pre => Valid and then In_Use (Snap, T),
          Post => In_Use (Snap, Minimum'Result)
                  and then Is_Minimum (Snap, T, Keys (Minimum'Result))
                  and then KM.Contains (Sub_Now (T), Keys (Minimum'Result)),
          Subprogram_Variant => (Decreases => Rank_Now (T));

   procedure Remove_Min (T : in out Tree; K : Key_Type)
     with Pre => Valid and then Is_Root (T) and then T /= 0
                 and then Room < Capacity
                 and then Is_Minimum (Snap, T, K)
                 and then KM.Contains (Sub_Now (T), K),
          Post => Valid and then Is_Root (T)
                  and then Room = Room'Old + 1
                  and then Size_Now (T) = Size_Of_Node (Snap'Old, T'Old) - 1
                  and then Rank_Now (T) <= Snap'Old.Links (T'Old).Rank
                  and then Is_Minimum (Snap'Old, T'Old, K)
                  and then Sub_Of (Snap'Old, T'Old) = KM.Add (Sub_Now (T), K)
                  and then (if T /= 0 and then Is_Root (Snap'Old, T)
                            then T = T'Old)
                  and then (for all X in 1 .. Capacity =>
                     (if Is_Root (Snap'Old, X) and then X /= T'Old
                      then Is_Root (X)
                           and then Links (X) = Snap'Old.Links (X)
                           and then Sub (X) = Snap'Old.Sub (X)))
                  and then Origins (Snap'Old, T'Old, 0, T),
          Subprogram_Variant => (Decreases => Rank_Now (T));

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

   procedure Prepend (A : Slot; B : Tree) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      if B /= 0 then
         Weight_Laws (Links (B).Rank + 1, Links (A).Rank);
         Weight_Laws (Links (B).Rank, Links (A).Rank);
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

   procedure Link_Equal (A, B : Slot; R : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
      Top, Loser : Slot;
      Kid : Tree;
      Below_Top, Below_Loser : KM.Multiset with Ghost;
   begin
      if Keys (A) <= Keys (B) then
         Top := A;
         Loser := B;
      else
         Top := B;
         Loser := A;
      end if;
      Weight_Laws (Links (Top).Rank, Links (Loser).Rank);
      Kid := Links (Top).Child;
      Below_Top := Sub_Now (Kid);
      Below_Loser := Sub_Now (Links (Loser).Child);
      Models.Lemma_Sum_Empty (Below_Top);
      Models.Lemma_Sum_Empty (Below_Loser);
      Models.Lemma_Add_Congruent
        (KM.Sum (Below_Top, KM.Empty_Multiset), Below_Top, Keys (Top));
      Models.Lemma_Add_Congruent
        (KM.Sum (Below_Loser, KM.Empty_Multiset), Below_Loser, Keys (Loser));
      pragma Assert (Sub (Top) = KM.Add (Below_Top, Keys (Top)));
      pragma Assert (Sub (Loser) = KM.Add (Below_Loser, Keys (Loser)));
      pragma Assert (Kid /= Top and then Kid /= Loser);
      pragma Assert
        (Links (Loser).Child /= Top and then Links (Loser).Child /= Loser
         and then (if Kid /= 0 then Links (Kid).Child /= Top
                   and then Links (Kid).Child /= Loser));
      if Kid /= 0 then
         Links (Kid).Parent := Loser;
      end if;
      --  The loser heads the winner's children. Its old children stay put;
      --  its new sibling is the winner's former child list.
      Links (Loser).Sibling := Kid;
      Links (Loser).Parent := Top;
      Links (Loser).Size :=
        1 + Size_Now (Links (Loser).Child) + Size_Now (Kid);
      Sub (Loser) :=
        KM.Add (KM.Sum (Sub_Now (Links (Loser).Child), Sub_Now (Kid)),
                Keys (Loser));
      Links (Top).Child := Loser;
      Links (Top).Rank := Links (Top).Rank + 1;
      Links (Top).Size := 1 + Size_Now (Loser);
      Sub (Top) := KM.Add (KM.Sum (Sub_Now (Loser), KM.Empty_Multiset),
                           Keys (Top));
      R := Top;
      pragma Assert
        (Size_Now (Links (Loser).Child)
           = Size_Of_Node (Before, Before.Links (Loser).Child));
      pragma Assert
        (Size_Now (Links (Top).Child) = Weight (Links (Top).Rank) - 1);
      pragma Assert (for all E of Below_Loser => Keys (Loser) <= E);
      pragma Assert (for all E of Below_Top => Keys (Top) <= E);
      pragma Assert (for all E of Sub_Now (Loser) => Keys (Top) <= E);
      pragma Assert (Node_In_Use (Snap, Loser));
      pragma Assert (Node_In_Use (Snap, Top));
      pragma Assert (if Kid /= 0 then Node_In_Use (Snap, Kid));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= Top and then X /= Loser
               and then X /= Kid
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Node_In_Use (Snap, X)));
      pragma Assert (Nodes_Sound (Snap));
      Models.Lemma_Sum_Empty (Sub_Now (Loser));
      Models.Lemma_Add_Congruent
        (KM.Sum (Sub_Now (Loser), KM.Empty_Multiset),
         Sub_Now (Loser), Keys (Top));
      pragma Assert
        (Sub (Top) = KM.Add (KM.Add (KM.Sum (Below_Loser, Below_Top),
                                      Keys (Loser)), Keys (Top)));
      Link_Model (Below_Top, Below_Loser, Keys (Top), Keys (Loser));
      pragma Assert
        (Sub (Top) = KM.Sum (Sub_Of (Before, Top), Sub_Of (Before, Loser)));
      Models.Lemma_Sum_Symmetric (Sub_Of (Before, A), Sub_Of (Before, B));
      Total_Change (Before, Snap, A, B, Capacity);
   end Link_Equal;

   procedure Merge (A, B : Tree; R : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      Held : constant Extended_Index := Size_Now (A) + Size_Now (B) with Ghost;
      Top, Other : Slot;
      Tail, Tail_B, Joined, Rest : Tree;
      Carry : Slot;
      M_Top, M_Tail, M_Other, M_Tail_B : KM.Multiset with Ghost;
      M_Joined, M_First, M_Rest : KM.Multiset with Ghost;
      Call_State : Snapshot with Ghost;
   begin
      if A = 0 or else B = 0 then
         R := (if A = 0 then B else A);
         Models.Lemma_Sum_Empty (Sub_Now (R));
         Models.Lemma_Sum_Empty_Left (Sub_Now (R));
         return;
      end if;
      if Links (A).Rank >= Links (B).Rank then
         Top := A;
         Other := B;
      else
         Top := B;
         Other := A;
      end if;
      --  Recurse on strictly smaller ranks. On return there can be at most
      --  one carry into Top's rank, which one equal-rank link resolves.
      Split (Top, Tail);
      M_Top := Sub_Now (Top);
      M_Tail := Sub_Now (Tail);
      pragma Assert
        (Size_Now (Top) + Size_Now (Tail) + Size_Now (Other) = Held);
      pragma Assert (Frame (Before, A, B));
      if Links (Top).Rank = Links (Other).Rank then
         --  Link the two large roots; merge their smaller-rank suffixes.
         Split (Other, Tail_B);
         M_Other := Sub_Now (Other);
         M_Tail_B := Sub_Now (Tail_B);
         pragma Assert
           (Size_Now (Top) + Size_Now (Tail)
              + Size_Now (Other) + Size_Now (Tail_B) = Held);
         Link_Equal (Top, Other, Carry);
         pragma Assert
           (Size_Now (Carry) + Size_Now (Tail) + Size_Now (Tail_B) = Held);
         pragma Assert (Frame (Before, A, B));
         Call_State := Snap;
         Merge (Tail, Tail_B, Joined);
         Sum_Result (Sub_Of (Call_State, Tail), Sub_Of (Call_State, Tail_B),
                     M_Tail, M_Tail_B, Sub_Now (Joined));
         pragma Assert (Size_Now (Carry) + Size_Now (Joined) = Held);
         pragma Assert (Frame (Before, A, B));
         Sum_Pairs (M_Top, M_Tail, M_Other, M_Tail_B,
                    Sub_Of (Before, Top), Sub_Of (Before, Other),
                    Sub_Now (Carry), Sub_Now (Joined));
         pragma Assert
           (for all X in 1 .. Capacity =>
              (if Is_Root (Before, X) and then X /= A and then X /= B
               then X /= Carry and then X /= Joined));
         Prepend (Carry, Joined);
         pragma Assert (Frame (Before, A, B));
         R := Carry;
         pragma Assert
           (Sub_Now (R)
              = KM.Sum (Sub_Of (Before, Top), Sub_Of (Before, Other)));
      else
         M_Other := Sub_Now (Other);
         Merge (Tail, Other, Joined);
         M_Joined := Sub_Now (Joined);
         pragma Assert (Size_Now (Top) + Size_Now (Joined) = Held);
         pragma Assert (Frame (Before, A, B));
         if Rank_Now (Joined) = Rank_Now (Top) then
            --  The recursive merge carried into the saved root's rank.
            Split (Joined, Rest);
            M_First := Sub_Now (Joined);
            M_Rest := Sub_Now (Rest);
            pragma Assert
              (Size_Now (Top) + Size_Now (Joined) + Size_Now (Rest) = Held);
            Link_Equal (Top, Joined, Carry);
            pragma Assert (Size_Now (Carry) + Size_Now (Rest) = Held);
            Sum_Regroup (M_Top, M_First, M_Rest, Sub_Now (Carry), M_Joined);
            pragma Assert (Frame (Before, A, B));
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Is_Root (Before, X) and then X /= A and then X /= B
                  then X /= Carry and then X /= Rest));
            Call_State := Snap;
            Prepend (Carry, Rest);
            Sum_Result (Sub_Of (Call_State, Carry), Sub_Of (Call_State, Rest),
                        Sub_Of (Call_State, Carry), M_Rest, Sub_Now (Carry));
            pragma Assert (Frame (Before, A, B));
            R := Carry;
         else
            Call_State := Snap;
            Prepend (Top, Joined);
            Sum_Result (Sub_Of (Call_State, Top), Sub_Of (Call_State, Joined),
                        M_Top, M_Joined, Sub_Now (Top));
            pragma Assert (Frame (Before, A, B));
            R := Top;
         end if;
         pragma Assert (Sub_Now (R) = KM.Sum (M_Top, M_Joined));
         Sum_Regroup (M_Top, M_Tail, M_Other, Sub_Of (Before, Top), M_Joined);
         Sum_Result (Sub_Of (Before, Top), M_Other,
                     Sub_Of (Before, Top), Sub_Of (Before, Other),
                     Sub_Now (R));
      end if;
      Models.Lemma_Sum_Symmetric (Sub_Of (Before, A), Sub_Of (Before, B));
      pragma Assert
        (Size_Now (R) = Size_Of_Node (Before, A) + Size_Of_Node (Before, B));
      pragma Assert (Frame (Before, A, B));
      pragma Assert (Origins (Before, A, B, R));
   end Merge;

   function Size_Of (T : Tree) return Extended_Index is (Size_Now (T));

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

   procedure Meld (T : in out Tree; U : in out Tree) is
      R : Tree;
   begin
      Merge (T, U, R);
      T := R;
      U := 0;
   end Meld;

   procedure Insert (T : in out Tree; K : Key_Type) is
      Node : Slot;
      R : Tree;
      Before : constant Tree := T;
   begin
      if T /= 0 then
         Total_Bound (Snap, T, Capacity);
      end if;
      Allocate (Node, K);
      Merge (T, Node, R);
      T := R;
      Models.Lemma_Sum_Empty (Sub_Now (Before));
      Models.Lemma_Sum_Add (Sub_Now (Before), KM.Empty_Multiset, K);
   end Insert;

   procedure Remove_Min (T : in out Tree; K : Key_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Head : constant Slot := T;
      Rest, Child, R : Tree;
      Before : Snapshot with Ghost;
      M_Head, M_Rest, M_Child : KM.Multiset with Ghost;
   begin
      --  K was selected once by Peek_Min. Detach roots until its first
      --  occurrence, then merge that root's children with its suffix and
      --  restore the larger-rank prefix on the way back.
      Split (Head, Rest);
      M_Head := Sub_Now (Head);
      M_Rest := Sub_Now (Rest);
      if K = Keys (Head) then
         Before := Snap;
         Child := Links (Head).Child;
         M_Child := Sub_Now (Child);
         Models.Lemma_Sum_Empty (M_Child);
         Models.Lemma_Add_Congruent
           (KM.Sum (M_Child, KM.Empty_Multiset), M_Child, K);
         pragma Assert (M_Head = KM.Add (M_Child, K));
         if Child /= 0 then
            Links (Child).Parent := 0;
         end if;
         Links (Head) :=
           (Child => 0, Sibling => 0, Parent => 0, Size => 1, Rank => 0);
         Sub (Head) := KM.Add (KM.Empty_Multiset, K);
         Total_Change (Before, Snap, Head, Child, Capacity);
         Models.Lemma_Sum_Empty (KM.Empty_Multiset);
         pragma Assert (Node_In_Use (Snap, Head));
         pragma Assert (if Child /= 0 then Node_In_Use (Snap, Child));
         pragma Assert
           (for all X in 1 .. Capacity =>
              (if In_Use (Snap, X) and then X /= Head and then X /= Child
               then Node_In_Use (Snap, X)));
         pragma Assert (Nodes_Sound (Snap));
         pragma Assert (Chain_Sound (Snap));
         Deallocate (Head);
         pragma Assert (Frame (Entry_State, Head, 0));
         Merge (Child, Rest, R);
         pragma Assert (Frame (Entry_State, Head, 0));
         T := R;
         Models.Lemma_Sum_Empty (M_Child);
         Models.Lemma_Sum_Symmetric (M_Head, M_Rest);
         Models.Lemma_Sum_Symmetric (M_Child, M_Rest);
         Remove_Model (Sub_Of (Entry_State, Head), M_Rest, M_Head,
                       M_Child, Sub_Now (T), K);
      else
         pragma Assert (Rest /= 0);
         pragma Assert (KM.Contains (Sub_Now (Rest), K));
         Remove_Min (Rest, K);
         pragma Assert (Frame (Entry_State, Head, 0));
         M_Child := Sub_Now (Rest);
         Prepend (Head, Rest);
         pragma Assert (Frame (Entry_State, Head, 0));
         T := Head;
         Remove_Model (Sub_Of (Entry_State, Head), M_Head, M_Rest,
                       M_Child, Sub_Now (T), K);
      end if;
   end Remove_Min;

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
   begin
      K := Peek_Min (T);
      Remove_Min (T, K);
   end Extract_Min;

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

   -------------
   -- Clear   --
   -------------

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

end Heaps.Binomial;
