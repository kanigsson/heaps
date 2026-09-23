--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

with Heaps.Models;

package body Heaps.Fibonacci with SPARK_Mode is

   package KM renames Key_Multisets;

   --  Multiset equality is extensional. These proved algebraic lemmas
   --  compose helper results without unfolding the whole arena again.

   procedure Link_Model (C, D : KM.Multiset; K, L : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Add (KM.Sum (D, C), L), K)
                    = KM.Sum (KM.Add (C, K), KM.Add (D, L));
   procedure Link_Model (C, D : KM.Multiset; K, L : Key_Type) is null;

   procedure Shift_Model (C, S, M : KM.Multiset; K : Key_Type)
     with Ghost,
          Post => KM.Sum (KM.Add (KM.Sum (C, S), K), M)
                    = KM.Add (KM.Sum (C, KM.Sum (S, M)), K);
   procedure Shift_Model (C, S, M : KM.Multiset; K : Key_Type) is null;
   --  Appending M behind a node's sibling suffix, which is what a
   --  concatenation does to every node of the list in front

   procedure Pop_Model (C, N, D : KM.Multiset; K, L : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Sum (KM.Add (KM.Sum (D, N), L),
                                  KM.Empty_Multiset), K)
                    = KM.Sum (KM.Add (KM.Sum (N, KM.Empty_Multiset), K),
                              KM.Add (KM.Sum (D, KM.Empty_Multiset), L));
   procedure Pop_Model (C, N, D : KM.Multiset; K, L : Key_Type) is null;
   --  Detaching the first child, of key L, children D and later siblings N,
   --  from a node of key K

   procedure Sum_Swap (A, B, C : KM.Multiset)
     with Ghost,
          Post => KM.Sum (KM.Sum (A, B), C) = KM.Sum (KM.Sum (A, C), B);
   procedure Sum_Swap (A, B, C : KM.Multiset) is null;

   ----------------
   -- Accounting --
   ----------------

   function Part (S : Snapshot; I, N : Tree) return Long_Long_Integer is
     (if I <= N then Root_Size (S, I) else 0) with Ghost;

   --  A local operation changes the contribution of at most two heads.
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

   procedure Total_Bound_One (S : Snapshot; K : Slot; M : Tree)
     with Ghost, Pre => K <= M,
          Post => Root_Size (S, K) <= Total (S, M),
          Subprogram_Variant => (Decreases => M);

   procedure Total_Bound_One (S : Snapshot; K : Slot; M : Tree) is
   begin
      if K < M then
         Total_Bound_One (S, K, M - 1);
      end if;
   end Total_Bound_One;

   procedure Total_Bound (S : Snapshot; I, J : Slot; N : Tree)
     with Ghost, Pre => I <= N and then J <= N and then I /= J,
          Post => Root_Size (S, I) + Root_Size (S, J) <= Total (S, N),
          Subprogram_Variant => (Decreases => N);
   --  Two distinct heads hold no more nodes between them than the arena

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

   ------------
   -- Weight --
   ------------

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

   ----------------------
   -- Frame predicates --
   ----------------------

   function Stable (S : Snapshot) return Boolean is
     (Keys = S.Keys and then Chain_Pos = S.Chain_Pos
      and then Chain_At = S.Chain_At
      and then Free = S.Free and then Free_Count = S.Free_Count) with Ghost;

   function Head_Now (T : Tree) return Boolean is (Is_Head (Snap, T))
     with Ghost;

   function Same (After, Before : Snapshot; X : Slot) return Boolean is
     (Is_Head (After, X)
      and then After.Links (X) = Before.Links (X)
      and then KM.Multiset_Logic_Equal (After.Sub (X), Before.Sub (X))
      and then After.Meta (X) = Before.Meta (X))
     with Ghost;
   --  X is a head in After, with the links, model and ghost data it had in
   --  Before. The model is compared by logical rather than extensional
   --  equality, so that the relation chains across steps by rewriting alone.

   function Unchanged (S : Snapshot; X : Slot) return Boolean is
     (Same (Snap, S, X))
     with Ghost;

   function Frame (S : Snapshot; A, B : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Is_Head (S, X) and then X /= A and then X /= B
         then Unchanged (S, X)))
     with Ghost;
   --  Every head the operation does not name comes back untouched

   function Origins (S : Snapshot; A, B, R1, R2 : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Head_Now (X) and then X /= R1 and then X /= R2
         then Is_Head (S, X) and then X /= A and then X /= B))
     with Ghost;
   --  Every head other than the results was a head, and not an operand

   --------------------
   -- List structure --
   --------------------

   --  A root list of one node owns no other node, because every node it
   --  owns sits between its head and its tail.

   procedure Lemma_Only_Owner (H : Slot)
     with Ghost,
          Pre => Valid and then Is_Head (Snap, H)
                 and then Links (H).Sibling = 0,
          Post => Links (H).Last = H
                  and then Meta (H).Owner = H
                  and then Meta (H).Pos = 1
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap, X) and then Meta (X).Owner = H
                               then X = H));

   procedure Lemma_Only_Owner (H : Slot) is
   begin
      pragma Assert (Node_In_Use (Snap, H));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Meta (X).Owner = H
            then Node_In_Use (Snap, X)
                 and then Meta (X).Pos <= 1));
   end Lemma_Only_Owner;

   --  Sizes decrease along a list, so none exceeds that of its head. The
   --  induction runs back up the list, towards smaller positions.

   procedure Lemma_Below_Owner (X : Slot)
     with Ghost,
          Pre => Valid and then In_Use (Snap, X)
                 and then Meta (X).Owner /= 0,
          Post => Meta (X).Size <= Meta (Meta (X).Owner).Size,
          Subprogram_Variant => (Decreases => Meta (X).Pos);

   procedure Lemma_Below_Owner (X : Slot) is
      P : Tree;
   begin
      pragma Assert (Node_In_Use (Snap, X));
      if Meta (X).Owner /= X then
         P := Meta (X).Parent;
         pragma Assert (P /= 0 and then In_Use (Snap, P));
         pragma Assert (Node_In_Use (Snap, P));
         pragma Assert (Links (P).Child /= X);
         pragma Assert (Links (P).Sibling = X);
         pragma Assert (Meta (P).Owner = Meta (X).Owner);
         pragma Assert (Meta (P).Pos + 1 = Meta (X).Pos);
         Lemma_Below_Owner (P);
      end if;
   end Lemma_Below_Owner;

   procedure Lemma_All_Below_Owner (H : Slot)
     with Ghost,
          Pre => Valid and then Is_Head (Snap, H),
          Post => (for all X in 1 .. Capacity =>
                     (if In_Use (Snap, X) and then Meta (X).Owner = H
                      then Meta (X).Size <= Meta (H).Size));

   procedure Lemma_All_Below_Owner (H : Slot) is
   begin
      for X in 1 .. Capacity loop
         if In_Use (Snap, X) and then Meta (X).Owner = H then
            Lemma_Below_Owner (X);
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              (if In_Use (Snap, Y) and then Meta (Y).Owner = H
               then Meta (Y).Size <= Meta (H).Size));
      end loop;
   end Lemma_All_Below_Owner;

   --  What a concatenation does to the model of every node in front

   procedure Lemma_Shift_All (S : Snapshot; A : Slot; M : KM.Multiset)
     with Ghost,
          Pre => Valid (S),
          Post => (for all X in 1 .. Capacity =>
                     (if In_Use (S, X) and then S.Meta (X).Owner = A
                      then KM.Sum (S.Sub (X), M)
                           = KM.Add
                               (KM.Sum (Sub_Of (S, S.Links (X).Child),
                                        KM.Sum (Sub_Of (S, S.Links (X).Sibling),
                                                M)),
                                S.Keys (X))));

   procedure Lemma_Shift_All (S : Snapshot; A : Slot; M : KM.Multiset) is
   begin
      for X in 1 .. Capacity loop
         if In_Use (S, X) and then S.Meta (X).Owner = A then
            pragma Assert (Node_In_Use (S, X));
            Shift_Model (Sub_Of (S, S.Links (X).Child),
                         Sub_Of (S, S.Links (X).Sibling), M, S.Keys (X));
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              (if In_Use (S, Y) and then S.Meta (Y).Owner = A
               then KM.Sum (S.Sub (Y), M)
                    = KM.Add
                        (KM.Sum (Sub_Of (S, S.Links (Y).Child),
                                 KM.Sum (Sub_Of (S, S.Links (Y).Sibling), M)),
                         S.Keys (Y))));
      end loop;
   end Lemma_Shift_All;

   ----------------
   -- Primitives --
   ----------------

   procedure Allocate (I : out Slot; K : Key_Type)
     with Pre  => Valid and then Room >= 1,
          Post => Valid
                  and then Is_Head (Snap, I)
                  and then Room = Room'Old - 1
                  and then Keys (I) = K
                  and then Sub (I) = KM.Add (KM.Empty_Multiset, K)
                  and then Links (I).Child = 0
                  and then Links (I).Sibling = 0
                  and then Links (I).Rank = 0
                  and then Meta (I).Size = 1
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                               then X /= I
                                    and then In_Use (Snap, X)
                                    and then Keys (X) = Snap'Old.Keys (X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Meta (X) = Snap'Old.Meta (X)
                                    and then KM.Multiset_Logic_Equal
                                               (Sub (X), Snap'Old.Sub (X))));

   procedure Deallocate (I : Slot)
     with Pre  => Valid
                  and then Room < Capacity
                  and then Is_Head (Snap, I)
                  and then Links (I).Child = 0
                  and then Links (I).Sibling = 0,
          Post => Valid
                  and then not In_Use (Snap, I)
                  and then Room = Room'Old + 1
                  and then Keys = Snap'Old.Keys
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap, X)
                               then In_Use (Snap'Old, X) and then X /= I))
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X) and then X /= I
                               then In_Use (Snap, X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Meta (X) = Snap'Old.Meta (X)
                                    and then KM.Multiset_Logic_Equal
                                               (Sub (X), Snap'Old.Sub (X))));

   --  The four primitives below each preserve the arena invariant, so their
   --  callers never inherit a broken forest.

   procedure Split (A : Slot; Rest : out Tree)
     with Pre => Valid and then Is_Head (Snap, A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Head (Snap, A)
                  and then Rest = Snap'Old.Links (A).Sibling
                  and then (if Rest /= 0
                            then Is_Head (Snap, Rest)
                                 and then not Is_Head (Snap'Old, Rest))
                  and then Links (A).Sibling = 0
                  and then Links (A).Rank = Snap'Old.Links (A).Rank
                  and then Links (A).Child = Snap'Old.Links (A).Child
                  and then Size_Now (A) + Size_Now (Rest)
                             = Snap'Old.Meta (A).Size
                  and then KM.Sum (Sub_Now (A), Sub_Now (Rest))
                             = Snap'Old.Sub (A)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, 0, 0, A, Rest);

   procedure Append (A : Slot; B : Tree)
     with Pre => Valid and then Is_Head (Snap, A)
                 and then (B = 0 or else Is_Head (Snap, B))
                 and then A /= B,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Head (Snap, A)
                  and then Links (A).Rank = Snap'Old.Links (A).Rank
                  and then Links (A).Child = Snap'Old.Links (A).Child
                  and then Meta (A).Size
                             = Snap'Old.Meta (A).Size
                               + Size_Of_Node (Snap'Old, B)
                  and then Sub (A)
                             = KM.Sum (Snap'Old.Sub (A), Sub_Of (Snap'Old, B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, B, 0, A, 0);
   --  Concatenate the list of B behind that of A. Only the old tail of A
   --  and the new tail pointer change; the rest of the update is ghost.

   procedure Link_Equal (A, B : Slot; R : out Slot)
     with Pre => Valid and then Is_Head (Snap, A) and then Is_Head (Snap, B)
                 and then A /= B
                 and then Links (A).Sibling = 0
                 and then Links (B).Sibling = 0
                 and then Links (A).Rank = Links (B).Rank
                 and then Size_Now (A) + Size_Now (B) <= Capacity,
          Post => Valid and then Stable (Snap'Old)
                  and then (R = A or else R = B)
                  and then Is_Head (Snap, R) and then Links (R).Sibling = 0
                  and then Links (R).Rank = Snap'Old.Links (A).Rank + 1
                  and then Sub (R)
                             = KM.Sum (Snap'Old.Sub (A), Snap'Old.Sub (B))
                  and then Frame (Snap'Old, A, B)
                  and then Origins (Snap'Old, A, B, R, 0);

   procedure Pop_Child (H : Slot; C : out Slot)
     with Pre => Valid and then Is_Head (Snap, H)
                 and then Links (H).Sibling = 0
                 and then Links (H).Child /= 0,
          Post => Valid and then Stable (Snap'Old)
                  and then C = Snap'Old.Links (H).Child
                  and then C /= H
                  and then Is_Head (Snap, H) and then Links (H).Sibling = 0
                  and then Links (H).Rank < Snap'Old.Links (H).Rank
                  and then Is_Head (Snap, C) and then Links (C).Sibling = 0
                  and then not Is_Head (Snap'Old, C)
                  and then KM.Sum (Sub (H), Sub (C)) = Snap'Old.Sub (H)
                  and then Frame (Snap'Old, H, 0)
                  and then Origins (Snap'Old, 0, 0, H, C);
   --  Move the first child of a single tree onto a root list of its own

   procedure Split (A : Slot; Rest : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      Rest := Links (A).Sibling;
      if Rest /= 0 then
         pragma Assert (Node_In_Use (Snap, Rest));
         pragma Assert (Links (A).Last /= A);
         Links (Rest).Last := Links (A).Last;
         Meta (Rest).Parent := 0;
      end if;
      Links (A).Sibling := 0;
      Links (A).Last := A;
      Meta (A).Size := 1 + Size_Now (Links (A).Child);
      Sub (A) := KM.Add (KM.Sum (Sub_Now (Links (A).Child),
                                 KM.Empty_Multiset), Keys (A));

      --  Every node behind A moves to the list headed by Rest, one place
      --  further forward.
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) and then X /= A
               and then Before.Meta (X).Owner = A
            then Node_In_Use (Before, X)
                 and then Before.Meta (X).Pos >= 2
                 and then (Before.Meta (X).Pos = 2) = (X = Rest)));
      Meta :=
        [for X in 1 .. Capacity =>
           (if Chain_Pos (X) = 0 and then X /= A
               and then Meta (X).Owner = A
            then (Meta (X) with delta
                    Owner => Rest, Pos => Meta (X).Pos - 1)
            else Meta (X))];

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

   procedure Append (A : Slot; B : Tree) is
      Before : constant Snapshot := Snap with Ghost;
      Tail : Slot;
      M_B : KM.Multiset with Ghost;
      S_B : Extended_Index with Ghost;
   begin
      if B = 0 then
         Models.Lemma_Sum_Empty (Sub (A));
         return;
      end if;
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (Node_In_Use (Snap, B));
      Total_Bound (Snap, A, B, Capacity);
      Lemma_All_Below_Owner (A);
      Tail := Links (A).Last;
      pragma Assert (Node_In_Use (Snap, Tail));
      M_B := Sub (B);
      S_B := Meta (B).Size;
      Lemma_Shift_All (Before, A, M_B);

      --  Who can see what changes: the two lists are disjoint, a node of
      --  either one is linked from inside its own list or from nowhere, and
      --  every other node, and every head it names, belongs to neither.
      pragma Assert (Before.Meta (Tail).Owner = A);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) and then Before.Meta (X).Owner = B
            then Node_In_Use (Before, X)
                 and then X /= A and then X /= Tail
                 and then (if X /= B
                           then Before.Meta (X).Parent /= 0
                                and then Before.Links
                                           (Before.Meta (X).Parent).Sibling
                                         = X
                                and then Before.Meta
                                           (Before.Meta (X).Parent).Owner
                                         = B)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) and then Before.Meta (X).Owner /= A
               and then Before.Meta (X).Owner /= B
            then Node_In_Use (Before, X)
                 and then X /= A and then X /= Tail and then X /= B
                 and then (if Before.Meta (X).Owner /= 0
                           then Before.Links (Before.Meta (X).Owner).Last
                                  /= Tail
                                and then Before.Meta
                                           (Before.Links
                                              (Before.Meta (X).Owner).Last)
                                           .Owner
                                         = Before.Meta (X).Owner)));

      Links (Tail).Sibling := B;
      Links (A).Last := Links (B).Last;

      --  The nodes of A gain the whole of B behind them; the nodes of B
      --  change owner and move back by the length of A.
      Meta :=
        [for X in 1 .. Capacity =>
           (if Chain_Pos (X) = 0 and then Meta (X).Owner = A
            then (Meta (X) with delta Size => Meta (X).Size + S_B)
            elsif Chain_Pos (X) = 0 and then Meta (X).Owner = B
            then (Meta (X) with delta
                    Owner  => A,
                    Pos    => Meta (X).Pos + Before.Meta (Tail).Pos,
                    Parent => (if X = B then Tail else Meta (X).Parent))
            else Meta (X))];
      Sub :=
        [for X in 1 .. Capacity =>
           (if Chain_Pos (X) = 0 and then Before.Meta (X).Owner = A
            then KM.Sum (Sub (X), M_B)
            else Sub (X))];

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) and then Before.Meta (X).Owner = A
            then Node_In_Use (Before, X)));
      Models.Lemma_Sum_Empty_Left (M_B);
      pragma Assert (Before.Links (Tail).Sibling = 0);
      pragma Assert (Sub (B) = M_B);
      pragma Assert
        (Sub (Tail)
           = KM.Add (KM.Sum (Sub_Of (Before, Links (Tail).Child),
                             KM.Sum (KM.Empty_Multiset, M_B)),
                     Keys (Tail)));
      Models.Lemma_Sum_Congruent
        (KM.Sum (KM.Empty_Multiset, M_B), M_B,
         Sub_Of (Before, Links (Tail).Child));
      Models.Lemma_Sum_Symmetric
        (KM.Sum (KM.Empty_Multiset, M_B), Sub_Of (Before, Links (Tail).Child));
      Models.Lemma_Sum_Symmetric (M_B, Sub_Of (Before, Links (Tail).Child));
      pragma Assert
        (Sub (Tail)
           = KM.Add (KM.Sum (Sub_Of (Snap, Links (Tail).Child),
                             Sub_Of (Snap, Links (Tail).Sibling)),
                     Keys (Tail)));
      pragma Assert
        (Meta (Tail).Size
           = 1 + Size_Of_Node (Snap, Links (Tail).Child)
               + Size_Of_Node (Snap, Links (Tail).Sibling));
      pragma Assert (Links_Sound (Snap, Tail));
      pragma Assert (Node_In_Use (Snap, Tail));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (Node_In_Use (Snap, B));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = A
            then Node_In_Use (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = B
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Meta (X).Owner = A
                 and then Meta (X).Size = Before.Meta (X).Size
                 and then Meta (X).Pos
                          = Before.Meta (X).Pos + Before.Meta (Tail).Pos
                 and then Meta (X).Parent
                          = (if X = B then Tail else Before.Meta (X).Parent)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = B
            then Links_Sound (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = B
            then Top_Sound (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = B
            then Node_In_Use (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner /= A
               and then Before.Meta (X).Owner /= B
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Meta (X) = Before.Meta (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner /= A
               and then Before.Meta (X).Owner /= B
            then Links_Sound (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner = 0
            then Child_Sound (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner /= A
               and then Before.Meta (X).Owner /= B
               and then Before.Meta (X).Owner /= 0
            then Top_Sound (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then Before.Meta (X).Owner /= A
               and then Before.Meta (X).Owner /= B
            then Node_In_Use (Snap, X)));
      Total_Change (Before, Snap, A, B, Capacity);
   end Append;

   procedure Link_Equal (A, B : Slot; R : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
      Top, Loser : Slot;
      Kid : Tree;
      Below_Top, Below_Loser : KM.Multiset with Ghost;
   begin
      Lemma_Only_Owner (A);
      Lemma_Only_Owner (B);
      if Keys (A) <= Keys (B) then
         Top := A;
         Loser := B;
      else
         Top := B;
         Loser := A;
      end if;
      pragma Assert (Node_In_Use (Snap, Top));
      pragma Assert (Node_In_Use (Snap, Loser));
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
        (Links (Loser).Child /= Top and then Links (Loser).Child /= Loser);
      if Kid /= 0 then
         Meta (Kid).Parent := Loser;
      end if;
      --  The loser heads the winner's children. Its old children stay put;
      --  its new sibling is the winner's former child list.
      Links (Loser).Sibling := Kid;
      Meta (Loser) :=
        (Parent => Top,
         Size   => 1 + Size_Now (Links (Loser).Child) + Size_Now (Kid),
         Owner  => 0,
         Pos    => 0);
      Sub (Loser) :=
        KM.Add (KM.Sum (Sub_Now (Links (Loser).Child), Sub_Now (Kid)),
                Keys (Loser));
      Links (Top).Child := Loser;
      Links (Top).Rank := Links (Top).Rank + 1;
      Meta (Top).Size := 1 + Size_Now (Loser);
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
                 and then Meta (X) = Before.Meta (X)
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
        (Sub (Top) = KM.Sum (Before.Sub (Top), Before.Sub (Loser)));
      Models.Lemma_Sum_Symmetric (Before.Sub (A), Before.Sub (B));
      Total_Change (Before, Snap, A, B, Capacity);
   end Link_Equal;

   procedure Pop_Child (H : Slot; C : out Slot) is
      Before : constant Snapshot := Snap with Ghost;
      Next, Grand : Tree;
   begin
      Lemma_Only_Owner (H);
      pragma Assert (Node_In_Use (Snap, H));
      C := Links (H).Child;
      pragma Assert (Node_In_Use (Snap, C));
      Next := Links (C).Sibling;
      Grand := Links (C).Child;
      pragma Assert (if Next /= 0 then Node_In_Use (Snap, Next));
      Weight_Laws (Links (C).Rank, Links (H).Rank);
      if Next /= 0 then
         Weight_Laws (Links (Next).Rank, Links (C).Rank);
         Weight_Laws (Links (C).Rank - 1, Links (Next).Rank + 1);
      else
         Weight_Laws (0, Links (C).Rank);
      end if;
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) then Meta (X).Owner /= C));
      pragma Assert
        (Size_Now (Next) = Weight (Links (C).Rank) - 1);
      pragma Assert
        (if Next /= 0 then Links (Next).Rank + 1 = Links (C).Rank
         else Links (C).Rank = 0);

      Links (H).Child := Next;
      Links (H).Rank := Links (C).Rank;
      if Next /= 0 then
         Meta (Next).Parent := H;
      end if;
      Links (C).Sibling := 0;
      Links (C).Last := C;
      Meta (C) :=
        (Parent => 0,
         Size   => 1 + Size_Now (Grand),
         Owner  => C,
         Pos    => 1);
      Sub (C) := KM.Add (KM.Sum (Sub_Now (Grand), KM.Empty_Multiset),
                         Keys (C));
      Meta (H).Size := 1 + Size_Now (Next);
      Sub (H) := KM.Add (KM.Sum (Sub_Now (Next), KM.Empty_Multiset),
                         Keys (H));

      Pop_Model (KM.Empty_Multiset, Sub_Now (Next), Sub_Now (Grand),
                 Keys (H), Keys (C));
      pragma Assert
        (Sub_Of (Before, C)
           = KM.Add (KM.Sum (Sub_Now (Grand), Sub_Now (Next)), Keys (C)));
      pragma Assert (for all E of Sub_Now (Next) => Keys (H) <= E);
      pragma Assert (Node_In_Use (Snap, H));
      pragma Assert (Node_In_Use (Snap, C));
      pragma Assert (if Next /= 0 then Node_In_Use (Snap, Next));
      pragma Assert (if Grand /= 0 then Node_In_Use (Snap, Grand));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= H and then X /= C
               and then X /= Next
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Meta (X) = Before.Meta (X)
                 and then Node_In_Use (Snap, X)));
      pragma Assert (Nodes_Sound (Snap));
      Models.Lemma_Sum_Symmetric (Sub (H), Sub (C));
      Total_Change (Before, Snap, H, C, Capacity);
   end Pop_Child;

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
        (Child => 0, Sibling => 0, Last => Head, Rank => 0);
      Meta (Head) := (Parent => 0, Size => 1, Owner => Head, Pos => 1);
      Sub (Head) := KM.Add (KM.Empty_Multiset, K);
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);
      Total_Change (Before, Snap, Head, 0, Capacity);
      pragma Assert
        (Total (Snap, Capacity) + Long_Long_Integer (Free_Count)
           = Long_Long_Integer (Capacity));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X)
            then X /= Head and then Links (X) = Before.Links (X)
                 and then Node_In_Use (Before, X)));
      pragma Assert (Node_In_Use (Snap, Head));
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
      Lemma_Only_Owner (I);
      pragma Assert (Node_In_Use (Snap, I));
      pragma Assert (Meta (I).Size = 1);
      pragma Assert (Root_Size (Snap, I) = 1);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= I
            then Node_In_Use (Snap, X)
                 and then Links (X).Child /= I
                 and then Links (X).Sibling /= I
                 and then Meta (X).Parent /= I
                 and then Meta (X).Owner /= I
                 and then (if Meta (X).Owner /= 0
                           then Links (Meta (X).Owner).Last /= I)));
      Links (I) :=
        (Child => Free, Sibling => 0, Last => 0, Rank => 0);
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
      pragma Assert (Root_Size (Snap, I) = 0);
      pragma Assert
        (Total (Snap, Capacity) = Total (Before, Capacity) - 1);
      pragma Assert
        (Total (Snap, Capacity) + Long_Long_Integer (Free_Count)
           = Long_Long_Integer (Capacity));
      pragma Assert (Chain_Sound (Snap));
      pragma Assert (Nodes_Sound (Snap));
   end Deallocate;

   ---------------------
   -- The rank table  --
   ---------------------

   type Table_Type is array (Rank_Type) of Tree;

   function Table_Sound (S : Snapshot; T : Table_Type) return Boolean is
     (for all R in Rank_Type =>
        (if T (R) /= 0
         then Is_Head (S, T (R))
              and then S.Links (T (R)).Sibling = 0
              and then S.Links (T (R)).Rank = R))
     with Ghost;
   --  One single tree per rank. Two entries cannot be the same node, since
   --  its rank is where it sits.

   function In_Table (T : Table_Type; X : Tree) return Boolean is
     (for some R in Rank_Type => T (R) = X)
     with Ghost;

   function Table_Model (S : Snapshot; T : Table_Type; R : Integer)
     return KM.Multiset is
     (if R < 0 then KM.Empty_Multiset
      else KM.Sum (Table_Model (S, T, R - 1), Sub_Of (S, T (R))))
     with Ghost,
          Pre => R in -1 .. Max_Rank,
          Subprogram_Variant => (Decreases => R);

   procedure Lemma_Table
     (S1 : Snapshot; T1 : Table_Type;
      S2 : Snapshot; T2 : Table_Type;
      J : Rank_Type; R : Integer)
     with Ghost,
          Pre => R in -1 .. Max_Rank
                 and then (for all Q in 0 .. R =>
                             (if Q /= J
                              then Sub_Of (S1, T1 (Q)) = Sub_Of (S2, T2 (Q)))),
          Post => (if J <= R
                   then KM.Sum (Table_Model (S1, T1, R), Sub_Of (S2, T2 (J)))
                        = KM.Sum (Table_Model (S2, T2, R), Sub_Of (S1, T1 (J)))
                   else Table_Model (S1, T1, R) = Table_Model (S2, T2, R)),
          Subprogram_Variant => (Decreases => R);
   --  Tables whose entries agree except at J differ by what is there

   procedure Lemma_Table
     (S1 : Snapshot; T1 : Table_Type;
      S2 : Snapshot; T2 : Table_Type;
      J : Rank_Type; R : Integer) is
   begin
      if R >= 0 then
         Lemma_Table (S1, T1, S2, T2, J, R - 1);
      end if;
   end Lemma_Table;

   procedure Lemma_Table_Empty (S : Snapshot; T : Table_Type; R : Integer)
     with Ghost,
          Pre => R in -1 .. Max_Rank
                 and then (for all Q in 0 .. R => T (Q) = 0),
          Post => KM.Is_Empty (Table_Model (S, T, R)),
          Subprogram_Variant => (Decreases => R);

   procedure Lemma_Table_Empty (S : Snapshot; T : Table_Type; R : Integer) is
   begin
      if R >= 0 then
         Lemma_Table_Empty (S, T, R - 1);
      end if;
   end Lemma_Table_Empty;

   procedure Lemma_Table_Frame
     (S1 : Snapshot; T : Table_Type; S2 : Snapshot)
     with Ghost,
          Pre => (for all Q in Rank_Type =>
                    (if T (Q) /= 0
                     then S2.Sub (T (Q)) = S1.Sub (T (Q)))),
          Post => Table_Model (S1, T, Max_Rank)
                  = Table_Model (S2, T, Max_Rank);

   procedure Lemma_Table_Frame
     (S1 : Snapshot; T : Table_Type; S2 : Snapshot) is
   begin
      Lemma_Table (S1, T, S2, T, 0, Max_Rank);
      Models.Lemma_Sum_Symmetric
        (Table_Model (S1, T, Max_Rank), Sub_Of (S2, T (0)));
   end Lemma_Table_Frame;

   --  Link X with whatever the table holds at its rank, and so on upwards,
   --  until a free rank takes it.

   procedure Place (Table : in out Table_Type; X : Slot)
     with Pre => Valid and then Is_Head (Snap, X)
                 and then Links (X).Sibling = 0
                 and then Table_Sound (Snap, Table)
                 and then not In_Table (Table, X),
          Post => Valid and then Stable (Snap'Old)
                  and then Table_Sound (Snap, Table)
                  and then Table_Model (Snap, Table, Max_Rank)
                           = KM.Sum (Table_Model (Snap'Old, Table'Old,
                                                  Max_Rank),
                                     Snap'Old.Sub (X))
                  and then (for all R in Rank_Type =>
                              (if Table (R) /= 0
                               then Table (R) = X
                                    or else In_Table (Table'Old, Table (R))))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= X
                                  and then not In_Table (Table'Old, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y) and then not In_Table (Table, Y)
                               then Is_Head (Snap'Old, Y) and then Y /= X
                                    and then not In_Table (Table'Old, Y)));

   procedure Place (Table : in out Table_Type; X : Slot) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      Cur : Slot := X;
      Linked : Slot;
      Other : Slot;
      D : Rank_Type := Links (X).Rank;
      Step_State : Snapshot with Ghost;
      Step_Table : Table_Type with Ghost;
      M_Cur, M_Other, M_Mid : KM.Multiset with Ghost;
   begin
      while Table (D) /= 0 loop
         pragma Loop_Invariant (Valid and then Stable (Entry_State));
         pragma Loop_Invariant
           (Is_Head (Snap, Cur) and then Links (Cur).Sibling = 0
            and then Links (Cur).Rank = D
            and then Table_Sound (Snap, Table)
            and then not In_Table (Table, Cur));
         pragma Loop_Invariant
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (Cur))
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Entry_State.Sub (X)));
         pragma Loop_Invariant
           (Cur = X or else In_Table (Entry_Table, Cur));
         pragma Loop_Invariant
           (for all R in Rank_Type =>
              (if Table (R) /= 0 then In_Table (Entry_Table, Table (R))));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= X
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then not In_Table (Table, Y)
                  and then Y /= Cur
               then Is_Head (Entry_State, Y) and then Y /= X
                    and then not In_Table (Entry_Table, Y)));
         pragma Loop_Variant (Increases => D);

         Other := Table (D);
         Step_State := Snap;
         Step_Table := Table;
         M_Cur := Sub (Cur);
         M_Other := Sub (Other);
         Table (D) := 0;
         Lemma_Table (Step_State, Step_Table, Step_State, Table, D, Max_Rank);
         M_Mid := Table_Model (Step_State, Table, Max_Rank);
         Models.Lemma_Sum_Empty
           (Table_Model (Step_State, Step_Table, Max_Rank));
         pragma Assert
           (Table_Model (Step_State, Step_Table, Max_Rank)
              = KM.Sum (M_Mid, M_Other));
         Total_Bound (Snap, Cur, Other, Capacity);
         Link_Equal (Cur, Other, Linked);
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0
               then Table (Q) /= Cur and then Table (Q) /= Other
                    and then Is_Head (Step_State, Table (Q))));
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0 then Unchanged (Step_State, Table (Q))));
         pragma Assert (Table_Sound (Snap, Table));
         Lemma_Table_Frame (Step_State, Table, Snap);
         pragma Assert (Table_Model (Snap, Table, Max_Rank) = M_Mid);
         pragma Assert (Sub (Linked) = KM.Sum (M_Cur, M_Other));
         Models.Lemma_Sum_Assoc (M_Mid, M_Cur, M_Other);
         Sum_Swap (M_Mid, M_Cur, M_Other);
         pragma Assert
           (KM.Sum (M_Mid, Sub (Linked))
              = KM.Sum (KM.Sum (M_Mid, M_Other), M_Cur));
         pragma Assert
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (Linked))
              = KM.Sum (Table_Model (Step_State, Step_Table, Max_Rank),
                        M_Cur));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= X
                  and then not In_Table (Entry_Table, Y)
               then Y /= Cur and then Y /= Other
                    and then Unchanged (Step_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= X
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then not In_Table (Table, Y)
                  and then Y /= Linked
               then Is_Head (Step_State, Y) and then Y /= Cur
                    and then Y /= Other
                    and then not In_Table (Step_Table, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then not In_Table (Table, Y)
                  and then Y /= Linked
               then Is_Head (Entry_State, Y) and then Y /= X
                    and then not In_Table (Entry_Table, Y)));
         Cur := Linked;
         D := Links (Cur).Rank;
      end loop;
      Step_State := Snap;
      Step_Table := Table;
      Table (D) := Cur;
      Lemma_Table (Step_State, Step_Table, Snap, Table, D, Max_Rank);
      Models.Lemma_Sum_Empty (Table_Model (Snap, Table, Max_Rank));
      pragma Assert (In_Table (Table, Cur));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then not In_Table (Table, Y)
            then Y /= Cur and then not In_Table (Step_Table, Y)));
   end Place;

   ---------------
   -- Interface --
   ---------------

   function Size_Of (T : Tree) return Extended_Index is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Weight);
      N : Extended_Index := 0;
      X : Tree := T;
   begin
      while X /= 0 loop
         pragma Loop_Invariant
           (In_Use (Snap, X) and then Meta (X).Owner = T
            and then N + Meta (X).Size = Size_Now (T));
         pragma Loop_Variant (Decreases => Size_Now (X));
         pragma Assert (Node_In_Use (Snap, X));
         N := N + 2 ** Links (X).Rank;
         X := Links (X).Sibling;
      end loop;
      return N;
   end Size_Of;

   function Peek_Min (T : Tree) return Key_Type is
   begin
      pragma Assert (Node_In_Use (Snap, T));
      return Keys (T);
   end Peek_Min;

   function Min_Of (T : Tree) return Key_Type is (Peek_Min (T));

   procedure Meld (T : in out Tree; U : in out Tree) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      if T = 0 then
         T := U;
         U := 0;
         Models.Lemma_Sum_Empty_Left (Sub_Now (T));
         return;
      end if;
      if U = 0 then
         Models.Lemma_Sum_Empty (Sub_Now (T));
         return;
      end if;
      if Keys (U) < Keys (T) then
         Append (U, T);
         Models.Lemma_Sum_Symmetric (Sub_Of (Before, U), Sub_Of (Before, T));
         T := U;
      else
         Append (T, U);
      end if;
      U := 0;
   end Meld;

   procedure Insert (T : in out Tree; K : Key_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Old_T : constant Tree := T with Ghost;
      Node : Slot;
      Mid : Snapshot with Ghost;
   begin
      Allocate (Node, K);
      Mid := Snap;
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Head (Before, U)
            then Same (Mid, Before, U) and then U /= Node
                 and then Keys (U) = Before.Keys (U)));
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);
      if T = 0 then
         T := Node;
         Models.Lemma_Sum_Empty_Left (Sub (Node));
         return;
      end if;
      pragma Assert (Node_In_Use (Snap, T));
      if K < Keys (T) then
         Append (Node, T);
         Models.Lemma_Sum_Symmetric
           (KM.Add (KM.Empty_Multiset, K), Sub_Of (Before, Old_T));
         T := Node;
      else
         Append (T, Node);
      end if;
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Head (Before, U) and then U /= Old_T
            then Same (Mid, Before, U) and then Unchanged (Mid, U)
                 and then Keys (U) = Before.Keys (U)));
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Root (Before, U) and then U /= Old_T
            then Is_Root (Snap, U)));
      Models.Lemma_Sum_Empty (Model (Before, Old_T));
      Models.Lemma_Sum_Add (Model (Before, Old_T), KM.Empty_Multiset, K);
   end Insert;

   --  The three phases of an extraction. Each is stated against the table
   --  alone: which heads it may consume, which it leaves as they were, and
   --  what the table holds afterwards.

   procedure Scatter_Children (H : Slot; Table : in out Table_Type)
     with Pre => Valid and then Is_Head (Snap, H)
                 and then Links (H).Sibling = 0
                 and then Table_Sound (Snap, Table)
                 and then not In_Table (Table, H),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Head (Snap, H)
                  and then Links (H).Sibling = 0
                  and then Links (H).Child = 0
                  and then Table_Sound (Snap, Table)
                  and then not In_Table (Table, H)
                  and then KM.Sum (Table_Model (Snap, Table, Max_Rank),
                                   Sub (H))
                           = KM.Sum (Table_Model (Snap'Old, Table'Old,
                                                  Max_Rank),
                                     Snap'Old.Sub (H))
                  and then (for all R in Rank_Type =>
                              (if Table (R) /= 0
                               then In_Table (Table'Old, Table (R))
                                    or else not Is_Head (Snap'Old, Table (R))))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= H
                                  and then not In_Table (Table'Old, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y) and then Y /= H
                                  and then not In_Table (Table, Y)
                               then Is_Head (Snap'Old, Y)
                                    and then not In_Table (Table'Old, Y)));
   --  Move every child of the single tree H into the table

   procedure Scatter_Children (H : Slot; Table : in out Table_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      C : Slot;
      M_Table, M_H, M_C : KM.Multiset with Ghost;
      S0, S1 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
   begin
      Models.Lemma_Sum_Empty (Sub (H));
      while Links (H).Child /= 0 loop
         pragma Loop_Invariant
           (Valid and then Stable (Entry_State)
            and then Is_Head (Snap, H) and then Links (H).Sibling = 0
            and then Table_Sound (Snap, Table)
            and then not In_Table (Table, H));
         pragma Loop_Invariant
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (H))
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Entry_State.Sub (H)));
         pragma Loop_Invariant
           (for all R in Rank_Type =>
              (if Table (R) /= 0
               then In_Table (Entry_Table, Table (R))
                    or else not Is_Head (Entry_State, Table (R))));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Table (Table, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Table (Entry_Table, Y)));
         pragma Loop_Variant (Decreases => Links (H).Rank);

         S0 := Snap;
         T0 := Table;
         M_Table := Table_Model (Snap, Table, Max_Rank);
         M_H := Sub (H);
         Pop_Child (H, C);
         M_C := Sub (C);
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0
               then Table (Q) /= H and then Unchanged (S0, Table (Q))));
         pragma Assert (Table_Sound (Snap, Table));
         pragma Assert (not In_Table (Table, C));
         Lemma_Table_Frame (S0, Table, Snap);
         S1 := Snap;
         Place (Table, C);
         pragma Assert (Unchanged (S1, H));
         pragma Assert
           (Table_Model (Snap, Table, Max_Rank) = KM.Sum (M_Table, M_C));
         pragma Assert (M_H = KM.Sum (Sub (H), M_C));
         Models.Lemma_Sum_Assoc (M_Table, M_C, Sub (H));
         Models.Lemma_Sum_Symmetric (M_C, Sub (H));
         pragma Assert
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (H))
              = KM.Sum (M_Table, M_H));

         --  The invariant again, as it stands at the end of the step, so
         --  that it is known on leaving the loop as well.
         pragma Assert
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (H))
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Entry_State.Sub (H)));
         pragma Assert
           (for all R in Rank_Type =>
              (if Table (R) /= 0
               then Table (R) = C or else In_Table (T0, Table (R))));
         pragma Assert
           (for all R in Rank_Type =>
              (if Table (R) /= 0
               then In_Table (Entry_Table, Table (R))
                    or else not Is_Head (Entry_State, Table (R))));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Table (Entry_Table, Y)
               then Same (S0, Entry_State, Y)
                    and then Y /= C and then not In_Table (T0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Table (Entry_Table, Y)
               then Same (S1, S0, Y) and then Same (Snap, S1, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Table (Table, Y)
               then Is_Head (S1, Y) and then Y /= C
                    and then not In_Table (T0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Table (Table, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Table (Entry_Table, Y)));
      end loop;
   end Scatter_Children;

   procedure Scatter_List (Rest : Tree; Table : in out Table_Type)
     with Pre => Valid
                 and then (Rest = 0
                           or else (Is_Head (Snap, Rest)
                                    and then not In_Table (Table, Rest)))
                 and then Table_Sound (Snap, Table),
          Post => Valid and then Stable (Snap'Old)
                  and then Table_Sound (Snap, Table)
                  and then Table_Model (Snap, Table, Max_Rank)
                           = KM.Sum (Table_Model (Snap'Old, Table'Old,
                                                  Max_Rank),
                                     Sub_Of (Snap'Old, Rest))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= Rest
                                  and then not In_Table (Table'Old, Y)
                               then Unchanged (Snap'Old, Y)
                                    and then not In_Table (Table, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y)
                                  and then not In_Table (Table, Y)
                               then Is_Head (Snap'Old, Y) and then Y /= Rest
                                    and then not In_Table (Table'Old, Y)));
   --  Move every tree of the list headed by Rest into the table

   procedure Scatter_List (Rest : Tree; Table : in out Table_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      Cur : Tree := Rest;
      Next : Tree;
      M_Table, M_Cur, M_Next : KM.Multiset with Ghost;
      S0, S1 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
   begin
      Models.Lemma_Sum_Empty (Table_Model (Snap, Table, Max_Rank));
      while Cur /= 0 loop
         pragma Loop_Invariant
           (Valid and then Stable (Entry_State)
            and then Is_Head (Snap, Cur)
            and then Table_Sound (Snap, Table)
            and then not In_Table (Table, Cur));
         pragma Loop_Invariant
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub (Cur))
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Sub_Of (Entry_State, Rest)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)
                    and then Y /= Cur
                    and then not In_Table (Table, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Cur
                  and then not In_Table (Table, Y)
               then Is_Head (Entry_State, Y) and then Y /= Rest
                    and then not In_Table (Entry_Table, Y)));
         pragma Loop_Variant (Decreases => Size_Now (Cur));

         S0 := Snap;
         T0 := Table;
         M_Table := Table_Model (Snap, Table, Max_Rank);
         Split (Cur, Next);
         M_Cur := Sub (Cur);
         M_Next := Sub_Now (Next);
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0
               then Table (Q) /= Cur and then Unchanged (S0, Table (Q))));
         pragma Assert (Table_Sound (Snap, Table));
         pragma Assert (if Next /= 0 then not In_Table (Table, Next));
         Lemma_Table_Frame (S0, Table, Snap);
         S1 := Snap;
         Place (Table, Cur);
         pragma Assert (if Next /= 0 then Unchanged (S1, Next));
         pragma Assert (Sub_Now (Next) = M_Next);
         pragma Assert
           (Table_Model (Snap, Table, Max_Rank) = KM.Sum (M_Table, M_Cur));
         Models.Lemma_Sum_Assoc (M_Table, M_Cur, M_Next);

         --  The invariant again, for the list behind Cur, so that it is
         --  known on leaving the loop as well.
         pragma Assert
           (KM.Sum (Table_Model (Snap, Table, Max_Rank), Sub_Now (Next))
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Sub_Of (Entry_State, Rest)));
         pragma Assert
           (for all R in Rank_Type =>
              (if Table (R) /= 0
               then Table (R) = Cur or else In_Table (T0, Table (R))));
         pragma Assert (if Next /= 0 then not Is_Head (S0, Next));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Table (Entry_Table, Y)
               then Same (S0, Entry_State, Y)
                    and then Y /= Cur and then Y /= Next
                    and then not In_Table (T0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Table (Entry_Table, Y)
               then not In_Table (Table, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Table (Entry_Table, Y)
               then Same (S1, S0, Y) and then Same (Snap, S1, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Table (Entry_Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Next
                  and then not In_Table (Table, Y)
               then Is_Head (S1, Y) and then Y /= Cur
                    and then not In_Table (T0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Next
                  and then not In_Table (Table, Y)
               then Is_Head (Entry_State, Y) and then Y /= Rest
                    and then not In_Table (Entry_Table, Y)));
         Cur := Next;
      end loop;
      Models.Lemma_Sum_Empty (Table_Model (Snap, Table, Max_Rank));
   end Scatter_List;

   procedure Gather (Table : Table_Type; T : out Tree)
     with Pre => Valid and then Table_Sound (Snap, Table),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, T)
                  and then Sub_Of (Snap, T)
                           = Table_Model (Snap'Old, Table, Max_Rank)
                  and then (if T /= 0 then In_Table (Table, T))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y)
                                  and then not In_Table (Table, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y) and then Y /= T
                               then Is_Head (Snap'Old, Y)
                                    and then not In_Table (Table, Y)));
   --  Link the trees of the table into one list, the smallest root first

   procedure Gather (Table : Table_Type; T : out Tree) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Left : Table_Type := Table;
      Best : Tree := 0;
      L : Tree := 0;
      Goal : KM.Multiset with Ghost;
      M_Table, M_L, M_Entry : KM.Multiset with Ghost;
      S0 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
   begin
      for R in Rank_Type loop
         if Left (R) /= 0
           and then (Best = 0 or else Keys (Left (R)) < Keys (Best))
         then
            Best := Left (R);
         end if;
         pragma Loop_Invariant
           (if Best = 0 then (for all Q in 0 .. R => Left (Q) = 0)
            else Best in 1 .. Capacity
                 and then Left (Links (Best).Rank) = Best
                 and then (for all Q in 0 .. R =>
                             (if Left (Q) /= 0
                              then Keys (Best) <= Keys (Left (Q)))));
      end loop;
      Goal := Table_Model (Snap, Table, Max_Rank);

      if Best = 0 then
         T := 0;
         Lemma_Table_Empty (Snap, Table, Max_Rank);
         return;
      end if;

      pragma Assert (Node_In_Use (Snap, Best));
      T0 := Left;
      Left (Links (Best).Rank) := 0;
      Lemma_Table (Snap, T0, Snap, Left, Links (Best).Rank, Max_Rank);
      Models.Lemma_Sum_Empty (Goal);
      Models.Lemma_Sum_Empty (Table_Model (Snap, Left, Max_Rank));
      pragma Assert
        (KM.Sum (KM.Sum (Table_Model (Snap, Left, Max_Rank), Sub_Now (L)),
                 Sub (Best))
           = Goal);
      for R in Rank_Type loop
         if Left (R) /= 0 then
            S0 := Snap;
            T0 := Left;
            M_Table := Table_Model (Snap, Left, Max_Rank);
            M_L := Sub_Now (L);
            M_Entry := Sub (Left (R));
            pragma Assert (Node_In_Use (Snap, Left (R)));
            pragma Assert (for all E of M_Entry => Keys (Left (R)) <= E);
            Append (Left (R), L);
            L := Left (R);
            Left (R) := 0;
            pragma Assert
              (for all Q in Rank_Type =>
                 (if Left (Q) /= 0 then Unchanged (S0, Left (Q))));
            pragma Assert (Unchanged (S0, Best));
            Lemma_Table (S0, T0, Snap, Left, R, Max_Rank);
            Models.Lemma_Sum_Empty (M_Table);
            pragma Assert
              (M_Table = KM.Sum (Table_Model (Snap, Left, Max_Rank), M_Entry));
            pragma Assert (Sub (L) = KM.Sum (M_Entry, M_L));
            Models.Lemma_Sum_Assoc
              (Table_Model (Snap, Left, Max_Rank), M_Entry, M_L);
            Models.Lemma_Sum_Congruent
              (KM.Sum (Table_Model (Snap, Left, Max_Rank), Sub (L)),
               KM.Sum (M_Table, M_L), Sub (Best));
            pragma Assert
              (for all Y in 1 .. Capacity =>
                 (if Is_Head (Entry_State, Y) and then not In_Table (Table, Y)
                  then Same (S0, Entry_State, Y) and then Same (Snap, S0, Y)));
            pragma Assert
              (for all Y in 1 .. Capacity =>
                 (if Head_Now (Y) and then Y /= Best and then Y /= L
                     and then not In_Table (Left, Y)
                  then Is_Head (S0, Y) and then not In_Table (T0, Y)));
         end if;
         pragma Loop_Invariant (Valid and then Stable (Entry_State));
         pragma Loop_Invariant
           (Table_Sound (Snap, Left)
            and then Is_Head (Snap, Best)
            and then Links (Best).Sibling = 0
            and then not In_Table (Left, Best)
            and then (for all Q in 0 .. R => Left (Q) = 0)
            and then (for all Q in Rank_Type =>
                        (if Left (Q) /= 0 then Left (Q) = Table (Q)))
            and then (L = 0
                      or else (Is_Head (Snap, L) and then L /= Best
                               and then not In_Table (Left, L)
                               and then In_Table (Table, L))));
         pragma Loop_Invariant
           (KM.Sum (KM.Sum (Table_Model (Snap, Left, Max_Rank), Sub_Now (L)),
                    Sub (Best))
              = Goal);
         pragma Loop_Invariant
           (for all Q in Rank_Type =>
              (if Left (Q) /= 0 then Keys (Best) <= Keys (Left (Q))));
         pragma Loop_Invariant
           (for all E of Sub_Now (L) => Keys (Best) <= E);
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then not In_Table (Table, Y)
               then Unchanged (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Best and then Y /= L
                  and then not In_Table (Left, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Table (Table, Y)));
      end loop;
      Lemma_Table_Empty (Snap, Left, Max_Rank);
      Models.Lemma_Sum_Empty_Left (Sub_Now (L));
      pragma Assert
        (KM.Sum (Table_Model (Snap, Left, Max_Rank), Sub_Now (L))
           = Sub_Now (L));
      Models.Lemma_Sum_Congruent
        (KM.Sum (Table_Model (Snap, Left, Max_Rank), Sub_Now (L)),
         Sub_Now (L), Sub (Best));
      Models.Lemma_Sum_Symmetric (Sub_Now (L), Sub (Best));
      pragma Assert (KM.Sum (Sub (Best), Sub_Now (L)) = Goal);
      pragma Assert (Node_In_Use (Snap, Best));
      pragma Assert (for all E of Sub (Best) => Keys (Best) <= E);
      S0 := Snap;
      Append (Best, L);
      T := Best;
      pragma Assert (Sub (T) = Goal);
      pragma Assert (Is_Minimum (Snap, T, Keys (T)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then not In_Table (Table, Y)
            then Same (S0, Entry_State, Y) and then Y /= L and then Y /= Best
                 and then Same (Snap, S0, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S0, Y) and then Y /= L and then Y /= Best));
   end Gather;

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      H : constant Slot := T;
      Rest : Tree;
      Table : Table_Type := [others => 0];
      M_Table, M_Rest : KM.Multiset with Ghost;
      S1, S2, S3, S4 : Snapshot with Ghost;
      T2, T4 : Table_Type with Ghost;
   begin
      K := Keys (T);

      --  Detach the minimum from its list, scatter its children and then
      --  the rest of the list into the table, and relink the table.
      Split (H, Rest);
      S1 := Snap;
      Lemma_Table_Empty (Snap, Table, Max_Rank);
      Models.Lemma_Sum_Empty_Left (Sub (H));
      pragma Assert (for all R in Rank_Type => Table (R) = 0);
      Scatter_Children (H, Table);
      S2 := Snap;
      T2 := Table;

      pragma Assert (Node_In_Use (Snap, H));
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);
      pragma Assert (Sub (H) = KM.Add (KM.Empty_Multiset, K));
      M_Table := Table_Model (Snap, Table, Max_Rank);
      M_Rest := Sub_Of (S1, Rest);
      pragma Assert (if Rest /= 0 then Unchanged (S1, Rest));
      pragma Assert (if Rest /= 0 then not In_Table (Table, Rest));
      pragma Assert (KM.Sum (M_Table, Sub (H)) = S1.Sub (H));
      Models.Lemma_Sum_Add (M_Table, KM.Empty_Multiset, K);
      Models.Lemma_Sum_Empty (M_Table);
      pragma Assert (KM.Sum (M_Table, Sub (H)) = KM.Add (M_Table, K));
      Models.Lemma_Sum_Add_Left (M_Table, M_Rest, K);
      pragma Assert
        (Entry_State.Sub (H) = KM.Add (KM.Sum (M_Table, M_Rest), K));

      Total_Bound_One (Snap, H, Capacity);
      Deallocate (H);
      S3 := Snap;
      pragma Assert
        (for all Q in Rank_Type =>
           (if Table (Q) /= 0 then Same (S3, S2, Table (Q))));
      pragma Assert (Table_Sound (Snap, Table));
      Lemma_Table_Frame (S2, Table, Snap);
      pragma Assert (if Rest /= 0 then Same (S3, S2, Rest));

      Scatter_List (Rest, Table);
      S4 := Snap;
      T4 := Table;
      pragma Assert
        (Table_Model (Snap, Table, Max_Rank) = KM.Sum (M_Table, M_Rest));
      Gather (Table, T);
      pragma Assert (Entry_State.Sub (H) = KM.Add (Sub_Now (T), K));

      --  Every other head the arena had comes through all four steps as it
      --  was, and every head there is now is one of those or the result.
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S1, Entry_State, Y) and then Y /= Rest));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S2, S1, Y) and then not In_Table (T2, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S3, S2, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S4, S3, Y) and then not In_Table (T4, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Unchanged (S4, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Unchanged (Entry_State, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S4, Y) and then not In_Table (T4, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S3, Y) and then Y /= Rest
                 and then not In_Table (T2, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S2, Y) and then Y /= H));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S1, Y) and then Is_Head (Entry_State, Y)));

      --  The size follows from the arena accounting: one node went back to
      --  the free list, and the heap's head is the only head that changed.
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Head (Entry_State, X) and then X /= H
            then Root_Size (Entry_State, X) = Root_Size (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Head_Now (X) and then X /= T
            then Root_Size (Entry_State, X) = Root_Size (Snap, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not Is_Head (Entry_State, X) and then not Head_Now (X)
            then Root_Size (Entry_State, X) = 0
                 and then Root_Size (Snap, X) = 0));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= H and then X /= T
            then Root_Size (Entry_State, X) = Root_Size (Snap, X)));
      Total_Change (Entry_State, Snap, H, T, Capacity);
   end Extract_Min;

   -------------
   -- Clear   --
   -------------

   procedure Clear is
   begin
      Chain_Pos := [for J in 1 .. Capacity => J];
      Chain_At := [for J in 1 .. Capacity => J];
      Sub := [for J in 1 .. Capacity => KM.Empty_Multiset];
      Meta := [for J in 1 .. Capacity => (others => <>)];

      for I in 1 .. Capacity loop
         Links (I) :=
           (Child => (if I = 1 then 0 else I - 1),
            Sibling => 0, Last => 0, Rank => 0);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Links (J) =
                (Child   => (if J = 1 then 0 else J - 1),
                 Sibling => 0,
                 Last    => 0,
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

end Heaps.Fibonacci;
