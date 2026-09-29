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

package body Heaps.Rank_Pairing with SPARK_Mode is

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

   --  What an extraction has gathered so far: the rank table, and the list
   --  of trees already linked in this pass, whose head is its minimum

   function In_Acc (T : Table_Type; O : Tree; X : Slot) return Boolean is
     (In_Table (T, X) or else X = O)
     with Ghost;

   function Acc_Sound (S : Snapshot; T : Table_Type; O : Tree)
     return Boolean is
     (Table_Sound (S, T)
      and then (O = 0
                or else (Is_Head (S, O)
                         and then Is_Minimum (S, O, S.Keys (O))
                         and then not In_Table (T, O))))
     with Ghost;

   function Acc_Model (S : Snapshot; T : Table_Type; O : Tree)
     return KM.Multiset is
     (KM.Sum (Table_Model (S, T, Max_Rank), Sub_Of (S, O)))
     with Ghost;

   procedure Lemma_Acc_Frame
     (S1 : Snapshot; T : Table_Type; O : Tree; S2 : Snapshot)
     with Ghost,
          Pre => (for all Q in Rank_Type =>
                    (if T (Q) /= 0
                     then S2.Sub (T (Q)) = S1.Sub (T (Q))))
                 and then (if O /= 0 then S2.Sub (O) = S1.Sub (O)),
          Post => Acc_Model (S1, T, O) = Acc_Model (S2, T, O);

   procedure Lemma_Acc_Frame
     (S1 : Snapshot; T : Table_Type; O : Tree; S2 : Snapshot) is
      pragma Unreferenced (O);
   begin
      Lemma_Table_Frame (S1, T, S2);
   end Lemma_Acc_Frame;

   procedure Place_Model (A, O, X, B : KM.Multiset)
     with Ghost,
          Post => KM.Sum (A, KM.Sum (O, KM.Sum (X, B)))
                    = KM.Sum (KM.Sum (KM.Sum (A, B), O), X);
   procedure Place_Model (A, O, X, B : KM.Multiset) is null;
   --  Moving the entry B out of the table A and linking it with X onto the
   --  list O

   procedure Gather_Model (A, E, T : KM.Multiset)
     with Ghost,
          Post => KM.Sum (A, KM.Sum (T, E)) = KM.Sum (KM.Sum (A, E), T);
   procedure Gather_Model (A, E, T : KM.Multiset) is null;
   --  Moving the entry E out of the table A onto the list T

   --  Concatenate the lists of T and X, the smaller head in front, so that
   --  the head of the result is its minimum

   procedure Merge_Root (T : in out Tree; X : Slot)
     with Pre => Valid
                 and then (T = 0
                           or else (Is_Head (Snap, T)
                                    and then Is_Minimum (Snap, T, Keys (T))))
                 and then Is_Head (Snap, X)
                 and then Is_Minimum (Snap, X, Keys (X))
                 and then T /= X,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Head (Snap, T)
                  and then Is_Minimum (Snap, T, Keys (T))
                  and then (T = T'Old or else T = X)
                  and then Sub (T)
                           = KM.Sum (Sub_Of (Snap'Old, T'Old),
                                     Snap'Old.Sub (X))
                  and then Frame (Snap'Old, T'Old, X)
                  and then Origins (Snap'Old, T'Old, X, T, 0);

   procedure Merge_Root (T : in out Tree; X : Slot) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      if T = 0 then
         T := X;
         Models.Lemma_Sum_Empty_Left (Sub (X));
         return;
      end if;
      if Keys (X) < Keys (T) then
         Append (X, T);
         Models.Lemma_Sum_Symmetric (Before.Sub (X), Sub_Of (Before, T));
         T := X;
      else
         Append (T, X);
      end if;
   end Merge_Root;

   --  The one-pass step: X takes its rank's entry if that is free, and is
   --  otherwise linked with the entry, the winner going onto the output list
   --  and the entry leaving the table. Nothing is linked twice in one pass.

   procedure Place
     (Table : in out Table_Type; Out_List : in out Tree; X : Slot)
     with Pre => Valid and then Is_Head (Snap, X)
                 and then Links (X).Sibling = 0
                 and then Acc_Sound (Snap, Table, Out_List)
                 and then not In_Acc (Table, Out_List, X),
          Post => Valid and then Stable (Snap'Old)
                  and then Acc_Sound (Snap, Table, Out_List)
                  and then Acc_Model (Snap, Table, Out_List)
                           = KM.Sum (Acc_Model (Snap'Old, Table'Old,
                                                Out_List'Old),
                                     Snap'Old.Sub (X))
                  and then (for all Y in 1 .. Capacity =>
                              (if In_Acc (Table, Out_List, Y)
                               then Y = X
                                    or else In_Acc (Table'Old, Out_List'Old,
                                                    Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= X
                                  and then not In_Acc (Table'Old,
                                                       Out_List'Old, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y)
                                  and then not In_Acc (Table, Out_List, Y)
                               then Is_Head (Snap'Old, Y) and then Y /= X
                                    and then not In_Acc (Table'Old,
                                                         Out_List'Old, Y)));

   procedure Place
     (Table : in out Table_Type; Out_List : in out Tree; X : Slot)
   is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      Entry_Out : constant Tree := Out_List with Ghost;
      D : constant Rank_Type := Links (X).Rank;
      Other : Slot;
      Linked : Slot;
      M_X, M_Other, M_Mid, M_Out : KM.Multiset with Ghost;
      S1 : Snapshot with Ghost;
   begin
      if Table (D) = 0 then
         Table (D) := X;
         Lemma_Table (Entry_State, Entry_Table, Snap, Table, D, Max_Rank);
         Models.Lemma_Sum_Empty (Table_Model (Snap, Table, Max_Rank));
         pragma Assert
           (Table_Model (Snap, Table, Max_Rank)
              = KM.Sum (Table_Model (Entry_State, Entry_Table, Max_Rank),
                        Sub (X)));
         Sum_Swap (Table_Model (Entry_State, Entry_Table, Max_Rank),
                   Sub (X), Sub_Of (Snap, Out_List));
         pragma Assert (In_Table (Table, X));
         return;
      end if;

      Other := Table (D);
      M_X := Sub (X);
      M_Other := Sub (Other);
      M_Out := Sub_Of (Snap, Out_List);
      Table (D) := 0;
      Lemma_Table (Entry_State, Entry_Table, Entry_State, Table, D, Max_Rank);
      M_Mid := Table_Model (Entry_State, Table, Max_Rank);
      Models.Lemma_Sum_Empty
        (Table_Model (Entry_State, Entry_Table, Max_Rank));
      pragma Assert
        (Table_Model (Entry_State, Entry_Table, Max_Rank)
           = KM.Sum (M_Mid, M_Other));
      pragma Assert (Out_List /= X and then Out_List /= Other);
      Total_Bound (Snap, X, Other, Capacity);
      Link_Equal (X, Other, Linked);
      pragma Assert
        (for all Q in Rank_Type =>
           (if Table (Q) /= 0
            then Table (Q) /= X and then Table (Q) /= Other
                 and then Is_Head (Entry_State, Table (Q))
                 and then Unchanged (Entry_State, Table (Q))));
      pragma Assert (Table_Sound (Snap, Table));
      Lemma_Table_Frame (Entry_State, Table, Snap);
      pragma Assert (Table_Model (Snap, Table, Max_Rank) = M_Mid);
      pragma Assert
        (if Out_List /= 0 then Unchanged (Entry_State, Out_List));
      pragma Assert (Sub_Of (Snap, Out_List) = M_Out);
      pragma Assert (Node_In_Use (Snap, Linked));
      pragma Assert (Is_Minimum (Snap, Linked, Keys (Linked)));
      pragma Assert (Sub (Linked) = KM.Sum (M_X, M_Other));
      pragma Assert (not In_Table (Table, Linked));
      S1 := Snap;
      Merge_Root (Out_List, Linked);
      pragma Assert
        (for all Q in Rank_Type =>
           (if Table (Q) /= 0
            then Table (Q) /= Out_List and then Unchanged (S1, Table (Q))));
      pragma Assert (Table_Sound (Snap, Table));
      Lemma_Table_Frame (S1, Table, Snap);
      pragma Assert (Table_Model (Snap, Table, Max_Rank) = M_Mid);
      pragma Assert
        (Sub_Of (Snap, Out_List) = KM.Sum (M_Out, KM.Sum (M_X, M_Other)));
      Place_Model (M_Mid, M_Out, M_X, M_Other);
      pragma Assert
        (Acc_Model (Snap, Table, Out_List)
           = KM.Sum (Acc_Model (Entry_State, Entry_Table, Entry_Out), M_X));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if In_Acc (Table, Out_List, Y)
            then Y = X or else In_Acc (Entry_Table, Entry_Out, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= X
               and then not In_Acc (Entry_Table, Entry_Out, Y)
            then Y /= Other and then Unchanged (Entry_State, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= X
               and then not In_Acc (Entry_Table, Entry_Out, Y)
            then Same (S1, Entry_State, Y) and then Same (Snap, S1, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then not In_Acc (Table, Out_List, Y)
            then Is_Head (S1, Y) and then Y /= Linked
                 and then Y /= Entry_Out));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then not In_Acc (Table, Out_List, Y)
            then Is_Head (Entry_State, Y) and then Y /= X
                 and then Y /= Other
                 and then not In_Acc (Entry_Table, Entry_Out, Y)));
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

   --  The three phases of an extraction. Each is stated against what the
   --  pass has gathered alone: which heads it may consume, which it leaves
   --  as they were, and what the table and the output list hold afterwards.

   procedure Scatter_Children
     (H : Slot; Table : in out Table_Type; Out_List : in out Tree)
     with Pre => Valid and then Is_Head (Snap, H)
                 and then Links (H).Sibling = 0
                 and then Acc_Sound (Snap, Table, Out_List)
                 and then not In_Acc (Table, Out_List, H),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Head (Snap, H)
                  and then Links (H).Sibling = 0
                  and then Links (H).Child = 0
                  and then Acc_Sound (Snap, Table, Out_List)
                  and then not In_Acc (Table, Out_List, H)
                  and then KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (H))
                           = KM.Sum (Acc_Model (Snap'Old, Table'Old,
                                                Out_List'Old),
                                     Snap'Old.Sub (H))
                  and then (for all Y in 1 .. Capacity =>
                              (if In_Acc (Table, Out_List, Y)
                               then In_Acc (Table'Old, Out_List'Old, Y)
                                    or else not Is_Head (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= H
                                  and then not In_Acc (Table'Old,
                                                       Out_List'Old, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y) and then Y /= H
                                  and then not In_Acc (Table, Out_List, Y)
                               then Is_Head (Snap'Old, Y)
                                    and then not In_Acc (Table'Old,
                                                         Out_List'Old, Y)));
   --  Move every child of the single tree H into the pass

   procedure Scatter_Children
     (H : Slot; Table : in out Table_Type; Out_List : in out Tree)
   is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      Entry_Out : constant Tree := Out_List with Ghost;
      C : Slot;
      M_Acc, M_H, M_C : KM.Multiset with Ghost;
      S0, S1 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
      O0 : Tree with Ghost;
   begin
      Models.Lemma_Sum_Empty (Sub (H));
      while Links (H).Child /= 0 loop
         pragma Loop_Invariant
           (Valid and then Stable (Entry_State)
            and then Is_Head (Snap, H) and then Links (H).Sibling = 0
            and then Acc_Sound (Snap, Table, Out_List)
            and then not In_Acc (Table, Out_List, H));
         pragma Loop_Invariant
           (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (H))
              = KM.Sum (Acc_Model (Entry_State, Entry_Table, Entry_Out),
                        Entry_State.Sub (H)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if In_Acc (Table, Out_List, Y)
               then In_Acc (Entry_Table, Entry_Out, Y)
                    or else not Is_Head (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Unchanged (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Acc (Entry_Table, Entry_Out, Y)));
         pragma Loop_Variant (Decreases => Links (H).Rank);

         S0 := Snap;
         T0 := Table;
         O0 := Out_List;
         M_Acc := Acc_Model (Snap, Table, Out_List);
         M_H := Sub (H);
         Pop_Child (H, C);
         M_C := Sub (C);
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0
               then Table (Q) /= H and then Unchanged (S0, Table (Q))));
         pragma Assert
           (if Out_List /= 0
            then Out_List /= H and then Unchanged (S0, Out_List));
         pragma Assert (Acc_Sound (Snap, Table, Out_List));
         pragma Assert (not In_Acc (Table, Out_List, C));
         Lemma_Acc_Frame (S0, Table, Out_List, Snap);
         S1 := Snap;
         Place (Table, Out_List, C);
         pragma Assert (Unchanged (S1, H));
         pragma Assert
           (Acc_Model (Snap, Table, Out_List) = KM.Sum (M_Acc, M_C));
         pragma Assert (M_H = KM.Sum (Sub (H), M_C));
         Models.Lemma_Sum_Assoc (M_Acc, M_C, Sub (H));
         Models.Lemma_Sum_Symmetric (M_C, Sub (H));
         pragma Assert
           (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (H))
              = KM.Sum (M_Acc, M_H));

         --  The invariant again, as it stands at the end of the step, so
         --  that it is known on leaving the loop as well.
         pragma Assert
           (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (H))
              = KM.Sum (Acc_Model (Entry_State, Entry_Table, Entry_Out),
                        Entry_State.Sub (H)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if In_Acc (Table, Out_List, Y)
               then Y = C or else In_Acc (T0, O0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if In_Acc (Table, Out_List, Y)
               then In_Acc (Entry_Table, Entry_Out, Y)
                    or else not Is_Head (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Same (S0, Entry_State, Y)
                    and then Y /= C and then not In_Acc (T0, O0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Same (S1, S0, Y) and then Same (Snap, S1, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= H
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Unchanged (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (S1, Y) and then Y /= C
                    and then not In_Acc (T0, O0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= H
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Acc (Entry_Table, Entry_Out, Y)));
      end loop;
   end Scatter_Children;

   procedure Scatter_List
     (Rest : Tree; Table : in out Table_Type; Out_List : in out Tree)
     with Pre => Valid
                 and then (Rest = 0
                           or else (Is_Head (Snap, Rest)
                                    and then not In_Acc (Table, Out_List,
                                                         Rest)))
                 and then Acc_Sound (Snap, Table, Out_List),
          Post => Valid and then Stable (Snap'Old)
                  and then Acc_Sound (Snap, Table, Out_List)
                  and then Acc_Model (Snap, Table, Out_List)
                           = KM.Sum (Acc_Model (Snap'Old, Table'Old,
                                                Out_List'Old),
                                     Sub_Of (Snap'Old, Rest))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y) and then Y /= Rest
                                  and then not In_Acc (Table'Old,
                                                       Out_List'Old, Y)
                               then Unchanged (Snap'Old, Y)
                                    and then not In_Acc (Table, Out_List, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y)
                                  and then not In_Acc (Table, Out_List, Y)
                               then Is_Head (Snap'Old, Y) and then Y /= Rest
                                    and then not In_Acc (Table'Old,
                                                         Out_List'Old, Y)));
   --  Move every tree of the list headed by Rest into the pass

   procedure Scatter_List
     (Rest : Tree; Table : in out Table_Type; Out_List : in out Tree)
   is
      Entry_State : constant Snapshot := Snap with Ghost;
      Entry_Table : constant Table_Type := Table with Ghost;
      Entry_Out : constant Tree := Out_List with Ghost;
      Cur : Tree := Rest;
      Next : Tree;
      M_Acc, M_Cur, M_Next : KM.Multiset with Ghost;
      S0, S1 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
      O0 : Tree with Ghost;
   begin
      Models.Lemma_Sum_Empty (Acc_Model (Snap, Table, Out_List));
      while Cur /= 0 loop
         pragma Loop_Invariant
           (Valid and then Stable (Entry_State)
            and then Is_Head (Snap, Cur)
            and then Acc_Sound (Snap, Table, Out_List)
            and then not In_Acc (Table, Out_List, Cur));
         pragma Loop_Invariant
           (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (Cur))
              = KM.Sum (Acc_Model (Entry_State, Entry_Table, Entry_Out),
                        Sub_Of (Entry_State, Rest)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Unchanged (Entry_State, Y)
                    and then Y /= Cur
                    and then not In_Acc (Table, Out_List, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Cur
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (Entry_State, Y) and then Y /= Rest
                    and then not In_Acc (Entry_Table, Entry_Out, Y)));
         pragma Loop_Variant (Decreases => Size_Now (Cur));

         S0 := Snap;
         T0 := Table;
         O0 := Out_List;
         M_Acc := Acc_Model (Snap, Table, Out_List);
         Split (Cur, Next);
         M_Cur := Sub (Cur);
         M_Next := Sub_Now (Next);
         pragma Assert
           (for all Q in Rank_Type =>
              (if Table (Q) /= 0
               then Table (Q) /= Cur and then Unchanged (S0, Table (Q))));
         pragma Assert
           (if Out_List /= 0
            then Out_List /= Cur and then Unchanged (S0, Out_List));
         pragma Assert (Acc_Sound (Snap, Table, Out_List));
         pragma Assert
           (if Next /= 0 then not In_Acc (Table, Out_List, Next));
         Lemma_Acc_Frame (S0, Table, Out_List, Snap);
         S1 := Snap;
         Place (Table, Out_List, Cur);
         pragma Assert (if Next /= 0 then Unchanged (S1, Next));
         pragma Assert (Sub_Now (Next) = M_Next);
         pragma Assert
           (Acc_Model (Snap, Table, Out_List) = KM.Sum (M_Acc, M_Cur));
         Models.Lemma_Sum_Assoc (M_Acc, M_Cur, M_Next);

         --  The invariant again, for the list behind Cur, so that it is
         --  known on leaving the loop as well.
         pragma Assert
           (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub_Now (Next))
              = KM.Sum (Acc_Model (Entry_State, Entry_Table, Entry_Out),
                        Sub_Of (Entry_State, Rest)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if In_Acc (Table, Out_List, Y)
               then Y = Cur or else In_Acc (T0, O0, Y)));
         pragma Assert (if Next /= 0 then not Is_Head (S0, Next));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Same (S0, Entry_State, Y)
                    and then Y /= Cur and then Y /= Next
                    and then not In_Acc (T0, O0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then not In_Acc (Table, Out_List, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Same (S1, S0, Y) and then Same (Snap, S1, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y) and then Y /= Rest
                  and then not In_Acc (Entry_Table, Entry_Out, Y)
               then Unchanged (Entry_State, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Next
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (S1, Y) and then Y /= Cur
                    and then not In_Acc (T0, O0, Y)));
         pragma Assert
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then Y /= Next
                  and then not In_Acc (Table, Out_List, Y)
               then Is_Head (Entry_State, Y) and then Y /= Rest
                    and then not In_Acc (Entry_Table, Entry_Out, Y)));
         Cur := Next;
      end loop;
      Models.Lemma_Sum_Empty (Acc_Model (Snap, Table, Out_List));
   end Scatter_List;

   procedure Gather (Table : Table_Type; Out_List : Tree; T : out Tree)
     with Pre => Valid and then Acc_Sound (Snap, Table, Out_List),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, T)
                  and then Sub_Of (Snap, T)
                           = Acc_Model (Snap'Old, Table, Out_List)
                  and then (if T /= 0 then In_Acc (Table, Out_List, T))
                  and then (for all Y in 1 .. Capacity =>
                              (if Is_Head (Snap'Old, Y)
                                  and then not In_Acc (Table, Out_List, Y)
                               then Unchanged (Snap'Old, Y)))
                  and then (for all Y in 1 .. Capacity =>
                              (if Head_Now (Y) and then Y /= T
                               then Is_Head (Snap'Old, Y)
                                    and then not In_Acc (Table, Out_List,
                                                         Y)));
   --  Merge the trees left in the table into the output list

   procedure Gather (Table : Table_Type; Out_List : Tree; T : out Tree) is
      Entry_State : constant Snapshot := Snap with Ghost;
      Left : Table_Type := Table;
      Goal : constant KM.Multiset := Acc_Model (Snap, Table, Out_List)
        with Ghost;
      M_Table, M_T, M_Entry : KM.Multiset with Ghost;
      S0 : Snapshot with Ghost;
      T0 : Table_Type with Ghost;
      U0 : Tree with Ghost;
   begin
      T := Out_List;
      for R in Rank_Type loop
         if Left (R) /= 0 then
            S0 := Snap;
            T0 := Left;
            U0 := T;
            M_Table := Table_Model (Snap, Left, Max_Rank);
            M_T := Sub_Now (T);
            M_Entry := Sub (Left (R));
            pragma Assert (Node_In_Use (Snap, Left (R)));
            pragma Assert (Is_Minimum (Snap, Left (R), Keys (Left (R))));
            Merge_Root (T, Left (R));
            Left (R) := 0;
            pragma Assert
              (for all Q in Rank_Type =>
                 (if Left (Q) /= 0
                  then Left (Q) /= T and then Unchanged (S0, Left (Q))));
            Lemma_Table (S0, T0, Snap, Left, R, Max_Rank);
            Models.Lemma_Sum_Empty (M_Table);
            pragma Assert
              (M_Table = KM.Sum (Table_Model (Snap, Left, Max_Rank), M_Entry));
            pragma Assert (Sub (T) = KM.Sum (M_T, M_Entry));
            Gather_Model (Table_Model (Snap, Left, Max_Rank), M_Entry, M_T);
            pragma Assert
              (Acc_Model (Snap, Left, T) = KM.Sum (M_Table, M_T));
            pragma Assert
              (for all Y in 1 .. Capacity =>
                 (if Is_Head (Entry_State, Y)
                     and then not In_Acc (Table, Out_List, Y)
                  then Same (S0, Entry_State, Y) and then Same (Snap, S0, Y)));
            pragma Assert
              (for all Y in 1 .. Capacity =>
                 (if Head_Now (Y) and then not In_Acc (Left, T, Y)
                  then Is_Head (S0, Y) and then not In_Acc (T0, U0, Y)));
         end if;
         pragma Loop_Invariant (Valid and then Stable (Entry_State));
         pragma Loop_Invariant
           (Acc_Sound (Snap, Left, T)
            and then (for all Q in 0 .. R => Left (Q) = 0)
            and then (for all Q in Rank_Type =>
                        (if Left (Q) /= 0 then Left (Q) = Table (Q)))
            and then (if T /= 0 then In_Acc (Table, Out_List, T)));
         pragma Loop_Invariant (Acc_Model (Snap, Left, T) = Goal);
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Is_Head (Entry_State, Y)
                  and then not In_Acc (Table, Out_List, Y)
               then Unchanged (Entry_State, Y)));
         pragma Loop_Invariant
           (for all Y in 1 .. Capacity =>
              (if Head_Now (Y) and then not In_Acc (Left, T, Y)
               then Is_Head (Entry_State, Y)
                    and then not In_Acc (Table, Out_List, Y)));
      end loop;
      Lemma_Table_Empty (Snap, Left, Max_Rank);
      Models.Lemma_Sum_Empty_Left (Sub_Of (Snap, T));
      pragma Assert (Sub_Of (Snap, T) = Goal);
      pragma Assert (for all Y in 1 .. Capacity => not In_Table (Left, Y));
   end Gather;

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
      Entry_State : constant Snapshot := Snap with Ghost;
      H : constant Slot := T;
      Rest : Tree;
      Table : Table_Type := [others => 0];
      Out_List : Tree := 0;
      M_Acc, M_Rest : KM.Multiset with Ghost;
      S1, S2, S3, S4 : Snapshot with Ghost;
      T2, T4 : Table_Type with Ghost;
      O2, O4 : Tree with Ghost;
   begin
      K := Keys (T);

      --  Detach the minimum from its list, pass its children and then the
      --  rest of the list through the table, and merge what is left there.
      Split (H, Rest);
      S1 := Snap;
      Lemma_Table_Empty (Snap, Table, Max_Rank);
      Models.Lemma_Sum_Empty (Table_Model (Snap, Table, Max_Rank));
      pragma Assert (KM.Is_Empty (Acc_Model (Snap, Table, Out_List)));
      Models.Lemma_Sum_Empty_Left (Sub (H));
      pragma Assert (for all R in Rank_Type => Table (R) = 0);
      pragma Assert
        (KM.Sum (Acc_Model (Snap, Table, Out_List), Sub (H)) = Sub (H));
      Scatter_Children (H, Table, Out_List);
      S2 := Snap;
      T2 := Table;
      O2 := Out_List;

      pragma Assert (Node_In_Use (Snap, H));
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);
      pragma Assert (Sub (H) = KM.Add (KM.Empty_Multiset, K));
      M_Acc := Acc_Model (Snap, Table, Out_List);
      M_Rest := Sub_Of (S1, Rest);
      pragma Assert (if Rest /= 0 then Unchanged (S1, Rest));
      pragma Assert (if Rest /= 0 then not In_Acc (Table, Out_List, Rest));
      pragma Assert (KM.Sum (M_Acc, Sub (H)) = S1.Sub (H));
      Models.Lemma_Sum_Add (M_Acc, KM.Empty_Multiset, K);
      Models.Lemma_Sum_Empty (M_Acc);
      pragma Assert (KM.Sum (M_Acc, Sub (H)) = KM.Add (M_Acc, K));
      Models.Lemma_Sum_Add_Left (M_Acc, M_Rest, K);
      pragma Assert
        (Entry_State.Sub (H) = KM.Add (KM.Sum (M_Acc, M_Rest), K));

      Total_Bound_One (Snap, H, Capacity);
      Deallocate (H);
      S3 := Snap;
      pragma Assert
        (for all Q in Rank_Type =>
           (if Table (Q) /= 0 then Same (S3, S2, Table (Q))));
      pragma Assert (if Out_List /= 0 then Same (S3, S2, Out_List));
      pragma Assert (Acc_Sound (Snap, Table, Out_List));
      Lemma_Acc_Frame (S2, Table, Out_List, Snap);
      pragma Assert (if Rest /= 0 then Same (S3, S2, Rest));

      Scatter_List (Rest, Table, Out_List);
      S4 := Snap;
      T4 := Table;
      O4 := Out_List;
      pragma Assert
        (Acc_Model (Snap, Table, Out_List) = KM.Sum (M_Acc, M_Rest));
      Gather (Table, Out_List, T);
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
            then Same (S2, S1, Y) and then not In_Acc (T2, O2, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S3, S2, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Is_Head (Entry_State, Y) and then Y /= H
            then Same (S4, S3, Y) and then not In_Acc (T4, O4, Y)));
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
            then Is_Head (S4, Y) and then not In_Acc (T4, O4, Y)));
      pragma Assert
        (for all Y in 1 .. Capacity =>
           (if Head_Now (Y) and then Y /= T
            then Is_Head (S3, Y) and then Y /= Rest
                 and then not In_Acc (T2, O2, Y)));
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

end Heaps.Rank_Pairing;
