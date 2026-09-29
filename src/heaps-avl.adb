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

package body Heaps.AVL with SPARK_Mode is

   package KM renames Key_Multisets;

   --  Multiset equality is extensional. These proved algebraic lemmas
   --  compose helper results without unfolding the whole arena again.

   procedure Rotate_Model (LL, LR, AR : KM.Multiset; KL, KA : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Sum (LL, KM.Add (KM.Sum (LR, AR), KA)), KL)
                    = KM.Add (KM.Sum (KM.Add (KM.Sum (LL, LR), KL), AR), KA);
   procedure Rotate_Model (LL, LR, AR : KM.Multiset; KL, KA : Key_Type)
   is null;
   --  A right rotation, read left to right; read right to left, with the
   --  sides exchanged, it is a left rotation

   procedure Rotate_Model_Left
     (AL, RL, RR : KM.Multiset; KA, KR : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Sum (KM.Add (KM.Sum (AL, RL), KA), RR), KR)
                    = KM.Add (KM.Sum (AL, KM.Add (KM.Sum (RL, RR), KR)), KA);
   procedure Rotate_Model_Left
     (AL, RL, RR : KM.Multiset; KA, KR : Key_Type) is null;

   procedure Grow_Left (C, O : KM.Multiset; KA, KN : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Sum (KM.Add (C, KN), O), KA)
                    = KM.Add (KM.Add (KM.Sum (C, O), KA), KN);
   procedure Grow_Left (C, O : KM.Multiset; KA, KN : Key_Type) is null;
   --  One key more in the left subtree is one key more in the tree

   procedure Grow_Right (O, C : KM.Multiset; KA, KN : Key_Type)
     with Ghost,
          Post => KM.Add (KM.Sum (O, KM.Add (C, KN)), KA)
                    = KM.Add (KM.Add (KM.Sum (O, C), KA), KN);
   procedure Grow_Right (O, C : KM.Multiset; KA, KN : Key_Type) is null;

   procedure Move_Model (T, R : KM.Multiset; K : Key_Type)
     with Ghost,
          Post => KM.Sum (KM.Add (T, K), R) = KM.Sum (T, KM.Add (R, K));
   procedure Move_Model (T, R : KM.Multiset; K : Key_Type) is null;
   --  A key moving from one tree to the other in a meld

   ----------------------
   -- Frame predicates --
   ----------------------

   function Stable (S : Snapshot) return Boolean is
     (Keys = S.Keys and then Chain_Pos = S.Chain_Pos
      and then Chain_At = S.Chain_At
      and then Free = S.Free and then Free_Count = S.Free_Count) with Ghost;

   function Root_Now (X : Slot) return Boolean is (Is_Root (Snap, X))
     with Ghost;

   function Same (After, Before : Snapshot; X : Slot) return Boolean is
     (Is_Root (After, X)
      and then After.Links (X) = Before.Links (X)
      and then KM.Multiset_Logic_Equal (After.Sub (X), Before.Sub (X)))
     with Ghost;
   --  X is a root in After, with the links and model it had in Before. The
   --  model is compared by logical rather than extensional equality, so
   --  that the relation chains across steps by rewriting alone.

   function Unchanged (S : Snapshot; X : Slot) return Boolean is
     (Same (Snap, S, X))
     with Ghost;

   function Frame (S : Snapshot; A, B : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Is_Root (S, X) and then X /= A and then X /= B
         then Unchanged (S, X)))
     with Ghost;
   --  Every root the operation does not name comes back untouched

   function Origins (S : Snapshot; A, B, R1, R2 : Tree) return Boolean is
     (for all X in 1 .. Capacity =>
        (if Root_Now (X) and then X /= R1 and then X /= R2
         then Is_Root (S, X) and then X /= A and then X /= B))
     with Ghost;
   --  Every root other than the results was a root, and not an operand

   function From (S : Snapshot; R, A, B : Tree) return Boolean is
     (if R /= 0 and then Is_Root (S, R) then R = A or else R = B)
     with Ghost;
   --  A result that was already a root is one of the operands, so it is
   --  none of the roots the operation leaves alone

   function Keep (S : Snapshot; A, C : Tree) return Boolean is
     ((for all X in 1 .. Capacity =>
         (if X /= A then KM.Multiset_Logic_Equal (Sub (X), S.Sub (X))))
      and then (for all X in 1 .. Capacity =>
                  (if X /= A and then X /= C
                   then Links (X) = S.Links (X))))
     with Ghost;
   --  Only the models of A and the links of A and C changed. This is what
   --  carries the subtrees a rotation does not restructure through it.

   --  A root that an operation left unchanged, and whose other side is
   --  empty, still has the model it had below its one child: the operation
   --  can only frame roots, but the cached model of the root pins down the
   --  model of that child.

   procedure Lemma_Right_Kept (S : Snapshot; A : Slot)
     with Ghost,
          Pre  => Valid (S) and then Valid and then Is_Root (S, A)
                  and then Unchanged (S, A)
                  and then Links (A).Left = 0,
          Post => Sub_Now (Links (A).Right)
                  = Sub_Of (S, S.Links (A).Right);

   procedure Lemma_Right_Kept (S : Snapshot; A : Slot) is
   begin
      pragma Assert (Node_In_Use (S, A));
      pragma Assert (Node_In_Use (Snap, A));
      Models.Lemma_Sum_Empty_Left (Sub_Now (Links (A).Right));
      Models.Lemma_Sum_Empty_Left (Sub_Of (S, S.Links (A).Right));
   end Lemma_Right_Kept;

   procedure Lemma_Left_Kept (S : Snapshot; A : Slot)
     with Ghost,
          Pre  => Valid (S) and then Valid and then Is_Root (S, A)
                  and then Unchanged (S, A)
                  and then Links (A).Right = 0,
          Post => Sub_Now (Links (A).Left)
                  = Sub_Of (S, S.Links (A).Left);

   procedure Lemma_Left_Kept (S : Snapshot; A : Slot) is
   begin
      pragma Assert (Node_In_Use (S, A));
      pragma Assert (Node_In_Use (Snap, A));
      Models.Lemma_Sum_Empty (Sub_Now (Links (A).Left));
      Models.Lemma_Sum_Empty (Sub_Of (S, S.Links (A).Left));
   end Lemma_Left_Kept;

   ----------------
   -- Primitives --
   ----------------

   procedure Allocate (I : out Slot; K : Key_Type)
     with Pre  => Valid and then Room >= 1,
          Post => Valid
                  and then Is_Root (Snap, I)
                  and then Room = Room'Old - 1
                  and then Keys (I) = K
                  and then Sub (I) = KM.Add (KM.Empty_Multiset, K)
                  and then Links (I) = (Left   => 0, Right  => 0,
                                        Parent => 0, Size   => 1,
                                        Height => 1)
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                               then X /= I
                                    and then In_Use (Snap, X)
                                    and then Keys (X) = Snap'Old.Keys (X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then KM.Multiset_Logic_Equal
                                               (Sub (X), Snap'Old.Sub (X))));

   procedure Deallocate (I : Slot)
     with Pre  => Valid
                  and then Room < Capacity
                  and then Is_Root (Snap, I)
                  and then Links (I).Left = 0
                  and then Links (I).Right = 0,
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
                                    and then KM.Multiset_Logic_Equal
                                               (Sub (X), Snap'Old.Sub (X))));

   --  The four primitives below are the only subprograms that write a link.
   --  Each takes a root apart or puts one together at one of its two
   --  children and preserves the arena invariant, so the rotations, the
   --  rebalancing and the two recursions above them never see a broken tree.

   procedure Detach_Left (A : Slot; C : out Tree)
     with Pre  => Valid and then Is_Root (Snap, A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, A)
                  and then C = Snap'Old.Links (A).Left
                  and then Links (A).Left = 0
                  and then Links (A).Right = Snap'Old.Links (A).Right
                  and then Size_Now (A) + Size_Now (C)
                             = Snap'Old.Links (A).Size
                  and then Snap'Old.Sub (A)
                           = KM.Add (KM.Sum (Sub_Now (C),
                                             Sub_Now (Links (A).Right)),
                                     Keys (A))
                  and then (for all E of Sub_Now (C) => E <= Keys (A))
                  and then (for all E of Sub_Now (Links (A).Right) =>
                              Keys (A) <= E)
                  and then (if C /= 0
                            then Is_Root (Snap, C)
                                 and then not Is_Root (Snap'Old, C)
                                 and then Links (C)
                                          = (Snap'Old.Links (C)
                                               with delta Parent => 0))
                  and then Keep (Snap'Old, A, C)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, 0, 0, A, C);

   procedure Detach_Right (A : Slot; C : out Tree)
     with Pre  => Valid and then Is_Root (Snap, A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, A)
                  and then C = Snap'Old.Links (A).Right
                  and then Links (A).Right = 0
                  and then Links (A).Left = Snap'Old.Links (A).Left
                  and then Size_Now (A) + Size_Now (C)
                             = Snap'Old.Links (A).Size
                  and then Snap'Old.Sub (A)
                           = KM.Add (KM.Sum (Sub_Now (Links (A).Left),
                                             Sub_Now (C)),
                                     Keys (A))
                  and then (for all E of Sub_Now (C) => Keys (A) <= E)
                  and then (for all E of Sub_Now (Links (A).Left) =>
                              E <= Keys (A))
                  and then (if C /= 0
                            then Is_Root (Snap, C)
                                 and then not Is_Root (Snap'Old, C)
                                 and then Links (C)
                                          = (Snap'Old.Links (C)
                                               with delta Parent => 0))
                  and then Keep (Snap'Old, A, C)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, 0, 0, A, C);

   procedure Attach_Left (A : Slot; C : Tree)
     with Pre  => Valid and then Is_Root (Snap, A)
                  and then Links (A).Left = 0
                  and then (C = 0 or else (Is_Root (Snap, C) and then C /= A))
                  and then (for all E of Sub_Now (C) => E <= Keys (A))
                  and then Size_Now (A) + Size_Now (C) <= Capacity,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, A)
                  and then Links (A).Left = C
                  and then Links (A).Right = Snap'Old.Links (A).Right
                  and then Links (A).Size
                             = Snap'Old.Links (A).Size
                               + Size_Of_Node (Snap'Old, C)
                  and then Sub (A)
                           = KM.Add (KM.Sum (Sub_Of (Snap'Old, C),
                                             Sub_Now (Links (A).Right)),
                                     Keys (A))
                  and then (if C /= 0
                            then Links (C)
                                 = (Snap'Old.Links (C) with delta Parent => A))
                  and then Keep (Snap'Old, A, C)
                  and then Frame (Snap'Old, A, C)
                  and then Origins (Snap'Old, C, 0, A, 0);

   procedure Attach_Right (A : Slot; C : Tree)
     with Pre  => Valid and then Is_Root (Snap, A)
                  and then Links (A).Right = 0
                  and then (C = 0 or else (Is_Root (Snap, C) and then C /= A))
                  and then (for all E of Sub_Now (C) => Keys (A) <= E)
                  and then Size_Now (A) + Size_Now (C) <= Capacity,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, A)
                  and then Links (A).Right = C
                  and then Links (A).Left = Snap'Old.Links (A).Left
                  and then Links (A).Size
                             = Snap'Old.Links (A).Size
                               + Size_Of_Node (Snap'Old, C)
                  and then Sub (A)
                           = KM.Add (KM.Sum (Sub_Now (Links (A).Left),
                                             Sub_Of (Snap'Old, C)),
                                     Keys (A))
                  and then (if C /= 0
                            then Links (C)
                                 = (Snap'Old.Links (C) with delta Parent => A))
                  and then Keep (Snap'Old, A, C)
                  and then Frame (Snap'Old, A, C)
                  and then Origins (Snap'Old, C, 0, A, 0);

   --------------
   -- Allocate --
   --------------

   procedure Allocate (I : out Slot; K : Key_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Head   : constant Slot := Free;
      Next   : constant Tree := Links (Head).Left;
   begin
      I := Head;

      pragma Assert (Chain_Pos (Head) = Free_Count);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not In_Use (Before, X) and then X /= Head
            then Chain_Pos (X) in 1 .. Capacity
                 and then Chain_At (Chain_Pos (X)) = X
                 and then Chain_Pos (X) /= Free_Count
                 and then Chain_Pos (X) <= Free_Count - 1));

      Free       := Next;
      Free_Count := Free_Count - 1;

      Chain_Pos (Head) := 0;
      Keys (Head) := K;
      Links (Head) :=
        (Left => 0, Right => 0, Parent => 0, Size => 1, Height => 1);
      Sub (Head) := KM.Add (KM.Empty_Multiset, K);
      Models.Lemma_Sum_Empty (KM.Empty_Multiset);

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X)
            then X /= Head and then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Before, X) then Node_In_Use (Snap, X)));
      pragma Assert (Node_In_Use (Snap, Head));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if not In_Use (Snap, X) then Node_Free (Snap, X)));
   end Allocate;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (I : Slot) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      --  A root with no children is named by no link: a child link to it
      --  would need a parent backlink, and a parent link from a node would
      --  need a child link back.

      pragma Assert (Node_In_Use (Snap, I));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= I
            then Node_In_Use (Snap, X)
                 and then Links (X).Left /= I
                 and then Links (X).Right /= I
                 and then Links (X).Parent /= I));

      Links (I).Left   := Free;
      Free_Count       := Free_Count + 1;
      Chain_Pos (I)    := Free_Count;
      Chain_At (Free_Count) := I;
      Free             := I;

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

   -----------------
   -- Detach_Left --
   -----------------

   procedure Detach_Left (A : Slot; C : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      R : constant Tree := Links (A).Right;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      C := Links (A).Left;
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
      pragma Assert (if R /= 0 then Node_In_Use (Snap, R));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X)
            then Links (X).Left /= A and then Links (X).Right /= A));

      if C /= 0 then
         Links (C).Parent := 0;
      end if;
      Links (A).Left := 0;
      Links (A).Size := 1 + Size_Now (R);
      Links (A).Height := 1 + Height_Now (R);
      Sub (A) := KM.Add (KM.Sum (KM.Empty_Multiset, Sub_Now (R)), Keys (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A and then X /= C then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A then Sub (X) = Before.Sub (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= C
            then Node_In_Use (Snap, X)));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
   end Detach_Left;

   ------------------
   -- Detach_Right --
   ------------------

   procedure Detach_Right (A : Slot; C : out Tree) is
      Before : constant Snapshot := Snap with Ghost;
      L : constant Tree := Links (A).Left;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      C := Links (A).Right;
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
      pragma Assert (if L /= 0 then Node_In_Use (Snap, L));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X)
            then Links (X).Left /= A and then Links (X).Right /= A));

      if C /= 0 then
         Links (C).Parent := 0;
      end if;
      Links (A).Right := 0;
      Links (A).Size := 1 + Size_Now (L);
      Links (A).Height := 1 + Height_Now (L);
      Sub (A) := KM.Add (KM.Sum (Sub_Now (L), KM.Empty_Multiset), Keys (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A and then X /= C then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A then Sub (X) = Before.Sub (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= C
            then Node_In_Use (Snap, X)));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
   end Detach_Right;

   -----------------
   -- Attach_Left --
   -----------------

   procedure Attach_Left (A : Slot; C : Tree) is
      Before : constant Snapshot := Snap with Ghost;
      R : constant Tree := Links (A).Right;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
      pragma Assert (if R /= 0 then Node_In_Use (Snap, R));
      pragma Assert (if C /= 0 then C /= R);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X)
            then Links (X).Left /= A and then Links (X).Right /= A
                 and then (if C /= 0
                           then Links (X).Left /= C
                                and then Links (X).Right /= C)));

      if C /= 0 then
         Links (C).Parent := A;
      end if;
      Links (A).Left := C;
      Links (A).Size := 1 + Size_Now (C) + Size_Now (R);
      Links (A).Height :=
        1 + Extended_Index'Max (Height_Now (C), Height_Now (R));
      Sub (A) := KM.Add (KM.Sum (Sub_Now (C), Sub_Now (R)), Keys (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A and then X /= C then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A then Sub (X) = Before.Sub (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= C
            then Node_In_Use (Snap, X)));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
   end Attach_Left;

   ------------------
   -- Attach_Right --
   ------------------

   procedure Attach_Right (A : Slot; C : Tree) is
      Before : constant Snapshot := Snap with Ghost;
      L : constant Tree := Links (A).Left;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
      pragma Assert (if L /= 0 then Node_In_Use (Snap, L));
      pragma Assert (if C /= 0 then C /= L);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X)
            then Links (X).Left /= A and then Links (X).Right /= A
                 and then (if C /= 0
                           then Links (X).Left /= C
                                and then Links (X).Right /= C)));

      if C /= 0 then
         Links (C).Parent := A;
      end if;
      Links (A).Right := C;
      Links (A).Size := 1 + Size_Now (L) + Size_Now (C);
      Links (A).Height :=
        1 + Extended_Index'Max (Height_Now (L), Height_Now (C));
      Sub (A) := KM.Add (KM.Sum (Sub_Now (L), Sub_Now (C)), Keys (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A and then X /= C then Links (X) = Before.Links (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A then Sub (X) = Before.Sub (X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X) and then X /= A and then X /= C
            then Node_In_Use (Snap, X)));
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (if C /= 0 then Node_In_Use (Snap, C));
   end Attach_Right;

   ---------------
   -- Rotations --
   ---------------

   --  A rotation replaces the root A by one of its children and keeps the
   --  model; the other roots of the arena come through it untouched.

   procedure Rotate_Right (A : Slot; R : out Slot)
     with Pre  => Valid and then Is_Root (Snap, A)
                  and then Links (A).Left /= 0,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, R)
                  and then Size_Now (R) = Snap'Old.Links (A).Size
                  and then Sub (R) = Snap'Old.Sub (A)
                  and then From (Snap'Old, R, A, 0)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, A, 0, R, 0);

   procedure Rotate_Right (A : Slot; R : out Slot) is
      S0 : constant Snapshot := Snap with Ghost;
      L : Tree;
      LR : Tree;
      M_LL, M_LR, M_AR : KM.Multiset with Ghost;
      S1, S2, S3 : Snapshot with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (Node_In_Use (Snap, Links (A).Left));
      M_AR := Sub_Now (Links (A).Right);
      M_LL := Sub_Now (Links (Links (A).Left).Left);
      M_LR := Sub_Now (Links (Links (A).Left).Right);

      Detach_Left (A, L);
      S1 := Snap;
      pragma Assert (L /= 0 and then L /= A);
      pragma Assert (Sub_Now (Links (A).Right) = M_AR);
      pragma Assert
        (S1.Sub (L) = KM.Add (KM.Sum (M_LL, M_LR), Keys (L)));
      pragma Assert (for all E of S1.Sub (L) => E <= Keys (A));
      pragma Assert (Keys (L) <= Keys (A));

      Detach_Right (L, LR);
      S2 := Snap;
      pragma Assert (Sub_Now (LR) = M_LR);
      pragma Assert (Sub_Now (Links (L).Left) = M_LL);
      pragma Assert (Links (A) = S1.Links (A));
      pragma Assert (Sub_Now (Links (A).Right) = M_AR);
      pragma Assert (for all E of Sub_Now (LR) => E <= Keys (A));
      pragma Assert (if LR /= 0 then LR /= A);

      Attach_Left (A, LR);
      S3 := Snap;
      pragma Assert (Sub (A) = KM.Add (KM.Sum (M_LR, M_AR), Keys (A)));
      pragma Assert (for all E of M_AR => Keys (L) <= E);
      pragma Assert (for all E of Sub (A) => Keys (L) <= E);
      pragma Assert (Links (L) = S2.Links (L));
      pragma Assert (Sub_Now (Links (L).Left) = M_LL);

      Attach_Right (L, A);
      R := L;
      pragma Assert
        (Sub (R) = KM.Add (KM.Sum (M_LL, S3.Sub (A)), Keys (L)));
      Rotate_Model (M_LL, M_LR, M_AR, Keys (L), Keys (A));
      pragma Assert (Sub (R) = S0.Sub (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A
            then Same (S1, S0, X) and then X /= L
                 and then Same (S2, S1, X) and then X /= LR
                 and then Same (S3, S2, X)
                 and then Same (Snap, S3, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= R
            then Is_Root (S3, X) and then X /= A
                 and then Is_Root (S2, X) and then X /= LR
                 and then Is_Root (S1, X) and then X /= L
                 and then Is_Root (S0, X)));
   end Rotate_Right;

   procedure Rotate_Left (A : Slot; R : out Slot)
     with Pre  => Valid and then Is_Root (Snap, A)
                  and then Links (A).Right /= 0,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, R)
                  and then Size_Now (R) = Snap'Old.Links (A).Size
                  and then Sub (R) = Snap'Old.Sub (A)
                  and then From (Snap'Old, R, A, 0)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, A, 0, R, 0);

   procedure Rotate_Left (A : Slot; R : out Slot) is
      S0 : constant Snapshot := Snap with Ghost;
      C : Tree;
      CL : Tree;
      M_AL, M_CL, M_CR : KM.Multiset with Ghost;
      S1, S2, S3 : Snapshot with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      pragma Assert (Node_In_Use (Snap, Links (A).Right));
      M_AL := Sub_Now (Links (A).Left);
      M_CL := Sub_Now (Links (Links (A).Right).Left);
      M_CR := Sub_Now (Links (Links (A).Right).Right);

      Detach_Right (A, C);
      S1 := Snap;
      pragma Assert (C /= 0 and then C /= A);
      pragma Assert (Sub_Now (Links (A).Left) = M_AL);
      pragma Assert
        (S1.Sub (C) = KM.Add (KM.Sum (M_CL, M_CR), Keys (C)));
      pragma Assert (for all E of S1.Sub (C) => Keys (A) <= E);
      pragma Assert (Keys (A) <= Keys (C));

      Detach_Left (C, CL);
      S2 := Snap;
      pragma Assert (Sub_Now (CL) = M_CL);
      pragma Assert (Sub_Now (Links (C).Right) = M_CR);
      pragma Assert (Links (A) = S1.Links (A));
      pragma Assert (Sub_Now (Links (A).Left) = M_AL);
      pragma Assert (for all E of Sub_Now (CL) => Keys (A) <= E);
      pragma Assert (if CL /= 0 then CL /= A);

      Attach_Right (A, CL);
      S3 := Snap;
      pragma Assert (Sub (A) = KM.Add (KM.Sum (M_AL, M_CL), Keys (A)));
      pragma Assert (for all E of M_AL => E <= Keys (C));
      pragma Assert (for all E of Sub (A) => E <= Keys (C));
      pragma Assert (Links (C) = S2.Links (C));
      pragma Assert (Sub_Now (Links (C).Right) = M_CR);

      Attach_Left (A => C, C => A);
      R := C;
      pragma Assert
        (Sub (R) = KM.Add (KM.Sum (S3.Sub (A), M_CR), Keys (C)));
      Rotate_Model_Left (M_AL, M_CL, M_CR, Keys (A), Keys (C));
      pragma Assert (Sub (R) = S0.Sub (A));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A
            then Same (S1, S0, X) and then X /= C
                 and then Same (S2, S1, X) and then X /= CL
                 and then Same (S3, S2, X)
                 and then Same (Snap, S3, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= R
            then Is_Root (S3, X) and then X /= A
                 and then Is_Root (S2, X) and then X /= CL
                 and then Is_Root (S1, X) and then X /= C
                 and then Is_Root (S0, X)));
   end Rotate_Left;

   ---------------
   -- Rebalance --
   ---------------

   --  Restore the balance at A, whose subtrees are balanced and differ in
   --  height by at most two. Nothing in the proof depends on those
   --  premises: whatever the heights, the result is a valid search tree
   --  with A's model.

   procedure Rebalance (A : Slot; R : out Slot)
     with Pre  => Valid and then Is_Root (Snap, A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, R)
                  and then Size_Now (R) = Snap'Old.Links (A).Size
                  and then Sub (R) = Snap'Old.Sub (A)
                  and then From (Snap'Old, R, A, 0)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, A, 0, R, 0);

   procedure Rebalance (A : Slot; R : out Slot) is
      S0 : constant Snapshot := Snap with Ghost;
      HL : constant Extended_Index := Height_Now (Links (A).Left);
      HR : constant Extended_Index := Height_Now (Links (A).Right);
      C  : Tree;
      C2 : Slot;
      S1, S2, S3 : Snapshot with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      if HL > HR + 1 then
         C := Links (A).Left;
         pragma Assert (C /= 0 and then Node_In_Use (Snap, C));
         if Height_Now (Links (C).Left) < Height_Now (Links (C).Right) then
            Detach_Left (A, C);
            S1 := Snap;
            pragma Assert (C /= 0 and then Links (C).Right /= 0);
            Rotate_Left (C, C2);
            S2 := Snap;
            pragma Assert (Is_Root (S1, A) and then A /= C);
            pragma Assert (C2 /= A);
            pragma Assert (Unchanged (S1, A));
            pragma Assert (for all E of Sub (C2) => E <= Keys (A));
            Lemma_Right_Kept (S1, A);
            Attach_Left (A, C2);
            S3 := Snap;
            pragma Assert (Sub (A) = S0.Sub (A));
            pragma Assert (Links (A).Size = S0.Links (A).Size);
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Is_Root (S0, X) and then X /= A
                  then Same (S1, S0, X) and then X /= C
                       and then Same (S2, S1, X) and then X /= C2
                       and then Same (S3, S2, X)));
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Root_Now (X) and then X /= A
                  then Is_Root (S2, X) and then X /= C2
                       and then Is_Root (S1, X) and then X /= C
                       and then Is_Root (S0, X)));
            pragma Assert (Frame (S0, A, 0));
            pragma Assert (Origins (S0, A, 0, A, 0));
         end if;
         S3 := Snap;
         Rotate_Right (A, R);
      elsif HR > HL + 1 then
         C := Links (A).Right;
         pragma Assert (C /= 0 and then Node_In_Use (Snap, C));
         if Height_Now (Links (C).Right) < Height_Now (Links (C).Left) then
            Detach_Right (A, C);
            S1 := Snap;
            pragma Assert (C /= 0 and then Links (C).Left /= 0);
            Rotate_Right (C, C2);
            S2 := Snap;
            pragma Assert (Is_Root (S1, A) and then A /= C);
            pragma Assert (C2 /= A);
            pragma Assert (Unchanged (S1, A));
            pragma Assert (for all E of Sub (C2) => Keys (A) <= E);
            Lemma_Left_Kept (S1, A);
            Attach_Right (A, C2);
            S3 := Snap;
            pragma Assert (Sub (A) = S0.Sub (A));
            pragma Assert (Links (A).Size = S0.Links (A).Size);
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Is_Root (S0, X) and then X /= A
                  then Same (S1, S0, X) and then X /= C
                       and then Same (S2, S1, X) and then X /= C2
                       and then Same (S3, S2, X)));
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Root_Now (X) and then X /= A
                  then Is_Root (S2, X) and then X /= C2
                       and then Is_Root (S1, X) and then X /= C
                       and then Is_Root (S0, X)));
            pragma Assert (Frame (S0, A, 0));
            pragma Assert (Origins (S0, A, 0, A, 0));
         end if;
         S3 := Snap;
         Rotate_Left (A, R);
      else
         R := A;
         return;
      end if;
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A
            then Same (S3, S0, X) and then Same (Snap, S3, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= R
            then Is_Root (S3, X) and then X /= A and then Is_Root (S0, X)));
      pragma Assert (if Is_Root (S0, R) then R = A);
   end Rebalance;

   ---------
   -- Ins --
   ---------

   --  Insert the single node N into the tree A. The child the key goes to is
   --  detached before the recursive call and attached again after it, so
   --  every call sees a valid forest of which it owns two roots.

   procedure Ins (A : Tree; N : Slot; R : out Slot)
     with Pre  => Valid and then Is_Root (Snap, A)
                  and then Is_Root (Snap, N) and then N /= A
                  and then Links (N).Left = 0
                  and then Links (N).Right = 0
                  and then Size_Now (A) + 1 <= Capacity,
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, R)
                  and then Size_Now (R) = Size_Of_Node (Snap'Old, A) + 1
                  and then Sub (R) = KM.Add (Sub_Of (Snap'Old, A), Keys (N))
                  and then From (Snap'Old, R, A, N)
                  and then Frame (Snap'Old, A, N)
                  and then Origins (Snap'Old, A, N, R, 0),
          Subprogram_Variant => (Decreases => Size_Now (A));

   procedure Ins (A : Tree; N : Slot; R : out Slot) is
      S0 : constant Snapshot := Snap with Ghost;
      C  : Tree;
      C2 : Slot;
      M_C, M_O : KM.Multiset with Ghost;
      S1, S2, S3 : Snapshot with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, N));
      if A = 0 then
         R := N;
         Models.Lemma_Sum_Empty (KM.Empty_Multiset);
         pragma Assert (Sub (R) = KM.Add (KM.Empty_Multiset, Keys (N)));
         return;
      end if;

      pragma Assert (Node_In_Use (Snap, A));
      if Keys (N) < Keys (A) then
         M_O := Sub_Now (Links (A).Right);
         Detach_Left (A, C);
         S1 := Snap;
         M_C := Sub_Now (C);
         pragma Assert (Unchanged (S0, N) and then N /= C);
         Ins (C, N, C2);
         S2 := Snap;
         pragma Assert (Is_Root (S1, A) and then A /= C and then A /= N);
         pragma Assert (C2 /= A and then Unchanged (S1, A));
         pragma Assert (Sub (C2) = KM.Add (M_C, Keys (N)));
         pragma Assert (for all E of Sub (C2) => E <= Keys (A));
         Lemma_Right_Kept (S1, A);
         pragma Assert (Sub_Now (Links (A).Right) = M_O);
         Attach_Left (A, C2);
         S3 := Snap;
         pragma Assert (Sub (A) = KM.Add (KM.Sum (Sub (C2), M_O), Keys (A)));
         Grow_Left (M_C, M_O, Keys (A), Keys (N));
         pragma Assert (S1.Links (A).Size + Size_Of_Node (S1, C)
                        = S0.Links (A).Size);
         pragma Assert (Size_Now (C2) = Size_Of_Node (S1, C) + 1);
         pragma Assert (Links (A).Size = S2.Links (A).Size + Size_Now (C2));
         pragma Assert (Links (A).Size = S0.Links (A).Size + 1);
         pragma Assert (S0.Sub (A) = KM.Add (KM.Sum (M_C, M_O), Keys (A)));
         pragma Assert (Sub (A) = KM.Add (S0.Sub (A), Keys (N)));
      else
         M_O := Sub_Now (Links (A).Left);
         Detach_Right (A, C);
         S1 := Snap;
         M_C := Sub_Now (C);
         pragma Assert (Unchanged (S0, N) and then N /= C);
         Ins (C, N, C2);
         S2 := Snap;
         pragma Assert (Is_Root (S1, A) and then A /= C and then A /= N);
         pragma Assert (C2 /= A and then Unchanged (S1, A));
         pragma Assert (Sub (C2) = KM.Add (M_C, Keys (N)));
         pragma Assert (for all E of Sub (C2) => Keys (A) <= E);
         Lemma_Left_Kept (S1, A);
         pragma Assert (Sub_Now (Links (A).Left) = M_O);
         Attach_Right (A, C2);
         S3 := Snap;
         pragma Assert (Sub (A) = KM.Add (KM.Sum (M_O, Sub (C2)), Keys (A)));
         Grow_Right (M_O, M_C, Keys (A), Keys (N));
         pragma Assert (S1.Links (A).Size + Size_Of_Node (S1, C)
                        = S0.Links (A).Size);
         pragma Assert (Size_Now (C2) = Size_Of_Node (S1, C) + 1);
         pragma Assert (Links (A).Size = S2.Links (A).Size + Size_Now (C2));
         pragma Assert (Links (A).Size = S0.Links (A).Size + 1);
         pragma Assert (S0.Sub (A) = KM.Add (KM.Sum (M_O, M_C), Keys (A)));
         pragma Assert (Sub (A) = KM.Add (S0.Sub (A), Keys (N)));
      end if;
      pragma Assert (Sub (A) = KM.Add (S0.Sub (A), Keys (N)));
      pragma Assert (Links (A).Size = S0.Links (A).Size + 1);

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A and then X /= N
            then Same (S1, S0, X) and then X /= C
                 and then Same (S2, S1, X) and then X /= C2
                 and then Same (S3, S2, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= A
            then Is_Root (S2, X) and then X /= C2
                 and then Is_Root (S1, X) and then X /= C
                 and then X /= N
                 and then Is_Root (S0, X)));
      Rebalance (A, R);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A and then X /= N
            then Same (S3, S0, X) and then Same (Snap, S3, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= R
            then Is_Root (S3, X) and then X /= A
                 and then Is_Root (S0, X) and then X /= N));
      pragma Assert (if Is_Root (S0, R) then R = A or else R = N);
   end Ins;

   -------------
   -- Rem_Min --
   -------------

   --  Take the leftmost node M out of the tree A, leaving it a single node
   --  and a root of its own.

   procedure Rem_Min (A : Slot; R : out Tree; M : out Slot)
     with Pre  => Valid and then Is_Root (Snap, A),
          Post => Valid and then Stable (Snap'Old)
                  and then Is_Root (Snap, R)
                  and then Is_Root (Snap, M)
                  and then M /= R
                  and then Links (M).Left = 0
                  and then Links (M).Right = 0
                  and then Size_Now (R) + 1 = Snap'Old.Links (A).Size
                  and then Snap'Old.Sub (A) = KM.Add (Sub_Now (R), Keys (M))
                  and then Is_Minimum (Snap'Old, A, Keys (M))
                  and then From (Snap'Old, R, A, 0)
                  and then From (Snap'Old, M, A, 0)
                  and then Frame (Snap'Old, A, 0)
                  and then Origins (Snap'Old, A, 0, R, M),
          Subprogram_Variant => (Decreases => Size_Now (A));

   procedure Rem_Min (A : Slot; R : out Tree; M : out Slot) is
      S0 : constant Snapshot := Snap with Ghost;
      C  : Tree;
      L2 : Tree;
      M_L, M_O : KM.Multiset with Ghost;
      S1, S2, S3 : Snapshot with Ghost;
   begin
      pragma Assert (Node_In_Use (Snap, A));
      if Links (A).Left = 0 then
         Detach_Right (A, C);
         M := A;
         R := C;
         pragma Assert (Node_In_Use (Snap, A));
         Models.Lemma_Sum_Empty_Left (Sub_Now (R));
         pragma Assert (S0.Sub (A) = KM.Add (Sub_Now (R), Keys (M)));
         pragma Assert (for all E of Sub_Now (R) => Keys (M) <= E);
         pragma Assert (Is_Minimum (S0, A, Keys (M)));
         return;
      end if;

      M_O := Sub_Now (Links (A).Right);
      Detach_Left (A, C);
      S1 := Snap;
      M_L := Sub_Now (C);
      pragma Assert (C /= 0);
      Rem_Min (C, L2, M);
      S2 := Snap;
      pragma Assert (Is_Root (S1, A) and then A /= C);
      pragma Assert (M /= A and then Unchanged (S1, A));
      pragma Assert (if L2 /= 0 then L2 /= A);
      pragma Assert (M_L = KM.Add (Sub_Now (L2), Keys (M)));
      pragma Assert (KM.Contains (M_L, Keys (M)));
      pragma Assert (Keys (M) <= Keys (A));
      pragma Assert (for all E of Sub_Now (L2) => E <= Keys (A));
      Lemma_Right_Kept (S1, A);
      pragma Assert (Sub_Now (Links (A).Right) = M_O);
      Attach_Left (A, L2);
      S3 := Snap;
      pragma Assert (Links (M) = S2.Links (M));
      pragma Assert
        (Sub (A) = KM.Add (KM.Sum (Sub_Of (S2, L2), M_O), Keys (A)));
      Grow_Left (Sub_Of (S2, L2), M_O, Keys (A), Keys (M));
      pragma Assert (S0.Sub (A) = KM.Add (Sub (A), Keys (M)));
      pragma Assert (for all E of M_O => Keys (M) <= E);
      pragma Assert (Is_Minimum (S0, A, Keys (M)));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A
            then Same (S1, S0, X) and then X /= C
                 and then Same (S2, S1, X) and then X /= L2
                 and then X /= M
                 and then Same (S3, S2, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= A and then X /= M
            then Is_Root (S2, X) and then X /= L2
                 and then Is_Root (S1, X) and then X /= C
                 and then Is_Root (S0, X)));
      pragma Assert (Is_Root (S3, M) and then M /= A);
      Rebalance (A, R);
      pragma Assert (Unchanged (S3, M));
      pragma Assert (M /= R);
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Is_Root (S0, X) and then X /= A
            then Same (S3, S0, X) and then Same (Snap, S3, X)));
      pragma Assert
        (for all X in 1 .. Capacity =>
           (if Root_Now (X) and then X /= R and then X /= M
            then Is_Root (S3, X) and then X /= A and then Is_Root (S0, X)));
      pragma Assert (if Is_Root (S0, R) then R = A);
      pragma Assert (if Is_Root (S0, M) then M = A);
   end Rem_Min;

   ---------------
   -- Interface --
   ---------------

   function Size_Of (T : Tree) return Extended_Index is (Size_Now (T));

   function Peek_Min (T : Tree) return Key_Type is
      X : Slot := T;
   begin
      loop
         pragma Loop_Invariant (In_Use (Snap, X));
         pragma Loop_Invariant
           (for all E of Sub (X) => KM.Contains (Sub (T), E));
         pragma Loop_Invariant
           (for all E of Sub (T) =>
              KM.Contains (Sub_Now (Links (X).Left), E)
              or else Keys (X) <= E);
         pragma Loop_Variant (Decreases => Size_Now (X));
         pragma Assert (Node_In_Use (Snap, X));
         exit when Links (X).Left = 0;
         pragma Assert (Node_In_Use (Snap, Links (X).Left));
         pragma Assert (Keys (Links (X).Left) <= Keys (X));
         X := Links (X).Left;
      end loop;
      return Keys (X);
   end Peek_Min;

   procedure Insert (T : in out Tree; K : Key_Type) is
      S0 : constant Snapshot := Snap with Ghost;
      Old_T : constant Tree := T with Ghost;
      N : Slot;
      R : Slot;
      S1 : Snapshot with Ghost;
   begin
      Allocate (N, K);
      S1 := Snap;
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Root (S0, U) then Same (S1, S0, U) and then U /= N));
      pragma Assert (Sub_Of (S1, T) = Sub_Of (S0, T));
      Ins (T, N, R);
      T := R;
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Root (S0, U) and then U /= Old_T
            then Same (S1, S0, U) and then Unchanged (S1, U)));
   end Insert;

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
      S0 : constant Snapshot := Snap with Ghost;
      Old_T : constant Tree := T with Ghost;
      P : constant Key_Type := Peek_Min (T) with Ghost;
      R : Tree;
      M : Slot;
      S1 : Snapshot with Ghost;
   begin
      Rem_Min (T, R, M);
      S1 := Snap;
      K := Keys (M);
      pragma Assert (KM.Contains (S0.Sub (Old_T), K));
      pragma Assert (P <= K and then K <= P);
      Deallocate (M);
      T := R;
      pragma Assert
        (for all U in 1 .. Capacity =>
           (if Is_Root (S0, U) and then U /= Old_T
            then Same (S1, S0, U) and then U /= M));
      pragma Assert (if R /= 0 then Is_Root (S1, R) and then R /= M);
   end Extract_Min;

   procedure Meld (T : in out Tree; U : in out Tree) is
      S0 : constant Snapshot := Snap with Ghost;
      T0 : constant Tree := T with Ghost;
      U0 : constant Tree := U with Ghost;
      R  : Tree;
      M  : Slot;
      R2 : Slot;
      S1, S2 : Snapshot with Ghost;
      M_T, M_R : KM.Multiset with Ghost;
   begin
      Models.Lemma_Sum_Empty (Sub_Of (S0, T0));
      loop
         pragma Loop_Invariant (Valid and then Stable (S0));
         pragma Loop_Invariant
           (Is_Root (Snap, T) and then Is_Root (Snap, U)
            and then (if T /= 0 and then U /= 0 then T /= U));
         pragma Loop_Invariant
           (Size_Now (T) + Size_Now (U)
              = Size_Of_Node (S0, T0) + Size_Of_Node (S0, U0));
         pragma Loop_Invariant
           (Size_Now (T) + Size_Now (U) <= Capacity);
         pragma Loop_Invariant
           (KM.Sum (Sub_Now (T), Sub_Now (U))
              = KM.Sum (Sub_Of (S0, T0), Sub_Of (S0, U0)));
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Is_Root (S0, X) and then X /= T0 and then X /= U0
               then Unchanged (S0, X) and then X /= T and then X /= U));
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Root_Now (X) and then X /= T and then X /= U
               then Is_Root (S0, X) and then X /= T0 and then X /= U0));
         pragma Loop_Variant (Decreases => Size_Now (U));
         exit when U = 0;

         S1 := Snap;
         Rem_Min (U, R, M);
         S2 := Snap;
         pragma Assert (if T /= 0 then Unchanged (S1, T) and then M /= T);
         pragma Assert (if R /= 0 then R /= T);
         M_T := Sub_Now (T);
         M_R := Sub_Now (R);
         Ins (T, M, R2);
         pragma Assert (if R /= 0 then Unchanged (S2, R) and then R /= R2);
         pragma Assert (Sub (R2) = KM.Add (M_T, Keys (M)));
         pragma Assert (S1.Sub (U) = KM.Add (M_R, Keys (M)));
         Move_Model (M_T, M_R, Keys (M));
         pragma Assert
           (for all X in 1 .. Capacity =>
              (if Is_Root (S0, X) and then X /= T0 and then X /= U0
               then Same (S2, S1, X) and then X /= M and then X /= R
                    and then Unchanged (S2, X) and then X /= R2));
         pragma Assert
           (for all X in 1 .. Capacity =>
              (if Root_Now (X) and then X /= R2 and then X /= R
               then Is_Root (S2, X) and then X /= M
                    and then Is_Root (S1, X) and then X /= T
                    and then X /= U));
         T := R2;
         U := R;
      end loop;
      Models.Lemma_Sum_Empty (Sub_Now (T));
      pragma Assert
        (for all W in 1 .. Capacity =>
           (if W /= T0 and then W /= U0 and then Is_Root (S0, W)
            then Unchanged (S0, W)));
   end Meld;

   -----------
   -- Clear --
   -----------

   procedure Clear is
   begin
      Chain_Pos := [for J in 1 .. Capacity => J];
      Chain_At  := [for J in 1 .. Capacity => J];
      Sub       := [for J in 1 .. Capacity => KM.Empty_Multiset];

      for I in 1 .. Capacity loop
         Links (I) :=
           (Left   => (if I = 1 then 0 else I - 1),
            Right  => 0,
            Parent => 0,
            Size   => 0,
            Height => 0);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Links (J) = (Left   => (if J = 1 then 0 else J - 1),
                           Right  => 0,
                           Parent => 0,
                           Size   => 0,
                           Height => 0));
      end loop;

      Free       := Capacity;
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
            then Links (I).Left = 0
            else Links (I).Left /= 0
                 and then Chain_Pos (Links (I).Left) = Chain_Pos (I) - 1));
      pragma Assert (for all I in 1 .. Capacity => Node_Free (Snap, I));
      pragma Assert (Chain_Sound (Snap));
      pragma Assert (Nodes_Sound (Snap));
   end Clear;

end Heaps.AVL;
