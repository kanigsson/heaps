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

package body Heaps.Leftist_Arena with SPARK_Mode is

   package KM renames Key_Multisets;

   --------------------------
   -- Allocation          --
   --------------------------

   procedure Allocate (I : out Slot; K : Key_Type)
     with Pre  => Valid and then Room >= 1,
          Post => Valid
                  and then In_Use (Snap, I)
                  and then Room = Room'Old - 1
                  and then Keys (I) = K
                  and then Sub (I) = KM.Add (KM.Empty_Multiset, K)
                  and then Links (I).Left = 0
                  and then Links (I).Right = 0
                  and then Links (I).Parent = 0
                  and then Links (I).Size = 1
                  and then Links (I).Dist = 1

                  --  Every node that was in use is untouched, model included

                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                               then X /= I
                                    and then In_Use (Snap, X)
                                    and then Keys (X) = Snap'Old.Keys (X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Take the head of the free chain and hand it back as a one-node tree
   --  holding K. The key goes in here rather than in the caller because a node
   --  in use is required to carry a cached model that matches its key, so an
   --  allocation that left the key unset would leave the arena invalid.

   procedure Deallocate (I : Slot)
     with Pre  => Valid
                  and then Room < Capacity
                  and then In_Use (Snap, I)
                  and then Links (I).Left = 0
                  and then Links (I).Right = 0
                  and then Links (I).Parent = 0
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap, X) and then X /= I
                               then Links (X).Left /= I
                                    and then Links (X).Right /= I
                                    and then Links (X).Parent /= I)),
          Post => Valid
                  and then not In_Use (Snap, I)
                  and then Room = Room'Old + 1
                  and then Keys = Snap'Old.Keys
                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X) and then X /= I
                               then In_Use (Snap, X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Push a detached node back onto the free chain. It has to be detached
   --  already -- no link anywhere may still name it -- which is what the
   --  precondition asks for.

   procedure Merge (A, B : Tree; R : out Tree)
     with Pre  => Valid

                  --  The subtree sizes have to fit in their type through the
                  --  recursion. Carrying the bound in the contract rather than
                  --  deriving it from the invariant is what keeps it pure
                  --  arithmetic, as PROOF.md records for the same reason.

                  and then Size_Now (A) + Size_Now (B) <= Capacity
                  and then (if A /= 0
                            then In_Use (Snap, A)
                                 and then Links (A).Parent = 0)
                  and then (if B /= 0
                            then In_Use (Snap, B)
                                 and then Links (B).Parent = 0)
                  and then (if A /= 0 and then B /= 0 then A /= B),
          Post => Valid
                  and then Keys = Snap'Old.Keys
                  and then Chain_Pos = Snap'Old.Chain_Pos
                  and then Free = Snap'Old.Free
                  and then Free_Count = Snap'Old.Free_Count
                  and then (if A = 0 then R = B
                            elsif B = 0 then R = A
                            else R = A or else R = B)
                  and then (if R /= 0
                            then In_Use (Snap, R)
                                 and then Links (R).Parent = 0
                                 and then Links (R).Size
                                          = Size_Of_Node (Snap'Old, A)
                                            + Size_Of_Node (Snap'Old, B))

                  --  The model of the result is the sum of the two operands'.
                  --  Because the model is cached, this is an equality between
                  --  three array elements rather than a statement about which
                  --  nodes belong to which tree.

                  and then Sub_Now (R)
                           = Sub_Of (Snap'Old, A) + Sub_Of (Snap'Old, B)

                  --  A merge creates no root except the one it returns, and A
                  --  and B are no longer roots.

                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap, X)
                                  and then Links (X).Parent = 0
                                  and then X /= R
                               then Snap'Old.Links (X).Parent = 0
                                    and then X /= A
                                    and then X /= B))

                  --  And the other trees of the arena come back untouched,
                  --  their cached models included. This is the clause that
                  --  the recursive alternative could not state without a
                  --  reachability relation, and it composes through the
                  --  recursion exactly as the link-level frame does.

                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                                  and then Snap'Old.Links (X).Parent = 0
                                  and then X /= A
                                  and then X /= B
                               then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X))),
          Subprogram_Variant =>
            (Decreases => Size_Now (A) + Size_Now (B));
   --  Merge the two trees rooted at A and B into one and return its root.
   --  Everything the operations do to the shape of the arena happens here.

   --------------
   -- Allocate --
   --------------

   procedure Allocate (I : out Slot; K : Key_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Head   : constant Slot := Free;
      Next   : constant Tree := Links (Head).Left;
   begin
      I := Head;

      --  The head sits at the far end of the chain, and by injectivity it is
      --  the only node that does, so every other free node is at a position
      --  that survives the decrement.

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
        (Left => 0, Right => 0, Parent => 0, Size => 1, Dist => 1);
      Sub (Head) := KM.Add (KM.Empty_Multiset, K);

      --  Nothing in use pointed at the head, because a free node's Left is a
      --  free node and every used node's links are used nodes.

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
   end Allocate;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (I : Slot) is
      Before : constant Snapshot := Snap with Ghost;
   begin
      Links (I).Left   := Free;
      Free_Count       := Free_Count + 1;
      Chain_Pos (I)    := Free_Count;
      Chain_At (Free_Count) := I;
      Free             := I;

      --  I was in use, so no free node's Left named it and it is genuinely a
      --  new position at the far end: injectivity survives because every other
      --  free node is strictly below the new Free_Count.

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
      --  Thread every slot onto the free chain, the last slot at the head, so
      --  that a slot's position along the chain is its own index.
      --
      --  The ghost arrays are written as aggregates rather than in a loop. An
      --  iterated component association defines every element directly, so
      --  there is nothing for a loop invariant to carry out; the loop version
      --  rested its postcondition on carrying one, which was a single large
      --  goal that sat on the prover's time limit and went through or not
      --  depending on how loaded the run was. These three arrays are erased at
      --  run time, so the form costs nothing there.

      Chain_Pos := [for J in 1 .. Capacity => J];
      Chain_At  := [for J in 1 .. Capacity => J];
      Sub       := [for J in 1 .. Capacity => KM.Empty_Multiset];

      --  Links is real, and there the same form is not free: an array
      --  aggregate is built as a whole-array temporary before being assigned,
      --  and at the sizes this arena exists for that temporary overflows an
      --  ordinary stack. So this one array is written slot by slot. It costs
      --  an invariant, but only over the one array whose elements differ from
      --  each other, and the three goals above stay in their cheap form.

      for I in 1 .. Capacity loop
         Links (I) :=
           (Left   => (if I = 1 then 0 else I - 1),
            Right  => 0,
            Parent => 0,
            Size   => 0,
            Dist   => 0);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Links (J) = (Left   => (if J = 1 then 0 else J - 1),
                           Right  => 0,
                           Parent => 0,
                           Size   => 0,
                           Dist   => 0));
      end loop;

      Free       := Capacity;
      Free_Count := Capacity;

      --  One clause of Valid at a time, so that none of them is a large
      --  verification condition.

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

   -------------
   -- Size_Of --
   -------------

   function Size_Of (T : Tree) return Extended_Index is
     (if T = 0 then 0 else Links (T).Size);

   --------------
   -- Peek_Min --
   --------------

   function Peek_Min (T : Tree) return Key_Type is (Keys (T));

   -----------
   -- Merge --
   -----------

   procedure Merge (A, B : Tree; R : out Tree) is
      Was   : Extended_Index with Ghost;
      --  The size of Top before its right subtree is cut loose

      Top   : Slot;
      Other : Slot;
      Rest  : Tree;
      Sub_R : Tree;
      Swap  : Tree;
   begin
      if A = 0 or else B = 0 then
         R := (if A = 0 then B else A);

         if A = 0 then
            KM.Lemma_Sym_Sum (Sub_Now (A), Sub_Now (B));
         end if;
         Models.Lemma_Sum_Empty (Sub_Now (R));

         return;
      end if;

      --  The smaller of the two roots is the root of the result

      if Keys (A) <= Keys (B) then
         Top := A;
         Other := B;
      else
         Top := B;
         Other := A;
      end if;

      --  Detach the right subtree of Top. Doing so before the recursive call
      --  rather than after it keeps the arena a well formed forest throughout:
      --  Top is left a smaller but perfectly valid tree, and the subtree that
      --  has just left it becomes a tree of its own. The cached model of Top
      --  is brought down with its Size, by the same assignment.

      Was  := Links (Top).Size;
      Rest := Links (Top).Right;

      if Rest /= 0 then
         Links (Rest).Parent := 0;
      end if;

      Links (Top).Right := 0;
      Links (Top).Size := 1 + Size_Now (Links (Top).Left);
      Links (Top).Dist := 1;
      Sub (Top) :=
        KM.Add (KM.Sum (Sub_Now (Links (Top).Left),
                        Sub_Now (Links (Top).Right)),
                Keys (Top));

      --  The detached subtree is strictly smaller than the node it left, so
      --  the bound the contract carries still holds one level down.

      pragma Assert (Was = 1 + Size_Now (Links (Top).Left) + Size_Now (Rest));
      pragma Assert (Size_Now (Rest) + Size_Now (Other) <= Capacity);

      Merge (Rest, Other, Sub_R);

      --  Top was a tree of its own across the call, so the merge left it
      --  alone -- its links and its cached model both.

      pragma Assert (Sub_R /= 0 and then Sub_R /= Top);
      pragma Assert (Links (Sub_R).Parent = 0);
      pragma Assert (Links (Top).Left /= Sub_R);

      Links (Sub_R).Parent := Top;
      Links (Top).Right := Sub_R;

      --  Restore the leftist condition by putting the deeper subtree on the
      --  left, then say what the node has become.

      if Dist_Now (Links (Top).Left) < Dist_Now (Links (Top).Right) then
         Swap := Links (Top).Left;
         Links (Top).Left := Links (Top).Right;
         Links (Top).Right := Swap;
      end if;

      Links (Top).Size :=
        1 + Size_Now (Links (Top).Left) + Size_Now (Links (Top).Right);
      Links (Top).Dist := 1 + Dist_Now (Links (Top).Right);
      Sub (Top) :=
        KM.Add (KM.Sum (Sub_Now (Links (Top).Left),
                        Sub_Now (Links (Top).Right)),
                Keys (Top));

      R := Top;
   end Merge;

   ----------
   -- Meld --
   ----------

   procedure Meld (T : in out Tree; U : in out Tree) is
      New_Root : Tree;
   begin
      Merge (T, U, New_Root);
      T := New_Root;
      U := 0;
   end Meld;

   ------------
   -- Insert --
   ------------

   procedure Insert (T : in out Tree; K : Key_Type) is
      Node     : Slot;
      New_Root : Tree;
      Before   : constant Tree := T;
   begin
      Allocate (Node, K);

      pragma Assert (Before /= Node);

      Merge (Before, Node, New_Root);
      T := New_Root;

      Models.Lemma_Sum_Empty (Sub_Now (Before));
      Models.Lemma_Sum_Add (Sub_Now (Before), KM.Empty_Multiset, K);
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (T : in out Tree; K : out Key_Type) is
      Gone     : constant Slot := T;
      Held     : constant Extended_Index := Links (T).Size with Ghost;
      --  What the tree held before its root was cut away
      Left     : constant Tree := Links (Gone).Left;
      Right    : constant Tree := Links (Gone).Right;
      New_Root : Tree;
   begin
      K := Keys (Gone);

      --  Cut the two subtrees loose and give the root's slot back. Without
      --  prefix compaction there is nothing else to do: no live node moves, so
      --  no cached model has to follow one.

      if Left /= 0 then
         Links (Left).Parent := 0;
      end if;

      if Right /= 0 then
         Links (Right).Parent := 0;
      end if;

      --  Cutting the children off leaves Gone a one-node tree, so its size and
      --  its cached model have to say so: a node still in use whose Size were
      --  0, or whose model did not match its key, would make the arena
      --  invalid between here and the release below.

      Links (Gone) := (Left => 0, Right => 0, Parent => 0, Size => 1,
                       Dist => 1);
      Sub (Gone) := KM.Add (KM.Empty_Multiset, Keys (Gone));

      Deallocate (Gone);

      --  The two subtrees together held one node fewer than the tree did.

      pragma Assert (Size_Now (Left) + Size_Now (Right) = Held - 1);
      pragma Assert (Size_Now (Left) + Size_Now (Right) <= Capacity);

      Merge (Left, Right, New_Root);
      T := New_Root;
   end Extract_Min;

end Heaps.Leftist_Arena;
