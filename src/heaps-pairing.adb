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

package body Heaps.Pairing with SPARK_Mode is

   package KM renames Key_Multisets;

   ----------------
   -- Allocation --
   ----------------

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

                  --  Every node that was in use is untouched, model included

                  and then (for all X in 1 .. Capacity =>
                              (if In_Use (Snap'Old, X)
                               then X /= I
                                    and then In_Use (Snap, X)
                                    and then Keys (X) = Snap'Old.Keys (X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Take the head of the free chain and hand it back as a one-node tree
   --  holding K. The key is set here because a node in use must carry a
   --  cached model matching it, so leaving it unset would leave the arena
   --  invalid.

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
                              (if In_Use (Snap'Old, X) and then X /= I
                               then In_Use (Snap, X)
                                    and then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Push a detached node back onto the free chain. It has to be detached
   --  already -- no link anywhere may still name it -- which is what the
   --  precondition asks for.

   procedure Merge (A, B : Tree; R : out Tree)
     with Pre  => Valid

                  --  The sizes have to fit in their type. Carrying the
                  --  bound in the contract rather than deriving it from the
                  --  invariant keeps it pure arithmetic.

                  and then Size_Now (A) + Size_Now (B) <= Capacity
                  and then Is_Root (Snap, A)
                  and then Is_Root (Snap, B)
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
                            then Is_Root (Snap, R)
                                 and then Links (R).Size
                                          = Size_Of_Node (Snap'Old, A)
                                            + Size_Of_Node (Snap'Old, B))

                  --  The model of the result is the sum of the two
                  --  operands', which with a cached model is an equality
                  --  between three array elements.

                  and then Sub_Now (R)
                           = Sub_Of (Snap'Old, A) + Sub_Of (Snap'Old, B)

                  --  A merge creates no root except the one it returns, and A
                  --  and B are no longer roots.

                  and then (for all X in 1 .. Capacity =>
                              (if Is_Root (Snap, X) and then X /= R
                               then Is_Root (Snap'Old, X)
                                    and then X /= A
                                    and then X /= B))

                  --  The other trees come back untouched, cached models
                  --  included.

                  and then (for all X in 1 .. Capacity =>
                              (if Is_Root (Snap'Old, X)
                                  and then X /= A
                                  and then X /= B
                               then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Link one tree under the other and return the root of the result: the
   --  loser becomes the winner's first child, one comparison and four
   --  assignments whatever the two operands hold.

   procedure Fuse
     (A : Slot; Prev : Tree; B : Slot; Rest : Tree; P : out Slot)
     with Pre  => Valid
                  and then In_Use (Snap, A)
                  and then Prev = Links (A).Parent
                  and then Prev /= 0
                  and then B = Links (A).Sibling
                  and then Rest = Links (B).Sibling,
          Post => Valid
                  and then Keys = Snap'Old.Keys
                  and then Chain_Pos = Snap'Old.Chain_Pos
                  and then Free = Snap'Old.Free
                  and then Free_Count = Snap'Old.Free_Count
                  and then In_Use (Snap, P)
                  and then (P = A or else P = B)

                  --  The result stands exactly where A stood: same
                  --  predecessor, successor, size and cached multiset. A
                  --  fusion is invisible from above, so nothing up the list
                  --  has to be repaired.

                  and then Links (P).Parent = Prev
                  and then Links (P).Sibling = Rest
                  and then Links (P).Child /= 0
                  and then Links (P).Size = Snap'Old.Links (A).Size
                  and then Sub (P) = Snap'Old.Sub (A)
                  and then (if Rest /= 0 then Links (Rest).Parent = P)

                  --  The predecessor keeps everything but the one link that
                  --  named A, and which link that is depends on whether A
                  --  headed the list or stood in the middle of it.

                  and then Links (Prev).Parent
                           = Snap'Old.Links (Prev).Parent
                  and then Links (Prev).Size = Snap'Old.Links (Prev).Size
                  and then Sub (Prev) = Snap'Old.Sub (Prev)
                  and then (if Snap'Old.Links (Prev).Child = A
                            then Links (Prev).Child = P
                                 and then Links (Prev).Sibling
                                          = Snap'Old.Links (Prev).Sibling
                            else Links (Prev).Sibling = P
                                 and then Links (Prev).Child
                                          = Snap'Old.Links (Prev).Child)

                  --  Five nodes can change and no others: the two that were
                  --  fused, the one that followed them, the one that preceded
                  --  them, and whichever child of the winner the loser was
                  --  pushed in front of. The last is named by its old parent
                  --  rather than by index, because which of the two won is
                  --  not decided until the keys are compared.

                  and then (for all X in 1 .. Capacity =>
                              (if X /= A
                                  and then X /= B
                                  and then X /= Rest
                                  and then X /= Prev
                                  and then Snap'Old.Links (X).Parent /= A
                                  and then Snap'Old.Links (X).Parent /= B
                               then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Merge a node of a child list with the one after it and put the winner
   --  back in its place. It is one operation rather than a detachment and a
   --  Merge because cutting a list element out would leave its predecessor's
   --  cached model stale, and every node above it too.
   --
   --  A is asked to have a predecessor -- the node the list hangs from if A
   --  heads it, the node before it otherwise -- which is what keeps the four
   --  nodes a fusion touches distinct: a predecessor holds at least one node
   --  more than A does, which rules out a cycle.

   procedure Fold_Children (Root : Slot)
     with Pre  => Valid
                  and then Is_Root (Snap, Root)
                  and then Root /= 0
                  and then Links (Root).Child /= 0,
          Post => Valid
                  and then Keys = Snap'Old.Keys
                  and then Chain_Pos = Snap'Old.Chain_Pos
                  and then Free = Snap'Old.Free
                  and then Free_Count = Snap'Old.Free_Count
                  and then In_Use (Snap, Root)

                  --  One child left, and everything the node claims is what
                  --  it claimed before: no fusion is visible from above, so
                  --  the caller reads the keys off Root as it did before.

                  and then Links (Root).Child /= 0
                  and then Links (Links (Root).Child).Sibling = 0
                  and then Links (Root).Parent = 0
                  and then Links (Root).Sibling = 0
                  and then Links (Root).Size = Snap'Old.Links (Root).Size
                  and then Sub (Root) = Snap'Old.Sub (Root)

                  and then (for all X in 1 .. Capacity =>
                              (if Is_Root (Snap'Old, X) and then X /= Root
                               then Links (X) = Snap'Old.Links (X)
                                    and then Sub (X) = Snap'Old.Sub (X)));
   --  Fold the children of a node into one. Two passes: the first walks the
   --  list from the front fusing disjoint neighbouring pairs, which halves
   --  it; the second walks back from the end fusing the last two over and
   --  over. Folding from the front instead, one accumulator and one fusion
   --  per element, loses the amortized bound, because the accumulator ends up
   --  as one long child list for the next extraction to walk.
   --
   --  The node the list hangs from stays in place throughout, which makes the
   --  model of the fold trivial: Fuse preserves everything above the pair it
   --  fuses, and the root is above all of them, so neither pass carries a
   --  multiset of its own.
   --
   --  The passes are loops rather than recursion because a root that has
   --  taken n insertions has n children, and a recursion n / 2 deep
   --  overflows the stack at the sizes this arena is for.
   --
   --  The node is asked to be a tree rather than any node with children: a
   --  node with no parent and no sibling is one no list element can be, so
   --  every node the fold walks over is distinct from it for free.

   --------------
   -- Allocate --
   --------------

   procedure Allocate (I : out Slot; K : Key_Type) is
      Before : constant Snapshot := Snap with Ghost;
      Head   : constant Slot := Free;
      Next   : constant Tree := Links (Head).Child;
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
      Links (Head) := (Child => 0, Sibling => 0, Parent => 0, Size => 1);
      Sub (Head) := KM.Add (KM.Empty_Multiset, K);

      --  Nothing in use pointed at the head, because a free node's Child is a
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
      Links (I).Child  := Free;
      Free_Count       := Free_Count + 1;
      Chain_Pos (I)    := Free_Count;
      Chain_At (Free_Count) := I;
      Free             := I;

      --  I was in use, so no free node's Child named it and it is genuinely a
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
      --  The ghost arrays are aggregates rather than loops: an iterated
      --  component association defines every element directly, leaving
      --  nothing for a loop invariant to carry. They are erased at run time,
      --  so the form costs nothing there.

      Chain_Pos := [for J in 1 .. Capacity => J];
      Chain_At  := [for J in 1 .. Capacity => J];
      Sub       := [for J in 1 .. Capacity => KM.Empty_Multiset];

      --  Links is real, and there the same form is not free: the aggregate
      --  is built as a whole-array temporary, which overflows an ordinary
      --  stack at these sizes. So it is written slot by slot.

      for I in 1 .. Capacity loop
         Links (I) :=
           (Child   => (if I = 1 then 0 else I - 1),
            Sibling => 0,
            Parent  => 0,
            Size    => 0);

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Links (J) = (Child   => (if J = 1 then 0 else J - 1),
                           Sibling => 0,
                           Parent  => 0,
                           Size    => 0));
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
            then Links (I).Child = 0
            else Links (I).Child /= 0
                 and then Chain_Pos (Links (I).Child) = Chain_Pos (I) - 1));
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
      Before : constant Snapshot := Snap with Ghost;

      Top  : Slot;
      --  The winner, which keeps its root

      Loser : Slot;
      --  The other one, which becomes the winner's first child

      Kid : Tree;
      --  What the winner's first child was, and what the loser's next
      --  sibling becomes

      --  The two multisets the result is built out of, named before anything
      --  moves: what hung below the loser, and what hung below the winner.

      Below_Loser : KM.Multiset with Ghost;
      Below_Top   : KM.Multiset with Ghost;
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
         Loser := B;
      else
         Top := B;
         Loser := A;
      end if;

      Kid := Links (Top).Child;

      Below_Loser := Sub_Now (Links (Loser).Child);
      Below_Top   := Sub_Now (Kid);

      Models.Lemma_Sum_Empty (Below_Loser);
      Models.Lemma_Sum_Empty (Below_Top);

      pragma Assert (Sub (Top) = KM.Add (Below_Top, Keys (Top)));
      pragma Assert (Sub (Loser) = KM.Add (Below_Loser, Keys (Loser)));

      --  Splice the loser in at the head of the winner's child list. The
      --  loser keeps everything below it and gains a sibling; the winner
      --  keeps everything it had and gains a child. Both cached models
      --  therefore change, and both are rewritten from their links by the
      --  same expression that defines them.

      if Kid /= 0 then
         Links (Kid).Parent := Loser;
      end if;

      Links (Loser).Sibling := Kid;
      Links (Loser).Parent := Top;
      Links (Loser).Size :=
        1 + Size_Now (Links (Loser).Child) + Size_Now (Kid);
      Sub (Loser) :=
        KM.Add (KM.Sum (Sub_Now (Links (Loser).Child), Sub_Now (Kid)),
                Keys (Loser));

      Links (Top).Child := Loser;
      Links (Top).Size := 1 + Size_Now (Loser);
      Sub (Top) := KM.Add (KM.Sum (Sub_Now (Loser), KM.Empty_Multiset),
                           Keys (Top));

      R := Top;

      --  Re-establishing the invariant, one node at a time. Only the winner
      --  changed in a way the ordering clause can see: what it dominates is
      --  now the loser's whole cache, whose parts are the loser's key, which
      --  lost the comparison; what hung below the loser, which the loser
      --  dominated; and the old child's cache, which the winner dominated.

      pragma Assert
        (for all E of Sub_Now (Links (Loser).Child) => Keys (Loser) <= E);
      pragma Assert (for all E of Sub_Of (Before, Kid) => Keys (Top) <= E);
      pragma Assert (for all E of Sub_Now (Loser) => Keys (Top) <= E);

      pragma Assert (Node_In_Use (Snap, Loser));
      pragma Assert (Node_In_Use (Snap, Top));
      pragma Assert (if Kid /= 0 then Node_In_Use (Snap, Kid));

      --  Nothing untouched named either moved node: the loser was a tree, so
      --  nothing pointed at it, and only the winner named the old child.

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if In_Use (Snap, X)
               and then X /= Top
               and then X /= Loser
               and then X /= Kid
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then Node_In_Use (Snap, X)));
      pragma Assert (Nodes_Sound (Snap));

      --  The model of the result. The winner's new cache is its key over the
      --  loser's, which is the loser's key over what hung below each; the sum
      --  of the two old caches is the same keys and multisets in another
      --  order. What follows is that reassociation, one law per step.

      Models.Lemma_Sum_Empty (Sub_Now (Loser));

      pragma Assert
        (Sub_Now (R)
         = KM.Add (KM.Add (KM.Sum (Below_Loser, Below_Top), Keys (Loser)),
                   Keys (Top)));

      Models.Lemma_Sum_Symmetric (Below_Loser, Below_Top);
      Models.Lemma_Add_Congruent
        (KM.Sum (Below_Loser, Below_Top),
         KM.Sum (Below_Top, Below_Loser),
         Keys (Loser));
      Models.Lemma_Add_Congruent
        (KM.Add (KM.Sum (Below_Loser, Below_Top), Keys (Loser)),
         KM.Add (KM.Sum (Below_Top, Below_Loser), Keys (Loser)),
         Keys (Top));
      Models.Lemma_Add_Commutes
        (KM.Sum (Below_Top, Below_Loser), Keys (Loser), Keys (Top));

      pragma Assert
        (Sub_Now (R)
         = KM.Add (KM.Add (KM.Sum (Below_Top, Below_Loser), Keys (Top)),
                   Keys (Loser)));

      --  And the other side: the sum of the two operands as they were.

      Models.Lemma_Sum_Add
        (KM.Add (Below_Top, Keys (Top)), Below_Loser, Keys (Loser));
      Models.Lemma_Sum_Add_Left (Below_Top, Below_Loser, Keys (Top));
      Models.Lemma_Add_Congruent
        (KM.Sum (KM.Add (Below_Top, Keys (Top)), Below_Loser),
         KM.Add (KM.Sum (Below_Top, Below_Loser), Keys (Top)),
         Keys (Loser));

      pragma Assert
        (KM.Sum (Sub_Of (Before, Top), Sub_Of (Before, Loser))
         = KM.Add (KM.Add (KM.Sum (Below_Top, Below_Loser), Keys (Top)),
                   Keys (Loser)));

      --  Which of the two operands won the comparison is immaterial to the
      --  sum, and this is the only place that has to say so.

      Models.Lemma_Sum_Symmetric (Sub_Of (Before, Top), Sub_Of (Before, Loser));

   end Merge;

   ----------
   -- Fuse --
   ----------

   procedure Fuse
     (A : Slot; Prev : Tree; B : Slot; Rest : Tree; P : out Slot)
   is
      Before : constant Snapshot := Snap with Ghost;

      Top   : Slot;
      Loser : Slot;
      Kid   : Tree;

      --  What hangs below each of the two and what follows them. The result
      --  holds these three and the two keys, and so did A before the call;
      --  the algebra at the end is the reordering between the two.

      Below_Top   : KM.Multiset with Ghost;
      Below_Loser : KM.Multiset with Ghost;
      Tail_Of     : KM.Multiset with Ghost;
   begin
      --  The sizes of the four nodes involved, which is what says a list
      --  cannot bite its own tail: any two of them naming each other would
      --  have to hold one more node than they hold.

      pragma Assert
        (Links (A).Size
         = 1 + Size_Now (Links (A).Child) + Links (B).Size);
      pragma Assert
        (Links (B).Size
         = 1 + Size_Now (Links (B).Child) + Size_Now (Rest));
      pragma Assert
        (if Rest /= 0
         then Links (Rest).Size
              = 1 + Size_Now (Links (Rest).Child)
                  + Size_Now (Links (Rest).Sibling));
      pragma Assert
        (Links (Prev).Size
         = 1 + Size_Now (Links (Prev).Child)
             + Size_Now (Links (Prev).Sibling));

      --  A is one of the predecessor's two links, so the predecessor holds
      --  at least one node more than A does. That, with the two equations
      --  above, is what closes every cycle the four of them could form.

      pragma Assert (Links (Prev).Size >= 1 + Links (A).Size);

      pragma Assert (A /= B);
      pragma Assert (Rest /= A and then Rest /= B);
      pragma Assert (Prev /= A and then Prev /= B and then Prev /= Rest);

      if Keys (A) <= Keys (B) then
         Top := A;
         Loser := B;
      else
         Top := B;
         Loser := A;
      end if;

      Kid := Links (Top).Child;

      pragma Assert
        (Links (Top).Size
         = 1 + Size_Now (Kid) + Size_Now (Links (Top).Sibling));
      pragma Assert (if Kid /= 0 then Links (Kid).Parent = Top);
      pragma Assert (if Rest /= 0 then Links (Rest).Parent = B);
      pragma Assert
        (if Links (Loser).Child /= 0
         then Links (Links (Loser).Child).Parent = Loser);
      pragma Assert (if Kid /= 0 then Kid /= Links (Top).Sibling);
      pragma Assert (Kid /= A and then Kid /= B);

      --  The winner's old child and the node after the pair are children of
      --  different nodes, or -- when the winner is the second of the pair --
      --  the two links of the winner itself, which the invariant keeps apart.

      if Top = A then
         pragma Assert (Kid = 0 or else Links (Kid).Parent = A);
         pragma Assert (Rest = 0 or else Links (Rest).Parent = B);
      else
         pragma Assert (Links (Top).Sibling = Rest);
      end if;

      pragma Assert (if Kid /= 0 then Kid /= Rest);
      pragma Assert (Kid /= Prev);
      pragma Assert
        (if Links (Loser).Child /= 0 then Links (Loser).Child /= Kid);

      Below_Top   := Sub_Now (Kid);
      Below_Loser := Sub_Now (Links (Loser).Child);
      Tail_Of     := Sub_Now (Rest);

      Models.Lemma_Sum_Empty (Below_Top);
      Models.Lemma_Sum_Empty (Below_Loser);

      --  How the list held these three multisets and two keys before the
      --  fusion, which is what the result has to hold after it.

      pragma Assert
        (Before.Sub (B)
         = KM.Add (KM.Sum (Sub_Of (Before, Before.Links (B).Child), Tail_Of),
                   Keys (B)));
      pragma Assert
        (Before.Sub (A)
         = KM.Add (KM.Sum (Sub_Of (Before, Before.Links (A).Child),
                           Before.Sub (B)),
                   Keys (A)));

      --  The loser becomes the winner's first child, in front of whatever
      --  child the winner had.

      if Kid /= 0 then
         Links (Kid).Parent := Loser;
      end if;

      Links (Loser).Sibling := Kid;
      Links (Loser).Parent := Top;
      Links (Loser).Size :=
        1 + Size_Now (Links (Loser).Child) + Size_Now (Kid);
      Sub (Loser) :=
        KM.Add (KM.Sum (Sub_Now (Links (Loser).Child), Sub_Now (Kid)),
                Keys (Loser));

      --  And the winner takes the place in the list that A held.

      Links (Top).Child := Loser;
      Links (Top).Sibling := Rest;
      Links (Top).Parent := Prev;

      if Rest /= 0 then
         Links (Rest).Parent := Top;
      end if;

      if Links (Prev).Child = A then
         Links (Prev).Child := Top;
      else
         Links (Prev).Sibling := Top;
      end if;

      Links (Top).Size := 1 + Size_Now (Loser) + Size_Now (Rest);
      Sub (Top) := KM.Add (KM.Sum (Sub_Now (Loser), Sub_Now (Rest)),
                           Keys (Top));

      P := Top;

      --  The result holds what A held: the same three subtrees and the same
      --  two nodes, counted in a different order.

      pragma Assert
        (Links (P).Size
         = 2 + Size_Now (Links (Loser).Child) + Size_Now (Kid)
             + Size_Now (Rest));
      pragma Assert (Links (P).Size = Before.Links (A).Size);

      --  The model first, because the predecessor's clauses are stated in
      --  terms of the result's cache and cannot be re-established until it is
      --  known to be what it was.

      pragma Assert
        (Sub (P) = KM.Add (KM.Sum (KM.Add (KM.Sum (Below_Loser, Below_Top),
                                           Keys (Loser)),
                                   Tail_Of),
                           Keys (Top)));

      Models.Lemma_Sum_Add_Left
        (KM.Sum (Below_Loser, Below_Top), Tail_Of, Keys (Loser));
      Models.Lemma_Add_Congruent
        (KM.Sum (KM.Add (KM.Sum (Below_Loser, Below_Top), Keys (Loser)),
                 Tail_Of),
         KM.Add (KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
                 Keys (Loser)),
         Keys (Top));

      pragma Assert
        (Sub (P)
         = KM.Add (KM.Add (KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
                           Keys (Loser)),
                   Keys (Top)));

      if Top = A then

         --  A won: what the list held at A is A's key over its old child's
         --  cache and over B's, and B's is B's key over its own child's cache
         --  and the tail.

         pragma Assert
           (Before.Sub (A)
            = KM.Add (KM.Sum (Below_Top,
                              KM.Add (KM.Sum (Below_Loser, Tail_Of),
                                      Keys (Loser))),
                      Keys (Top)));

         Models.Lemma_Sum_Add
           (Below_Top, KM.Sum (Below_Loser, Tail_Of), Keys (Loser));
         Models.Lemma_Sum_Assoc (Below_Top, Below_Loser, Tail_Of);
         Models.Lemma_Sum_Symmetric (Below_Top, Below_Loser);
         Models.Lemma_Sum_Congruent
           (KM.Sum (Below_Top, Below_Loser),
            KM.Sum (Below_Loser, Below_Top),
            Tail_Of);
         Models.Lemma_Add_Congruent
           (KM.Sum (Below_Top, KM.Sum (Below_Loser, Tail_Of)),
            KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
            Keys (Loser));
         Models.Lemma_Add_Congruent
           (KM.Sum (Below_Top, KM.Add (KM.Sum (Below_Loser, Tail_Of),
                                       Keys (Loser))),
            KM.Add (KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
                    Keys (Loser)),
            Keys (Top));
      else

         --  B won, and A is the loser: what the list held at A is A's key over
         --  its own child's cache and over B's.

         pragma Assert
           (Before.Sub (A)
            = KM.Add (KM.Sum (Below_Loser,
                              KM.Add (KM.Sum (Below_Top, Tail_Of),
                                      Keys (Top))),
                      Keys (Loser)));

         Models.Lemma_Sum_Add
           (Below_Loser, KM.Sum (Below_Top, Tail_Of), Keys (Top));
         Models.Lemma_Sum_Assoc (Below_Loser, Below_Top, Tail_Of);
         Models.Lemma_Add_Congruent
           (KM.Sum (Below_Loser, KM.Sum (Below_Top, Tail_Of)),
            KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
            Keys (Top));
         Models.Lemma_Add_Congruent
           (KM.Sum (Below_Loser, KM.Add (KM.Sum (Below_Top, Tail_Of),
                                         Keys (Top))),
            KM.Add (KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
                    Keys (Top)),
            Keys (Loser));
         Models.Lemma_Add_Commutes
           (KM.Sum (KM.Sum (Below_Loser, Below_Top), Tail_Of),
            Keys (Top),
            Keys (Loser));
      end if;

      pragma Assert (Sub (P) = Before.Sub (A));

      --  And now the invariant, node by node. Only one clause is more than
      --  reading back an assignment: what the winner dominates is the loser's
      --  whole cache, whose parts are the loser's key, which lost the
      --  comparison; what hung below the loser; and the old child's cache.

      pragma Assert (for all E of Below_Loser => Keys (Loser) <= E);
      pragma Assert (for all E of Below_Top => Keys (Top) <= E);
      pragma Assert (for all E of Sub_Now (Loser) => Keys (Top) <= E);

      pragma Assert (Node_In_Use (Snap, Loser));
      pragma Assert (Node_In_Use (Snap, Top));
      pragma Assert (if Kid /= 0 then Node_In_Use (Snap, Kid));
      pragma Assert (if Rest /= 0 then Node_In_Use (Snap, Rest));
      pragma Assert (Node_In_Use (Snap, Prev));

      pragma Assert
        (for all X in 1 .. Capacity =>
           (if X /= A
               and then X /= B
               and then X /= Rest
               and then X /= Prev
               and then Before.Links (X).Parent /= A
               and then Before.Links (X).Parent /= B
            then Links (X) = Before.Links (X)
                 and then Sub (X) = Before.Sub (X)
                 and then (if In_Use (Snap, X) then Node_In_Use (Snap, X))));
      pragma Assert (Nodes_Sound (Snap));
   end Fuse;

   --------------------
   -- Fold_Children  --
   --------------------

   procedure Fold_Children (Root : Slot) is
      Entry_State : constant Snapshot := Snap with Ghost;

      Depth : Chain_Array (1 .. Capacity) := [others => 0] with Ghost;
      --  How far along the list a node stands, counting the first child as
      --  one, and 0 for a node not on the list the first pass has built. A
      --  value decreasing by one from a node to its predecessor is what lets
      --  the second pass walk back up without a reachability relation, and
      --  what says the walk ends at Root. Ghost, so it costs nothing at run
      --  time.

      Total : constant Extended_Index := Size_Now (Links (Root).Child)
        with Ghost;
      --  How many nodes the list holds altogether. Every fusion takes two
      --  nodes off the front of what is left and puts one back, so this is
      --  what bounds the number of them.

      Rank : Extended_Index := 0 with Ghost;
      --  How many nodes the first pass has placed

      Prev : Tree := 0;
      --  The last node the first pass placed; 0 while it has placed none, in
      --  which case the node before Cur is Root itself.

      Cur  : Tree := Links (Root).Child;
      Next : Tree;
      P    : Slot;
   begin
      --  First pass: fuse neighbouring pairs, front to back.

      while Cur /= 0 and then Links (Cur).Sibling /= 0 loop
         pragma Loop_Invariant (Valid);
         pragma Loop_Invariant (Keys = Entry_State.Keys);
         pragma Loop_Invariant (Chain_Pos = Entry_State.Chain_Pos);
         pragma Loop_Invariant (Free = Entry_State.Free);
         pragma Loop_Invariant (Free_Count = Entry_State.Free_Count);
         pragma Loop_Invariant (In_Use (Snap, Root));
         pragma Loop_Invariant
           (Links (Root).Parent = 0
            and then Links (Root).Sibling = 0
            and then Links (Root).Size = Entry_State.Links (Root).Size
            and then Sub (Root) = Entry_State.Sub (Root)
            and then Links (Root).Child /= 0);
         pragma Loop_Invariant (In_Use (Snap, Cur));
         pragma Loop_Invariant
           (if Prev = 0
            then Links (Cur).Parent = Root
                 and then Links (Root).Child = Cur
                 and then Rank = 0
            else In_Use (Snap, Prev)
                 and then Links (Cur).Parent = Prev
                 and then Links (Prev).Sibling = Cur
                 and then Depth (Prev) = Rank
                 and then Rank >= 1);
         pragma Loop_Invariant (2 * Rank + Size_Now (Cur) <= Total);
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Depth (X) /= 0
               then In_Use (Snap, X)
                    and then Depth (X) <= Rank
                    and then Links (X).Parent /= 0
                    and then (if Depth (X) = 1
                              then Links (X).Parent = Root
                                   and then Links (Root).Child = X
                              else Links (Links (X).Parent).Sibling = X
                                   and then Depth (Links (X).Parent)
                                            = Depth (X) - 1)));
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Is_Root (Entry_State, X) and then X /= Root
               then Links (X) = Entry_State.Links (X)
                    and then Sub (X) = Entry_State.Sub (X)));
         pragma Loop_Variant (Decreases => Size_Now (Cur));

         Next := Links (Links (Cur).Sibling).Sibling;

         --  Nothing the fusion touches is on the list already. A node on the
         --  list stands one deeper than its predecessor and no deeper than
         --  the last node placed, and each of these stands one past that --
         --  which is one too far.

         pragma Assert
           (for all X in 1 .. Capacity =>
              (if Depth (X) /= 0
               then X /= Cur
                    and then X /= Links (Cur).Sibling
                    and then X /= Next
                    and then Links (X).Parent /= Cur
                    and then Links (X).Parent /= Links (Cur).Sibling));

         Fuse (Cur, Links (Cur).Parent, Links (Cur).Sibling, Next, P);

         --  The fusion put one node back where two came off, so what is left
         --  of the list is at least two nodes shorter.

         pragma Assert (Links (P).Child /= 0);
         pragma Assert (Links (P).Size >= 2 + Size_Now (Next));

         Rank := Rank + 1;
         Depth (P) := Rank;

         Prev := P;
         Cur := Next;
      end loop;

      --  What the pass leaves is a list of half the length. Its last node is
      --  the odd one out if there was one, and the last fusion's result
      --  otherwise; either way the second pass starts there.

      if Cur /= 0 then
         pragma Assert (2 * Rank + 1 <= Total);
         Rank := Rank + 1;
         Depth (Cur) := Rank;
      else
         Cur := Prev;
      end if;

      pragma Assert (Cur /= 0);
      pragma Assert (Links (Cur).Sibling = 0);
      pragma Assert (Depth (Cur) = Rank and then Rank >= 1);

      --  Second pass: fuse the last two over and over, walking back up the
      --  list by the link that names each node's predecessor.

      while Links (Cur).Parent /= Root loop
         pragma Loop_Invariant (Valid);
         pragma Loop_Invariant (Keys = Entry_State.Keys);
         pragma Loop_Invariant (Chain_Pos = Entry_State.Chain_Pos);
         pragma Loop_Invariant (Free = Entry_State.Free);
         pragma Loop_Invariant (Free_Count = Entry_State.Free_Count);
         pragma Loop_Invariant (In_Use (Snap, Root));
         pragma Loop_Invariant
           (Links (Root).Parent = 0
            and then Links (Root).Sibling = 0
            and then Links (Root).Size = Entry_State.Links (Root).Size
            and then Sub (Root) = Entry_State.Sub (Root)
            and then Links (Root).Child /= 0);
         pragma Loop_Invariant (In_Use (Snap, Cur));
         pragma Loop_Invariant (Links (Cur).Sibling = 0);
         pragma Loop_Invariant (Cur /= 0);
         pragma Loop_Invariant (Depth (Cur) /= 0);
         pragma Loop_Invariant (Links (Cur).Parent /= 0);
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Depth (X) /= 0
               then In_Use (Snap, X)
                    and then Links (X).Parent /= 0
                    and then (if Depth (X) = 1
                              then Links (X).Parent = Root
                                   and then Links (Root).Child = X
                              else Links (Links (X).Parent).Sibling = X
                                   and then Depth (Links (X).Parent)
                                            = Depth (X) - 1)));
         pragma Loop_Invariant
           (for all X in 1 .. Capacity =>
              (if Is_Root (Entry_State, X) and then X /= Root
               then Links (X) = Entry_State.Links (X)
                    and then Sub (X) = Entry_State.Sub (X)));
         pragma Loop_Variant (Decreases => Depth (Cur));

         --  Cur is not the first child, so it stands at least two along the
         --  list and the node before it is on the list too.

         pragma Assert (Depth (Cur) >= 2);

         declare
            Above : constant Slot := Links (Cur).Parent;
            Rung  : constant Extended_Index := Depth (Above) with Ghost;
         begin
            pragma Assert (Links (Above).Sibling = Cur);
            pragma Assert
              (for all X in 1 .. Capacity =>
                 (if Depth (X) /= 0 and then Depth (X) < Rung
                  then X /= Above
                       and then X /= Cur
                       and then Links (X).Parent /= Above
                       and then Links (X).Parent /= Cur));

            Fuse (Above, Links (Above).Parent, Cur, 0, P);

            Depth (Cur) := 0;
            Depth (Above) := 0;
            Depth (P) := Rung;

            Cur := P;
         end;
      end loop;

      pragma Assert (Depth (Cur) = 1);
      pragma Assert (Links (Root).Child = Cur);
   end Fold_Children;

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
      New_Root : Tree;
   begin
      K := Keys (Gone);

      --  Fold the children while the root is still there. It is released
      --  below, and until then it is what holds the list together and what
      --  the fold's model postcondition is stated about: no key leaves the
      --  tree until its root does.

      if Links (Gone).Child /= 0 then
         Fold_Children (Gone);
      end if;

      New_Root := Links (Gone).Child;

      if New_Root /= 0 then
         Links (New_Root).Parent := 0;
      end if;

      --  Cutting the child off leaves Gone a one-node tree, so its size and
      --  its cached model have to say so: a node still in use whose Size were
      --  0, or whose model did not match its key, would make the arena
      --  invalid between here and the release below.

      Links (Gone) := (Child => 0, Sibling => 0, Parent => 0, Size => 1);
      Sub (Gone) := KM.Add (KM.Empty_Multiset, Keys (Gone));

      Deallocate (Gone);

      T := New_Root;

      Models.Lemma_Sum_Empty (Sub_Now (New_Root));
   end Extract_Min;

end Heaps.Pairing;
