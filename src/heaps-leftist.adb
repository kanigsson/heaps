--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The ghost model of these units -- a functional multiset built by recursion
--  over the key array -- cannot reasonably be evaluated at run time: doing so
--  would turn every O(log n) operation into a quadratic one. Since the
--  contracts are discharged by proof, run-time checking of them is redundant,
--  so assertions are disabled here whatever the compilation switches say.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Leftist with SPARK_Mode is

   procedure Merge
     (H : in out Heap; A, B : Extended_Index; R : out Extended_Index)
     with Pre  => Well_Linked (H)
                  and then A <= H.Count
                  and then B <= H.Count
                  and then (if A /= 0 then H.Links (A).Parent = 0)
                  and then (if B /= 0 then H.Links (B).Parent = 0)
                  and then (if A /= 0 and then B /= 0 then A /= B)
                  and then Size_Of (H, A) + Size_Of (H, B) <= H.Count,
          Post => Well_Linked (H)
                  and then H.Count = H.Count'Old
                  and then H.Keys = H.Keys'Old
                  and then H.Root = H.Root'Old
                  and then R <= H.Count
                  and then (if A = 0 then R = B
                            elsif B = 0 then R = A
                            else R = A or else R = B)
                  and then (if R /= 0
                            then H.Links (R).Parent = 0
                                 and then H.Links (R).Size
                                          = Size_Of (H'Old, A)
                                            + Size_Of (H'Old, B))

                  --  A merge does not leave any tree without a root that did
                  --  not have one already: the two it was given become one.

                  and then (for all X in 1 .. H.Count =>
                              (if H.Links (X).Parent = 0 and then X /= R
                               then H'Old.Links (X).Parent = 0
                                    and then X /= A
                                    and then X /= B))

                  --  And it leaves the other trees of the forest alone

                  and then (for all X in 1 .. H.Count =>
                              (if H'Old.Links (X).Parent = 0
                                  and then X /= A
                                  and then X /= B
                               then H.Links (X) = H'Old.Links (X))),
          Subprogram_Variant =>
            (Decreases => Size_Of (H, A) + Size_Of (H, B));
   --  Merge the two trees rooted at A and B into one, and return its root.
   --  Everything the operations do to the shape of the pool happens here.

   -----------
   -- Merge --
   -----------

   procedure Merge
     (H : in out Heap; A, B : Extended_Index; R : out Extended_Index)
   is
      Top   : Index;
      Other : Index;
      Rest  : Extended_Index;
      Sub   : Extended_Index;
      Swap  : Extended_Index;
   begin
      if A = 0 or else B = 0 then
         R := (if A = 0 then B else A);

         pragma Assert (Well_Linked (H));
         return;
      end if;

      --  The smaller of the two roots is the root of the result

      if H.Keys (A) <= H.Keys (B) then
         Top := A;
         Other := B;
      else
         Top := B;
         Other := A;
      end if;

      --  Detach the right subtree of Top. Doing so before the recursive call
      --  rather than after it keeps the pool a well-formed forest throughout:
      --  Top is left a smaller but perfectly valid tree, and the subtree that
      --  has just left it becomes a tree of its own.

      Rest := H.Links (Top).Right;

      if Rest /= 0 then
         H.Links (Rest).Parent := 0;
      end if;

      H.Links (Top).Right := 0;
      H.Links (Top).Size := 1 + Size_Of (H, H.Links (Top).Left);
      H.Links (Top).Dist := 1;

      Merge (H, Rest, Other, Sub);

      --  Top was a tree of its own across the call, so the merge left it
      --  alone, and what it says about its left subtree still holds.

      pragma Assert (Sub /= 0 and then Sub /= Top);
      pragma Assert (H.Links (Sub).Parent = 0);
      pragma Assert (H.Links (Top).Left /= Sub);

      H.Links (Sub).Parent := Top;
      H.Links (Top).Right := Sub;

      --  Restore the leftist condition by putting the deeper subtree on the
      --  left, then say what the node has become.

      if Dist_Of (H, H.Links (Top).Left) < Dist_Of (H, H.Links (Top).Right)
      then
         Swap := H.Links (Top).Left;
         H.Links (Top).Left := H.Links (Top).Right;
         H.Links (Top).Right := Swap;
      end if;

      pragma Assert
        (Dist_Of (H, H.Links (Top).Right)
         <= Size_Of (H, H.Links (Top).Right));

      H.Links (Top).Size :=
        1 + Size_Of (H, H.Links (Top).Left) + Size_Of (H, H.Links (Top).Right);
      H.Links (Top).Dist := 1 + Dist_Of (H, H.Links (Top).Right);

      pragma Assert (H.Links (Top).Dist <= H.Links (Top).Size);
      pragma Assert (Well_Linked (H));

      R := Top;
   end Merge;

   -----------------
   -- Lemma_Above --
   -----------------

   procedure Lemma_Above (H : Heap; I : Index)
     with Ghost,
          Pre  => Is_Heap (H) and then I <= H.Count,
          Post => H.Keys (H.Root) <= H.Keys (I),
          Subprogram_Variant => (Increases => H.Links (I).Size);
   --  Walk up the parent links from I. Each step meets a key no larger than
   --  the one below it and a strictly larger subtree, so the walk cannot
   --  cycle and ends at the only node without a parent.

   procedure Lemma_Above (H : Heap; I : Index) is
   begin
      if I /= H.Root then
         Lemma_Above (H, H.Links (I).Parent);
      end if;
   end Lemma_Above;

   ---------------------------
   -- Lemma_Root_Is_Minimum --
   ---------------------------

   procedure Lemma_Root_Is_Minimum (H : Heap) is
   begin
      for I in 1 .. H.Count loop
         Lemma_Above (H, I);

         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (H.Root) <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   ------------
   -- Min_Of --
   ------------

   function Min_Of (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Count loop
         if H.Keys (I) < Result then
            Result := H.Keys (I);
         end if;

         pragma Loop_Invariant (for all J in 1 .. I => Result <= H.Keys (J));
         pragma Loop_Invariant (for some J in 1 .. I => Result = H.Keys (J));
      end loop;

      return Result;
   end Min_Of;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Count := 0;
      H.Root := 0;
   end Clear;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Old_Keys : constant Key_Array := H.Keys with Ghost;

      Slot     : constant Index := H.Count + 1;
      Before   : constant Extended_Index := H.Root;
      New_Root : Extended_Index;
   begin
      --  A one-node heap is appended to the pool and then merged in. Since
      --  the used slots are a prefix, the model simply gains the key.

      H.Count := Slot;
      H.Keys (Slot) := K;
      H.Links (Slot) :=
        (Left => 0, Right => 0, Parent => 0, Size => 1, Dist => 1);

      Models.Lemma_Same_Prefix (Old_Keys, H.Keys, Slot - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Old_Keys, Slot - 1),
         Models.Occurrences (H.Keys, Slot - 1), K);

      pragma Assert (Size_Of (H, Before) = Slot - 1);

      Merge (H, Before, Slot, New_Root);
      H.Root := New_Root;

      pragma Assert (H.Links (New_Root).Size = H.Count);

      Models.Lemma_Same_Prefix (Old_Keys, H.Keys, Slot - 1);
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Old_Keys : constant Key_Array := H.Keys with Ghost;
      Cut_Keys : Key_Array := H.Keys with Ghost;

      Gone : constant Index := H.Root;
      Last : constant Index := H.Count;

      Left_Sub  : Extended_Index := H.Links (Gone).Left;
      Right_Sub : Extended_Index := H.Links (Gone).Right;

      New_Root : Extended_Index;
   begin
      Lemma_Root_Is_Minimum (H);
      K := H.Keys (Gone);

      pragma Assert
        (Size_Of (H, Left_Sub) + Size_Of (H, Right_Sub) = Last - 1);

      --  Cut the two subtrees loose and leave the old root a lone node, so
      --  that moving it out of the pool below disturbs nothing.

      if Left_Sub /= 0 then
         H.Links (Left_Sub).Parent := 0;
      end if;

      if Right_Sub /= 0 then
         H.Links (Right_Sub).Parent := 0;
      end if;

      H.Links (Gone) :=
        (Left => 0, Right => 0, Parent => 0, Size => 1, Dist => 1);

      pragma Assert
        (for all I in 1 .. Last =>
           (if I /= Gone then H.Links (I).Parent /= Gone));
      pragma Assert
        (for all I in 1 .. Last =>
           H.Links (I).Left <= Last
           and then H.Links (I).Right <= Last
           and then H.Links (I).Parent <= Last);
      pragma Assert
        (for all I in 1 .. Last =>
           (if H.Links (I).Parent = 0
            then I = Gone or else I = Left_Sub or else I = Right_Sub));

      --  Fill the hole with the last node of the pool and tell its three
      --  neighbours where it went, which is what keeps the used slots a
      --  prefix and the model a plain scan.

      if Gone /= Last then
         declare
            Mid   : constant Heap := H with Ghost;
            Kid_L : constant Extended_Index := H.Links (Last).Left;
            Kid_R : constant Extended_Index := H.Links (Last).Right;
            Up    : constant Extended_Index := H.Links (Last).Parent;
         begin
            --  Only the parent and the children of the last node refer to
            --  it, which is why telling those three is enough.

            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Up
                  then H.Links (I).Left /= Last
                       and then H.Links (I).Right /= Last));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Kid_L and then I /= Kid_R
                  then H.Links (I).Parent /= Last));
            pragma Assert (Kid_L /= Gone and then Kid_R /= Gone);
            pragma Assert (Kid_L /= Last and then Kid_R /= Last);
            pragma Assert (Up /= Gone and then Up /= Last);

            H.Keys (Gone) := H.Keys (Last);
            H.Links (Gone) := H.Links (Last);

            if Kid_L /= 0 then
               H.Links (Kid_L).Parent := Gone;
            end if;

            if Kid_R /= 0 then
               H.Links (Kid_R).Parent := Gone;
            end if;

            if Up /= 0 then
               pragma Assert
                 (H.Links (Up).Left = Last or else H.Links (Up).Right = Last);

               if H.Links (Up).Left = Last then
                  H.Links (Up).Left := Gone;
               else
                  H.Links (Up).Right := Gone;
               end if;
            end if;

            pragma Assert
              (if Up /= 0
               then H.Links (Up).Left
                    = (if Mid.Links (Up).Left = Last
                       then Gone else Mid.Links (Up).Left)
                    and then H.Links (Up).Right
                             = (if Mid.Links (Up).Right = Last
                                then Gone else Mid.Links (Up).Right));

            --  What is left in the last slot is now a duplicate of what sits
            --  in the hole, so empty it before it leaves the pool.

            H.Links (Last) :=
              (Left => 0, Right => 0, Parent => 0, Size => 1, Dist => 1);

            if Left_Sub = Last then
               Left_Sub := Gone;
            end if;

            if Right_Sub = Last then
               Right_Sub := Gone;
            end if;

            --  Nothing but the moved node and its three neighbours changed

            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                     and then I /= Kid_L and then I /= Kid_R
                  then H.Links (I) = Mid.Links (I)));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last
                  then H.Links (I).Size = Mid.Links (I).Size
                       and then H.Links (I).Dist = Mid.Links (I).Dist));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                  then H.Links (I).Left = Mid.Links (I).Left
                       and then H.Links (I).Right = Mid.Links (I).Right));
            pragma Assert (H.Links (Gone) = Mid.Links (Last));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                  then H.Links (I).Left /= Gone
                       and then H.Links (I).Right /= Gone
                       and then H.Links (I).Left /= Last
                       and then H.Links (I).Right /= Last));

            --  The only subtree sizes and depths that moved are the two the
            --  node did

            pragma Assert
              (for all X in 0 .. Last =>
                 (if X /= Gone and then X /= Last
                  then Size_Of (H, X) = Size_Of (Mid, X)
                       and then Dist_Of (H, X) = Dist_Of (Mid, X)));
            pragma Assert
              (Size_Of (H, Gone) = Size_Of (Mid, Last)
               and then Dist_Of (H, Gone) = Dist_Of (Mid, Last));
            pragma Assert
              (H.Links (Gone).Size
               = 1 + Size_Of (H, Kid_L) + Size_Of (H, Kid_R));
            pragma Assert
              (if Up /= 0
               then Mid.Links (Up).Left /= Gone
                    and then Mid.Links (Up).Right /= Gone);
            pragma Assert
              (if Up /= 0
               then Size_Of (H, H.Links (Up).Left)
                    = Size_Of (Mid, Mid.Links (Up).Left)
                    and then Size_Of (H, H.Links (Up).Right)
                             = Size_Of (Mid, Mid.Links (Up).Right));
            pragma Assert
              (if Up /= 0
               then Dist_Of (H, H.Links (Up).Left)
                    = Dist_Of (Mid, Mid.Links (Up).Left)
                    and then Dist_Of (H, H.Links (Up).Right)
                             = Dist_Of (Mid, Mid.Links (Up).Right));

            Models.Lemma_Set (Old_Keys, H.Keys, Gone, Last - 1);

            --  The three nodes the move touched, one at a time, and then
            --  everything else, which the move left where it was

            pragma Assert
              (H.Links (Last).Size
               = 1 + Size_Of (H, H.Links (Last).Left)
                   + Size_Of (H, H.Links (Last).Right));
            pragma Assert
              (H.Links (Gone).Size
               = 1 + Size_Of (H, H.Links (Gone).Left)
                   + Size_Of (H, H.Links (Gone).Right));
            pragma Assert
              (if Up /= 0
               then H.Links (Up).Size
                    = 1 + Size_Of (H, H.Links (Up).Left)
                        + Size_Of (H, H.Links (Up).Right));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                  then H.Links (I).Size
                       = 1 + Size_Of (H, H.Links (I).Left)
                           + Size_Of (H, H.Links (I).Right)));
            pragma Assert
              (for all I in 1 .. Last =>
                 H.Links (I).Size
                 = 1 + Size_Of (H, H.Links (I).Left)
                     + Size_Of (H, H.Links (I).Right));

            pragma Assert
              (H.Links (Last).Dist = 1 + Dist_Of (H, H.Links (Last).Right)
               and then H.Links (Last).Dist <= H.Links (Last).Size
               and then Dist_Of (H, H.Links (Last).Left)
                        >= Dist_Of (H, H.Links (Last).Right));
            pragma Assert
              (H.Links (Gone).Left = Kid_L
               and then H.Links (Gone).Right = Kid_R);
            pragma Assert
              (Dist_Of (H, Kid_L) = Dist_Of (Mid, Kid_L)
               and then Dist_Of (H, Kid_R) = Dist_Of (Mid, Kid_R)
               and then Dist_Of (Mid, Kid_L) >= Dist_Of (Mid, Kid_R));
            pragma Assert
              (H.Links (Gone).Dist = 1 + Dist_Of (H, H.Links (Gone).Right)
               and then H.Links (Gone).Dist <= H.Links (Gone).Size
               and then Dist_Of (H, H.Links (Gone).Left)
                        >= Dist_Of (H, H.Links (Gone).Right));
            pragma Assert
              (if Up /= 0
               then H.Links (Up).Dist = 1 + Dist_Of (H, H.Links (Up).Right)
                    and then H.Links (Up).Dist <= H.Links (Up).Size
                    and then Dist_Of (H, H.Links (Up).Left)
                             >= Dist_Of (H, H.Links (Up).Right));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                  then H.Links (I).Dist = 1 + Dist_Of (H, H.Links (I).Right)
                       and then H.Links (I).Dist <= H.Links (I).Size
                       and then Dist_Of (H, H.Links (I).Left)
                                >= Dist_Of (H, H.Links (I).Right)));
            pragma Assert
              (for all I in 1 .. Last =>
                 H.Links (I).Dist = 1 + Dist_Of (H, H.Links (I).Right)
                 and then H.Links (I).Dist <= H.Links (I).Size
                 and then Dist_Of (H, H.Links (I).Left)
                          >= Dist_Of (H, H.Links (I).Right));

            pragma Assert
              (for all I in 1 .. Last =>
                 (if I /= Gone and then I /= Last and then I /= Up
                  then (if H.Links (I).Left /= 0
                        then H.Links (H.Links (I).Left).Parent = I
                             and then H.Keys (I) <= H.Keys (H.Links (I).Left)
                             and then H.Links (I).Left /= H.Links (I).Right)
                       and then (if H.Links (I).Right /= 0
                                 then H.Links (H.Links (I).Right).Parent = I
                                      and then H.Keys (I)
                                               <= H.Keys (H.Links (I).Right))
                       and then (if H.Links (I).Parent /= 0
                                 then H.Links (H.Links (I).Parent).Left = I
                                      or else
                                        H.Links (H.Links (I).Parent).Right
                                        = I)));
            pragma Assert
              (for all I in 1 .. Last =>
                 (if H.Links (I).Left /= 0
                  then H.Links (H.Links (I).Left).Parent = I
                       and then H.Keys (I) <= H.Keys (H.Links (I).Left)
                       and then H.Links (I).Left /= H.Links (I).Right)
                 and then (if H.Links (I).Right /= 0
                           then H.Links (H.Links (I).Right).Parent = I
                                and then H.Keys (I)
                                         <= H.Keys (H.Links (I).Right))
                 and then (if H.Links (I).Parent /= 0
                           then H.Links (H.Links (I).Parent).Left = I
                                or else H.Links (H.Links (I).Parent).Right
                                        = I));

            pragma Assert (Well_Linked (H));
            pragma Assert
              (Size_Of (H, Left_Sub) + Size_Of (H, Right_Sub) = Last - 1);
            pragma Assert (if Left_Sub /= 0 then H.Links (Left_Sub).Parent = 0);
            pragma Assert
              (if Right_Sub /= 0 then H.Links (Right_Sub).Parent = 0);
            pragma Assert
              (for all I in 1 .. Last - 1 =>
                 (if H.Links (I).Parent = 0
                  then I = Left_Sub or else I = Right_Sub));
            pragma Assert
              (for all I in 1 .. Last - 1 =>
                 H.Links (I).Left < Last
                 and then H.Links (I).Right < Last
                 and then H.Links (I).Parent < Last);
            pragma Assert
              (Key_Multisets.Add (Models.Occurrences (H.Keys, Last - 1), K)
               = Models.Occurrences (Old_Keys, Last));
         end;
      else
         Models.Lemma_Same_Prefix (Old_Keys, H.Keys, Last - 1);

         pragma Assert (Well_Linked (H));
         pragma Assert
           (for all I in 1 .. Last - 1 =>
              (if H.Links (I).Parent = 0
               then I = Left_Sub or else I = Right_Sub));
         pragma Assert
           (for all I in 1 .. Last - 1 =>
              H.Links (I).Left < Last
              and then H.Links (I).Right < Last
              and then H.Links (I).Parent < Last);
         pragma Assert
           (Key_Multisets.Add (Models.Occurrences (H.Keys, Last - 1), K)
            = Models.Occurrences (Old_Keys, Last));
      end if;

      H.Count := Last - 1;

      pragma Assert (Well_Linked (H));
      pragma Assert (Size_Of (H, Left_Sub) + Size_Of (H, Right_Sub) = Last - 1);

      Cut_Keys := H.Keys;

      Merge (H, Left_Sub, Right_Sub, New_Root);
      H.Root := New_Root;

      Models.Lemma_Same_Prefix (Cut_Keys, H.Keys, H.Count);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Cut_Keys, H.Count),
         Models.Occurrences (H.Keys, H.Count), K);
   end Extract_Min;

end Heaps.Leftist;
