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

package body Heaps.Weak with SPARK_Mode is

   package KM renames Key_Multisets;

   ------------------------
   -- Auxiliary notions  --
   ------------------------

   function Sift_Invariant (H : Heap; J : Index) return Boolean is
     (for all M in 2 .. H.Last =>
        (if Da (H, M) /= 1 or else not Is_Ancestor (M, J)
         then H.Keys (Da (H, M)) <= H.Keys (M)))
     with Ghost;
   --  What a descent holds on to: the ordering is restored everywhere except,
   --  possibly, between the root and the nodes it directly answers for that
   --  are still above J. Those are exactly the nodes the descent has not
   --  reached yet.

   function Spine_Above (H : Heap; J : Index) return Boolean is
     (for all M in 2 .. H.Last =>
        (if Da (H, M) = 1 and then not Is_Ancestor (M, J)
         then Is_Ancestor (J, M)))
     with Ghost;
   --  What the walk down to the bottom of the left spine holds on to: every
   --  node the root answers for is on the walk, either behind J or ahead of
   --  it.

   ------------
   -- Lemmas --
   ------------

   procedure Lemma_Da_Is_Ancestor (H : Heap)
     with Ghost,
          Post => (for all M in 2 .. H.Capacity => Is_Ancestor (Da (H, M), M));
   --  The distinguished ancestor of a node really is one of its ancestors

   procedure Lemma_Da_Frame (H1, H2 : Heap; N : Extended_Index)
     with Ghost,
          Pre  => H1.Capacity = H2.Capacity
                  and then N <= H1.Capacity
                  and then (for all M in 1 .. N => H1.Flip (M) = H2.Flip (M)),
          Post => (for all M in 1 .. N => Da (H1, M) = Da (H2, M));
   --  The distinguished ancestor of a node is decided by the flip bits of its
   --  own ancestors, all of which have smaller indices, so agreeing on a
   --  prefix of the bits is enough to agree on it.

   procedure Lemma_Join (Old_H, New_H : Heap; A, J : Index)
     with Ghost,
          Pre  => New_H.Capacity = Old_H.Capacity
                  and then J in 2 .. Old_H.Capacity
                  and then A = Da (Old_H, J)
                  and then New_H.Flip (J) = not Old_H.Flip (J)
                  and then (for all M in 1 .. Old_H.Capacity =>
                              (if M /= J
                               then New_H.Flip (M) = Old_H.Flip (M))),
          Post => (for all M in 1 .. Old_H.Capacity =>
                     (if not (Is_Ancestor (J, M) and then M /= J)
                      then Da (New_H, M) = Da (Old_H, M)
                      elsif Da (Old_H, M) = A then Da (New_H, M) = J
                      elsif Da (Old_H, M) = J then Da (New_H, M) = A
                      else Da (New_H, M) = Da (Old_H, M)));
   --  Exchanging the two subtrees of J leaves every node outside those
   --  subtrees answerable to the same ancestor as before, and swaps the roles
   --  of J and of its own distinguished ancestor inside them. That is the one
   --  structural fact both sifts rest on: since the keys of J and A are
   --  exchanged at the same time, the ordering constraint attached to each
   --  node is carried along with the key that has to satisfy it.

   procedure Lemma_Spine_Reaches_Two (H : Heap)
     with Ghost,
          Post => (for all M in 2 .. H.Last =>
                     (if Da (H, M) = 1 then Is_Ancestor (2, M)));
   --  Every node the root answers for hangs below index 2

   procedure Lemma_Spine_Below (H : Heap; J : Index)
     with Ghost,
          Pre  => J in 2 .. H.Capacity,
          Post => (for all M in 2 .. H.Last =>
                     (if Da (H, M) = 1
                         and then Is_Ancestor (J, M)
                         and then M /= J
                      then Is_Ancestor (Left_Child (H, J), M)));
   --  A node the root answers for that lies below J lies below the left child
   --  of J: the only way out of a subtree, as far as the distinguished
   --  ancestor is concerned, is through left children.

   --------------------------
   -- Lemma_Da_Is_Ancestor --
   --------------------------

   procedure Lemma_Da_Is_Ancestor (H : Heap) is
   begin
      for I in 1 .. H.Capacity loop
         pragma Loop_Invariant
           (for all M in 2 .. I => Is_Ancestor (Da (H, M), M));
      end loop;
   end Lemma_Da_Is_Ancestor;

   --------------------
   -- Lemma_Da_Frame --
   --------------------

   procedure Lemma_Da_Frame (H1, H2 : Heap; N : Extended_Index) is
   begin
      for I in 1 .. N loop
         pragma Loop_Invariant (for all M in 1 .. I => Da (H1, M) = Da (H2, M));
      end loop;
   end Lemma_Da_Frame;

   ----------------
   -- Lemma_Join --
   ----------------

   procedure Lemma_Join (Old_H, New_H : Heap; A, J : Index) is
   begin
      for I in 1 .. Old_H.Capacity loop

         if I > 2 and then Parent (I) = J then

            --  I is one of the two children of J, so the flip of J exchanges
            --  its role: what was the left child is now the right one and the
            --  other way round.

            pragma Assert (I = 2 * J - 1 or else I = 2 * J);
            pragma Assert (Left_Child (New_H, J) /= Left_Child (Old_H, J));
            pragma Assert
              (Is_Left_Child (New_H, I) /= Is_Left_Child (Old_H, I));
            pragma Assert (Is_Ancestor (J, I) and then I /= J);

            --  J itself lies outside the two subtrees that moved, so it still
            --  answers to A. That is what the child that has just become a
            --  left child inherits.

            pragma Assert (Da (New_H, J) = A);

         elsif I > 2 then

            --  Only the flip bit of the parent decides the side a node is on

            pragma Assert
              (Is_Left_Child (New_H, I) = Is_Left_Child (Old_H, I));
         end if;

         pragma Loop_Invariant
           (for all M in 1 .. I =>
              (if not (Is_Ancestor (J, M) and then M /= J)
               then Da (New_H, M) = Da (Old_H, M)
               elsif Da (Old_H, M) = A then Da (New_H, M) = J
               elsif Da (Old_H, M) = J then Da (New_H, M) = A
               else Da (New_H, M) = Da (Old_H, M)));
      end loop;
   end Lemma_Join;

   ------------------------------
   -- Lemma_Spine_Reaches_Two  --
   ------------------------------

   procedure Lemma_Spine_Reaches_Two (H : Heap) is
   begin
      for I in 1 .. H.Last loop
         pragma Loop_Invariant
           (for all M in 2 .. I => (if Da (H, M) = 1 then Is_Ancestor (2, M)));
      end loop;
   end Lemma_Spine_Reaches_Two;

   -----------------------
   -- Lemma_Spine_Below --
   -----------------------

   procedure Lemma_Spine_Below (H : Heap; J : Index) is
   begin
      for I in 1 .. H.Last loop
         pragma Loop_Invariant
           (for all M in 2 .. I =>
              (if Da (H, M) = 1
                  and then Is_Ancestor (J, M)
                  and then M /= J
               then Is_Ancestor (Left_Child (H, J), M)));
      end loop;
   end Lemma_Spine_Below;

   ---------------------------
   -- Lemma_Root_Is_Minimum --
   ---------------------------

   procedure Lemma_Root_Is_Minimum (H : Heap) is
   begin
      --  Induction on the index: the distinguished ancestor of I is a smaller
      --  index, so by the time I is reached the root has already been shown to
      --  be below it.

      for I in 1 .. H.Last loop
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (1) <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   --------------
   -- Ancestor --
   --------------

   function Ancestor (H : Heap; I : Index) return Index
     with Pre  => I in 2 .. H.Capacity,
          Post => Ancestor'Result = Da (H, I);
   --  The distinguished ancestor, computed by the climb its definition
   --  describes. A sift resumes its own climb from the node this one stopped
   --  at, so the successive climbs of one sift add up to a single walk to the
   --  root rather than to one walk per level.

   function Ancestor (H : Heap; I : Index) return Index is
      Cur : Index := I;
   begin
      while Is_Left_Child (H, Cur) loop
         Cur := Parent (Cur);

         pragma Loop_Invariant (Cur in 2 .. I);
         pragma Loop_Invariant (Da (H, Cur) = Da (H, I));
         pragma Loop_Variant (Decreases => Cur);
      end loop;

      return Parent (Cur);
   end Ancestor;

   ------------
   -- Min_Of --
   ------------

   function Min_Of (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Last loop
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
      H.Last := 0;
   end Clear;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Old_H : constant Heap := H with Ghost;
      Base  : constant KM.Multiset := Model (H) with Ghost;

      Prev : Heap (Old_H.Capacity) with Ghost;
      --  Snapshot of the heap taken just before each exchange, so that
      --  Lemma_Join can relate the two states. SPARK does not allow declaring
      --  it inside the loop body, hence the hoisting.

      J : Index;
      A : Index;
      Above : Key_Type;
      --  The key of the node the exchange pulls down
   begin
      H.Last := H.Last + 1;
      H.Keys (H.Last) := K;
      H.Flip (H.Last) := False;
      J := H.Last;

      --  The new key lands past the end of the old array, so the model simply
      --  gains it and the ordering of the old nodes is untouched.

      Models.Lemma_Same_Prefix (Old_H.Keys, H.Keys, Old_H.Last);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Old_H.Keys, Old_H.Last),
         Models.Occurrences (H.Keys, Old_H.Last), K);
      Lemma_Da_Frame (Old_H, H, Old_H.Last);

      while J > 1 loop
         A := Ancestor (H, J);

         exit when H.Keys (A) <= H.Keys (J);

         --  The new key belongs above A. Exchanging the two keys and the two
         --  subtrees of J settles the ordering at J for good and moves the
         --  single node that may still be out of place up to A.

         Prev := H;

         Above := H.Keys (A);
         H.Keys (A) := H.Keys (J);
         H.Keys (J) := Above;
         H.Flip (J) := not H.Flip (J);

         Lemma_Join (Prev, H, A, J);
         Lemma_Da_Is_Ancestor (Prev);
         Models.Lemma_Swap (Prev.Keys, H.Keys, A, J, H.Last);

         --  A node that answered to J now answers to A and the other way
         --  round; every other node keeps the ancestor it had.

         pragma Assert
           (for all M in 2 .. H.Last =>
              (if Da (Prev, M) = J then Da (H, M) = A));
         pragma Assert
           (for all M in 2 .. H.Last =>
              (if M /= A then H.Keys (Da (H, M)) <= H.Keys (M)));

         J := A;

         pragma Loop_Invariant (J in 1 .. H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant
           (for all M in 2 .. H.Last =>
              (if M /= J then H.Keys (Da (H, M)) <= H.Keys (M)));
         pragma Loop_Invariant
           (Models.Occurrences (H.Keys, H.Last) = KM.Add (Base, K));
         pragma Loop_Variant (Decreases => J);
      end loop;
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Old_H : constant Heap := H with Ghost;

      Prev : Heap (Old_H.Capacity) with Ghost;
      --  See the comment on the homonym in Insert

      J : Index;
      Above : Key_Type;
      --  The key of the node the exchange pulls down
   begin
      Lemma_Root_Is_Minimum (H);
      K := H.Keys (1);

      if H.Last = 1 then
         H.Last := 0;
         return;
      end if;

      --  The last key takes the place of the extracted one. The only nodes
      --  whose ordering this can break are the ones the root answers for.

      H.Keys (1) := H.Keys (H.Last);
      H.Last := H.Last - 1;

      Models.Lemma_Set (Old_H.Keys, H.Keys, 1, H.Last);
      Lemma_Da_Frame (Old_H, H, H.Capacity);

      declare
         Base : constant KM.Multiset := Model (H) with Ghost;
      begin
         if H.Last = 1 then
            return;
         end if;

         --  Walk down the left spine to its last node. Along the way, every
         --  node the root answers for is shown to be on the walk.

         J := 2;
         Lemma_Spine_Reaches_Two (H);

         while Left_Child (H, J) <= H.Last loop
            Lemma_Spine_Below (H, J);
            J := Left_Child (H, J);

            pragma Loop_Invariant (J in 2 .. H.Last);
            pragma Loop_Invariant (Da (H, J) = 1);
            pragma Loop_Invariant (Spine_Above (H, J));
            pragma Loop_Variant (Increases => J);
         end loop;

         --  Nothing the root answers for lies below J, so the walk has the
         --  whole of it and can now be replayed upwards.

         Lemma_Spine_Below (H, J);

         while J > 1 loop
            if H.Keys (J) < H.Keys (1) then

               --  Same exchange as in an insertion, with the root as the
               --  ancestor: it settles the ordering at J and hands the
               --  subtree the root used to answer for over to J.

               Prev := H;

               Above := H.Keys (1);
               H.Keys (1) := H.Keys (J);
               H.Keys (J) := Above;
               H.Flip (J) := not H.Flip (J);

               Lemma_Join (Prev, H, 1, J);
               Lemma_Da_Is_Ancestor (Prev);
               Models.Lemma_Swap (Prev.Keys, H.Keys, 1, J, H.Last);

               pragma Assert
                 (for all M in 2 .. H.Last =>
                    (if Da (Prev, M) = J then Da (H, M) = 1));
            end if;

            pragma Assert (H.Keys (1) <= H.Keys (J));
            pragma Assert (Sift_Invariant (H, Parent (J)));

            J := Parent (J);

            pragma Loop_Invariant (J in 1 .. H.Last);
            pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
            pragma Loop_Invariant (if J >= 2 then Da (H, J) = 1);
            pragma Loop_Invariant (Sift_Invariant (H, J));
            pragma Loop_Invariant (Models.Occurrences (H.Keys, H.Last) = Base);
            pragma Loop_Variant (Decreases => J);
         end loop;
      end;
   end Extract_Min;

end Heaps.Weak;
