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

--  Contracts below mention H.Keys'Old under a quantifier and Model (H)'Old
--  after a short-circuit, neither of which the language allows by default.

pragma Unevaluated_Use_Of_Old (Allow);

package body Heaps.Min_Max with SPARK_Mode is

   package KM renames Key_Multisets;

   ------------------------------------
   -- Weakenings of the heap property --
   ------------------------------------

   --  A sift travels with one key that is not yet where it belongs. Each of
   --  the three predicates below says "the heap property holds everywhere
   --  except for what that one key claims", and they differ only in which
   --  claims are suspended: the ones the key makes about its subtree
   --  (sift-down), the ones its same-side ancestors make about it (sift-up),
   --  or all of them at once (a key just appended as a leaf).

   subtype Claim_Bound is Positive range 1 .. Max_Capacity + 1;
   --  A lower bound on the indices whose claims are in force. It reaches one
   --  past the largest index so that a build can start from "no claim at all".

   function Heap_Except_Below
     (H : Heap; I : Extended_Index; N : Claim_Bound) return Boolean
   is
     (for all A in N .. H.Last =>
        (for all D in 1 .. H.Last =>
           (if Is_Ancestor (A, D) and then A /= I
            then Ordered (Min_Level (A), H.Keys (A), H.Keys (D)))))
     with Ghost;
   --  N is the lowest index whose claims are in force. A sift works with
   --  N = 1, where every node in the array claims its subtree; a bottom-up
   --  build works its way down from N = H.Last + 1, where none of them does
   --  yet. Passing I = 0 suspends no claim at all, which is how the two ends
   --  of a build step are stated: Heap_Except_Below (H, 0, 1) is Is_Heap (H).

   function Heap_Except_Above (H : Heap; I : Index) return Boolean is
     (for all A in 1 .. H.Last =>
        (for all D in 1 .. H.Last =>
           (if Is_Ancestor (A, D)
               and then not (D = I and then Min_Level (A) = Min_Level (D))
            then Ordered (Min_Level (A), H.Keys (A), H.Keys (D)))))
     with Ghost;

   function Heap_Except_Leaf (H : Heap; I : Index) return Boolean is
     (for all A in 1 .. H.Last =>
        (for all D in 1 .. H.Last =>
           (if Is_Ancestor (A, D) and then D /= I
            then Ordered (Min_Level (A), H.Keys (A), H.Keys (D)))))
     with Ghost;

   function Is_Near (I, J : Index) return Boolean is
     (J / 2 = I or else J / 2 / 2 = I)
     with Ghost;
   --  J is a child or a grandchild of I: the nodes a sift-down step chooses
   --  between

   -------------------------
   -- Structural lemmas   --
   -------------------------

   procedure Lemma_Parent_Level (D : Index)
     with Ghost,
          Pre  => D > 1,
          Post => Min_Level (Parent (D)) = not Min_Level (D);

   ----------------------------
   -- Steps of a sift        --
   ----------------------------

   --  The three lemmas below are the heart of the unit: each of them takes
   --  the state before one elementary rearrangement and the state after it,
   --  and says which weakened heap property comes out. They are stated on two
   --  heap values rather than on an in-out parameter so that the case
   --  analysis has both states in hand at once.

   procedure Lemma_Step_Up (Before, After : Heap; I : Index)
     with Ghost,
          Pre  => I > 3
                  and then I <= Before.Last
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Above (Before, I)
                  and then Better (Min_Level (I),
                                   Before.Keys (I),
                                   Before.Keys (Grandparent (I)))
                  and then After.Keys (Grandparent (I)) = Before.Keys (I)
                  and then After.Keys (I) = Before.Keys (Grandparent (I))
                  and then (for all M in 1 .. Before.Last =>
                              (if M /= I and M /= Grandparent (I)
                               then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Above (After, Grandparent (I));

   procedure Lemma_Step_Down_Near
     (Before, After : Heap; I, M : Index; N : Claim_Bound)
     with Ghost,
          Pre  => I < M
                  and then M <= Before.Last
                  and then N <= I
                  and then Parent (M) = I
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Below (Before, I, N)
                  and then (for all J in 1 .. Before.Last =>
                              (if Is_Near (I, J)
                               then Ordered (Min_Level (I),
                                             Before.Keys (M),
                                             Before.Keys (J))))
                  and then Better (Min_Level (I),
                                   Before.Keys (M),
                                   Before.Keys (I))
                  and then After.Keys (I) = Before.Keys (M)
                  and then After.Keys (M) = Before.Keys (I)
                  and then (for all J in 1 .. Before.Last =>
                              (if J /= I and J /= M
                               then After.Keys (J) = Before.Keys (J))),
          Post => Heap_Except_Below (After, M, N);
   --  Exchanging a node with its best child. The key that comes down is on
   --  the other side, so the descent continues with the comparison direction
   --  reversed; it stops at once, because everything below a best child is
   --  squeezed between that child and the key that just replaced it.

   procedure Lemma_Step_Down_Far
     (Before, After : Heap; I, M : Index; N : Claim_Bound)
     with Ghost,
          Pre  => I < M
                  and then M <= Before.Last
                  and then N <= I
                  and then Grandparent (M) = I
                  and then Parent (M) /= I
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Below (Before, I, N)
                  and then (for all J in 1 .. Before.Last =>
                              (if Is_Near (I, J)
                               then Ordered (Min_Level (I),
                                             Before.Keys (M),
                                             Before.Keys (J))))
                  and then Better (Min_Level (I),
                                   Before.Keys (M),
                                   Before.Keys (I))
                  and then After.Keys (I) = Before.Keys (M)
                  and then Ordered (Min_Level (Parent (M)),
                                    After.Keys (Parent (M)),
                                    After.Keys (M))
                  and then ((After.Keys (M) = Before.Keys (I)
                             and then After.Keys (Parent (M))
                                      = Before.Keys (Parent (M)))
                            or else
                            (After.Keys (M) = Before.Keys (Parent (M))
                             and then After.Keys (Parent (M))
                                      = Before.Keys (I)))
                  and then (for all J in 1 .. Before.Last =>
                              (if J /= I and J /= M and J /= Parent (M)
                               then After.Keys (J) = Before.Keys (J))),
          Post => Heap_Except_Below (After, M, N);
   --  Exchanging a node with its best grandchild, then repairing the max node
   --  in between if the key that came down overshot it

   ---------------------------
   -- Settling of a sift    --
   ---------------------------

   procedure Lemma_Settled_Above (H : Heap; I : Index)
     with Ghost,
          Pre  => I <= H.Last
                  and then Heap_Except_Above (H, I)
                  and then (I <= 3
                            or else Ordered (Min_Level (I),
                                             H.Keys (Grandparent (I)),
                                             H.Keys (I))),
          Post => Is_Heap (H);

   procedure Lemma_Settled_Below
     (H : Heap; I : Index; N : Claim_Bound)
     with Ghost,
          Pre  => I <= H.Last
                  and then N <= I
                  and then Heap_Except_Below (H, I, N)
                  and then (for all J in 1 .. H.Last =>
                              (if Is_Near (I, J)
                               then Ordered (Min_Level (I),
                                             H.Keys (I),
                                             H.Keys (J)))),
          Post => Heap_Except_Below (H, 0, N);

   procedure Lemma_Leaf_Placed (H : Heap; I : Index)
     with Ghost,
          Pre  => I > 1
                  and then I = H.Last
                  and then Heap_Except_Leaf (H, I)
                  and then Ordered (Min_Level (Parent (I)),
                                    H.Keys (Parent (I)),
                                    H.Keys (I)),
          Post => Heap_Except_Above (H, I);
   --  A key appended as a leaf and found to sit correctly under its parent
   --  is then only ever too good for its same-side ancestors

   procedure Lemma_Leaf_Promoted (Before, After : Heap; I : Index)
     with Ghost,
          Pre  => I > 1
                  and then I = Before.Last
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Leaf (Before, I)
                  and then Better (Min_Level (Parent (I)),
                                   Before.Keys (I),
                                   Before.Keys (Parent (I)))
                  and then After.Keys (Parent (I)) = Before.Keys (I)
                  and then After.Keys (I) = Before.Keys (Parent (I))
                  and then (for all M in 1 .. Before.Last =>
                              (if M /= I and M /= Parent (I)
                               then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Above (After, Parent (I));
   --  A key appended as a leaf that turns out to belong on the other side is
   --  exchanged with its parent, and it is then that parent's position that
   --  has to travel up

   -----------------------
   -- Small operations  --
   -----------------------

   procedure Swap (H : in out Heap; I, J : Index)
     with Pre  => I < J and then J <= H.Last,
          Post => H.Last = H.Last'Old
                  and then H.Keys (I) = H.Keys'Old (J)
                  and then H.Keys (J) = H.Keys'Old (I)
                  and then (for all M in 1 .. H.Last =>
                              (if M /= I and M /= J
                               then H.Keys (M) = H.Keys'Old (M)))
                  and then Model (H) = Model (H)'Old;

   procedure Best_Near (H : Heap; I : Index; Min_Side : Boolean; M : out Index)
     with Pre  => Min_Side = Min_Level (I)
                  and then 2 * I <= H.Last,
          Post => M <= H.Last
                  and then Is_Near (I, M)
                  and then I < M
                  and then (for all J in 1 .. H.Last =>
                              (if Is_Near (I, J)
                               then Ordered (Min_Side, H.Keys (M),
                                             H.Keys (J))));
   --  The best of the children and grandchildren of I on the given side

   procedure Sift_Up (H : in out Heap; Start : Index; Min_Side : Boolean)
     with Pre  => Start <= H.Last
                  and then Min_Side = Min_Level (Start)
                  and then Heap_Except_Above (H, Start),
          Post => Is_Heap (H)
                  and then H.Last = H.Last'Old
                  and then Model (H) = Model (H)'Old;

   procedure Sift_Down
     (H : in out Heap; Start : Index; Min_Side : Boolean;
      N : Claim_Bound := 1)
     with Pre  => Start <= H.Last
                  and then N <= Start
                  and then Min_Side = Min_Level (Start)
                  and then Heap_Except_Below (H, Start, N),
          Post => Heap_Except_Below (H, 0, N)
                  and then H.Last = H.Last'Old
                  and then Model (H) = Model (H)'Old;
   --  N is the lowest index whose subtree is already in order; everything
   --  below it is left alone. The extractions sift with N = 1, where the
   --  whole array is in order but for the key being carried down; a bottom-up
   --  build sifts at N = Start, where nothing above Start is in order yet.

   ------------------
   -- Is_Min_Level --
   ------------------

   function Is_Min_Level (I : Index) return Boolean is
      J : Index := I;
   begin
      --  Climbing two levels at a time keeps the side unchanged, so the walk
      --  can stop as soon as it reaches the top three nodes -- of which only
      --  the root is a min node.

      while J > 3 loop
         pragma Loop_Invariant (Min_Level (I) = Min_Level (J));
         pragma Loop_Variant (Decreases => J);
         Lemma_Grandparent_Level (J);
         J := Grandparent (J);
      end loop;

      return J = 1;
   end Is_Min_Level;

   ------------------------
   -- Lemma_Parent_Level --
   ------------------------

   procedure Lemma_Parent_Level (D : Index) is null;

   -----------------------------
   -- Lemma_Grandparent_Level --
   -----------------------------

   procedure Lemma_Grandparent_Level (D : Index) is null;

   ------------------------------
   -- Lemma_Root_Is_Ancestor   --
   ------------------------------

   procedure Lemma_Root_Is_Ancestor (D : Index) is
   begin
      if D > 1 then
         Lemma_Root_Is_Ancestor (D / 2);
      end if;
   end Lemma_Root_Is_Ancestor;

   -----------------------
   -- Lemma_Below_Root  --
   -----------------------

   procedure Lemma_Below_Root (D : Index) is
   begin
      if D > 3 then
         Lemma_Below_Root (D / 2);
      end if;
   end Lemma_Below_Root;

   -------------------------------
   -- Lemma_Ancestor_Transitive --
   -------------------------------

   procedure Lemma_Ancestor_Transitive (A, B, D : Index) is
   begin
      if B /= D then
         Lemma_Ancestor_Transitive (A, B, D / 2);
      end if;
   end Lemma_Ancestor_Transitive;

   -----------------------
   -- Lemma_Skip_Level  --
   -----------------------

   procedure Lemma_Skip_Level (A, D : Index) is
      pragma Unreferenced (A);
   begin
      Lemma_Parent_Level (D);
   end Lemma_Skip_Level;

   ----------
   -- Swap --
   ----------

   procedure Swap (H : in out Heap; I, J : Index) is
      Before : constant Key_Array := H.Keys with Ghost;
      T      : constant Key_Type  := H.Keys (I);
   begin
      H.Keys (I) := H.Keys (J);
      H.Keys (J) := T;
      Models.Lemma_Swap (Before, H.Keys, I, J, H.Last);
   end Swap;

   ---------------
   -- Best_Near --
   ---------------

   procedure Best_Near
     (H : Heap; I : Index; Min_Side : Boolean; M : out Index)
   is
      First_Child      : constant Index   := 2 * I;
      Last_Child       : constant Natural := Natural'Min (2 * I + 1, H.Last);
      First_Grandchild : constant Natural := 4 * I;
      Last_Grandchild  : constant Natural := Natural'Min (4 * I + 3, H.Last);
   begin
      M := First_Child;

      for J in First_Child + 1 .. Last_Child loop
         if Better (Min_Side, H.Keys (J), H.Keys (M)) then
            M := J;
         end if;
         pragma Loop_Invariant (Is_Near (I, M) and I < M and M <= H.Last);
         pragma Loop_Invariant
           (for all L in First_Child .. J =>
              Ordered (Min_Side, H.Keys (M), H.Keys (L)));
      end loop;

      for J in First_Grandchild .. Last_Grandchild loop
         if Better (Min_Side, H.Keys (J), H.Keys (M)) then
            M := J;
         end if;
         pragma Loop_Invariant (Is_Near (I, M) and I < M and M <= H.Last);
         pragma Loop_Invariant
           (for all L in First_Child .. Last_Child =>
              Ordered (Min_Side, H.Keys (M), H.Keys (L)));
         pragma Loop_Invariant
           (for all L in First_Grandchild .. J =>
              Ordered (Min_Side, H.Keys (M), H.Keys (L)));
      end loop;
   end Best_Near;

   -------------
   -- Sift_Up --
   -------------

   procedure Sift_Up (H : in out Heap; Start : Index; Min_Side : Boolean) is
      I : Index := Start;
   begin
      while I > 3
        and then Better (Min_Side, H.Keys (I), H.Keys (Grandparent (I)))
      loop
         pragma Loop_Invariant (I <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (Min_Side = Min_Level (I));
         pragma Loop_Invariant (Heap_Except_Above (H, I));
         pragma Loop_Invariant (Model (H) = Model (H)'Loop_Entry);
         pragma Loop_Variant (Decreases => I);

         declare
            G      : constant Index := Grandparent (I);
            Before : constant Heap  := H with Ghost;
         begin
            Lemma_Grandparent_Level (I);
            Swap (H, G, I);
            Lemma_Step_Up (Before, H, I);
            I := G;
         end;
      end loop;

      Lemma_Settled_Above (H, I);
   end Sift_Up;

   ---------------
   -- Sift_Down --
   ---------------

   procedure Sift_Down
     (H : in out Heap; Start : Index; Min_Side : Boolean;
      N : Claim_Bound := 1) is
      I    : Index   := Start;
      Side : Boolean := Min_Side;
      M    : Index;
   begin
      loop
         pragma Loop_Invariant (I <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (Side = Min_Level (I));
         pragma Loop_Invariant (N <= I);
         pragma Loop_Invariant (Heap_Except_Below (H, I, N));
         pragma Loop_Invariant (Model (H) = Model (H)'Loop_Entry);
         pragma Loop_Variant (Increases => I);

         exit when 2 * I > H.Last;

         Best_Near (H, I, Side, M);

         exit when not Better (Side, H.Keys (M), H.Keys (I));

         declare
            Before : constant Heap := H with Ghost;
         begin
            Swap (H, I, M);

            if Grandparent (M) = I and then Parent (M) /= I then
               declare
                  P : constant Index := Parent (M);
               begin
                  if Better (Side, H.Keys (P), H.Keys (M)) then
                     Swap (H, P, M);
                  end if;
                  Lemma_Parent_Level (M);
                  Lemma_Step_Down_Far (Before, H, I, M, N);
               end;
            else
               Lemma_Step_Down_Near (Before, H, I, M, N);
               Lemma_Parent_Level (M);
               Side := not Side;
            end if;

            I := M;
         end;
      end loop;

      Lemma_Settled_Below (H, I, N);
   end Sift_Down;

   -----------
   -- Clear --
   -----------

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
   end Clear;

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

   ------------
   -- Max_Of --
   ------------

   function Max_Of (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) > Result then
            Result := H.Keys (I);
         end if;

         pragma Loop_Invariant (for all J in 1 .. I => H.Keys (J) <= Result);
         pragma Loop_Invariant (for some J in 1 .. I => Result = H.Keys (J));
      end loop;

      return Result;
   end Max_Of;

   ---------------------------
   -- Lemma_Root_Is_Minimum --
   ---------------------------

   procedure Lemma_Root_Is_Minimum (H : Heap) is
   begin
      for I in 1 .. H.Last loop
         Lemma_Root_Is_Ancestor (I);
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (1) <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   --------------------------
   -- Lemma_Top_Is_Maximum --
   --------------------------

   procedure Lemma_Top_Is_Maximum (H : Heap) is
      T : constant Index := Max_Index (H);
   begin
      Lemma_Root_Is_Minimum (H);

      for I in 1 .. H.Last loop
         if I > 1 then
            Lemma_Below_Root (I);
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (J) <= H.Keys (T));
      end loop;
   end Lemma_Top_Is_Maximum;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Base   : constant KM.Multiset := Model (H) with Ghost;
      Old_A  : constant Key_Array   := H.Keys with Ghost;
      I      : constant Index       := H.Last + 1;
      Side   : constant Boolean     := Is_Min_Level (I);
   begin
      H.Keys (I) := K;
      Models.Lemma_Same_Prefix (Old_A, H.Keys, H.Last);
      H.Last := I;

      pragma Assert (Model (H) = KM.Add (Base, K));
      pragma Assert (Heap_Except_Leaf (H, I));

      if I > 1 then
         declare
            P      : constant Index := Parent (I);
            Before : constant Heap  := H with Ghost;
         begin
            Lemma_Parent_Level (I);

            if Better (not Side, H.Keys (I), H.Keys (P)) then
               Swap (H, P, I);
               Lemma_Leaf_Promoted (Before, H, I);
               Sift_Up (H, P, not Side);
            else
               Lemma_Leaf_Placed (H, I);
               Sift_Up (H, I, Side);
            end if;
         end;
      else
         Lemma_Settled_Above (H, I);
      end if;
   end Insert;

   ----------
   -- Meld --
   ----------

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Before : constant Key_Array := Into.Keys with Ghost;
      Base   : constant Extended_Index := Into.Last;
      Cap    : constant Extended_Index := Into.Capacity;

      Joined : KM.Multiset with Ghost;
      --  The model of the concatenation, which the rebuild has to preserve

      Prev : Key_Array (1 .. Cap) with Ghost;
      --  See the comment on the homonym in Heaps.Unsorted.Meld
   begin
      --  Append the keys of From. This is the same argument as the unsorted
      --  array's meld: the prefix does not move and each copied key joins the
      --  sum in turn.

      for I in 1 .. From.Last loop
         Prev := Into.Keys;

         Into.Keys (Base + I) := From.Keys (I);
         Into.Last := Base + I;

         Models.Lemma_Same_Prefix (Prev, Into.Keys, Base + I - 1);
         Models.Lemma_Add_Congruent
           (Models.Occurrences (Prev, Base + I - 1),
            Models.Occurrences (Into.Keys, Base + I - 1),
            From.Keys (I));
         Models.Lemma_Sum_Add
           (Models.Occurrences (Before, Base),
            Models.Occurrences (From.Keys, I - 1),
            From.Keys (I));
         Models.Lemma_Sum_Empty (Models.Occurrences (Before, Base));

         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant
           (for all J in 1 .. Base => Into.Keys (J) = Before (J));
         pragma Loop_Invariant
           (Model (Into)
            = Models.Occurrences (Before, Base)
              + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (Models.Occurrences (Before, Base));
      end if;

      Joined := Model (Into);

      --  Rebuild bottom-up. The claim bound starts one past the last index,
      --  where no node yet answers for its subtree, and travels down to the
      --  root; each sift is given exactly the claims already established.

      for I in reverse 1 .. Into.Last loop
         Sift_Down (Into, I, Is_Min_Level (I), I);

         pragma Loop_Invariant (Heap_Except_Below (Into, 0, I));
         pragma Loop_Invariant (Into.Last = Base + From.Last);
         pragma Loop_Invariant (Model (Into) = Joined);
      end loop;

      From.Last := 0;
   end Meld;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Base  : constant KM.Multiset := Model (H) with Ghost;
      Old_A : constant Key_Array   := H.Keys with Ghost;
      Moved : constant Key_Type    := H.Keys (H.Last);
   begin
      Lemma_Root_Is_Minimum (H);

      K := H.Keys (1);
      H.Keys (1) := Moved;
      Models.Lemma_Set (Old_A, H.Keys, 1, H.Last);
      H.Last := H.Last - 1;

      pragma Assert (KM.Add (Model (H), Moved) = Models.Occurrences
                       (H.Keys, H.Last + 1));
      Models.Lemma_Add_Commutes (Model (H), Moved, K);
      Models.Lemma_Add_Cancels
        (KM.Add (Model (H), K), Base, Moved);

      if H.Last > 0 then
         Sift_Down (H, 1, True);
      end if;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
      Base  : constant KM.Multiset := Model (H) with Ghost;
      Old_A : constant Key_Array   := H.Keys with Ghost;
      Moved : constant Key_Type    := H.Keys (H.Last);
      T     : constant Index       := Max_Index (H);
   begin
      Lemma_Top_Is_Maximum (H);
      Lemma_Root_Is_Minimum (H);

      K := H.Keys (T);
      H.Keys (T) := Moved;
      Models.Lemma_Set (Old_A, H.Keys, T, H.Last);
      H.Last := H.Last - 1;

      pragma Assert (KM.Add (Model (H), Moved) = Models.Occurrences
                       (H.Keys, H.Last + 1));
      Models.Lemma_Add_Commutes (Model (H), Moved, K);
      Models.Lemma_Add_Cancels
        (KM.Add (Model (H), K), Base, Moved);

      if T <= H.Last then
         Sift_Down (H, T, Is_Min_Level (T));
      end if;
   end Extract_Max;

   -------------------------------------------------------------------
   -- The case analyses behind the sift steps                       --
   -------------------------------------------------------------------

   procedure Lemma_Step_Up (Before, After : Heap; I : Index) is
      pragma Unreferenced (Before);
      G : constant Index := Grandparent (I);
      P : constant Index := Parent (I);
   begin
      Lemma_Parent_Level (I);
      Lemma_Parent_Level (P);
      Lemma_Grandparent_Level (I);

      for A in 1 .. After.Last loop
         for D in 1 .. After.Last loop

            if Is_Ancestor (A, D)
              and then not (D = G and then Min_Level (A) = Min_Level (D))
            then
               if A = I then

                  --  I now holds what G held, and G is above everything I is
                  --  above.

                  Lemma_Ancestor_Transitive (G, I, D);

               elsif A /= G and then A /= P and then D = I then

                  --  An ancestor above the pair was already related to the
                  --  key that has just moved up.

                  pragma Assert (Is_Ancestor (A, P));
                  pragma Assert (Is_Ancestor (A, G));

               elsif A /= G and then A /= P and then D = G then

                  --  ... and to the one that has just moved down.

                  Lemma_Ancestor_Transitive (A, G, I);

               elsif A = P and then D = I then

                  --  The max node in between separated the two keys already.

                  pragma Assert (Is_Ancestor (G, P));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E)
                     and then not (E = G
                                   and then Min_Level (A) = Min_Level (E))
                  then Ordered (Min_Level (A), After.Keys (A),
                                After.Keys (E))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. After.Last =>
                 (if Is_Ancestor (B, E)
                     and then not (E = G
                                   and then Min_Level (B) = Min_Level (E))
                  then Ordered (Min_Level (B), After.Keys (B),
                                After.Keys (E)))));
      end loop;
   end Lemma_Step_Up;

   procedure Lemma_Step_Down_Near
     (Before, After : Heap; I, M : Index; N : Claim_Bound) is
      pragma Unreferenced (Before);
   begin
      Lemma_Parent_Level (M);

      for A in N .. After.Last loop
         for D in 1 .. After.Last loop

            if Is_Ancestor (A, D) and then A /= M then
               if A = I and then D /= I and then not Is_Near (I, D) then

                  --  Below the children and grandchildren the bound is
                  --  reached one same-side ancestor at a time; that ancestor
                  --  is never I itself, so the old heap property still
                  --  applies to it.

                  Lemma_Parent_Level (D);
                  Lemma_Grandparent_Level (D);

               elsif A /= I and then D = I then

                  --  Above I nothing moved, and the key now at I came from M.

                  Lemma_Ancestor_Transitive (A, I, M);

               elsif A /= I and then D = M then

                  --  ... while the key now at M came from I.

                  pragma Assert (Is_Ancestor (A, I));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E) and then A /= M
                  then Ordered (Min_Level (A), After.Keys (A),
                                After.Keys (E))));
         end loop;

         pragma Loop_Invariant
           (for all B in N .. A =>
              (for all E in 1 .. After.Last =>
                 (if Is_Ancestor (B, E) and then B /= M
                  then Ordered (Min_Level (B), After.Keys (B),
                                After.Keys (E)))));
      end loop;
   end Lemma_Step_Down_Near;

   procedure Lemma_Step_Down_Far
     (Before, After : Heap; I, M : Index; N : Claim_Bound) is
      pragma Unreferenced (Before);
      P : constant Index := Parent (M);
   begin
      Lemma_Parent_Level (M);
      Lemma_Grandparent_Level (M);
      pragma Assert (Is_Ancestor (I, P));
      pragma Assert (Is_Near (I, P));

      for A in N .. After.Last loop
         for D in 1 .. After.Last loop

            if Is_Ancestor (A, D) and then A /= M then
               if A = I then

                  --  I holds the best of its children and grandchildren, so
                  --  it bounds them outright; further down the bound is
                  --  reached one same-side ancestor at a time, and that
                  --  ancestor is never I itself.

                  if D /= I and then not Is_Near (I, D) then
                     Lemma_Parent_Level (D);
                     Lemma_Grandparent_Level (D);
                  end if;
                  pragma Assert
                    (Ordered (Min_Level (A), After.Keys (A), After.Keys (D)));

               elsif A = P then

                  --  The max node in between either kept its key, or took the
                  --  one that came down -- and that one overshot it, which is
                  --  precisely why it was moved here.

                  pragma Assert
                    (Ordered (Min_Level (A), After.Keys (A), After.Keys (D)));

               elsif D = I then

                  --  Above the pair nothing moved, and the key now at I came
                  --  from M.

                  Lemma_Ancestor_Transitive (A, I, M);
                  pragma Assert
                    (Ordered (Min_Level (A), After.Keys (A), After.Keys (D)));

               elsif D = M or else D = P then

                  --  The keys that ended up at M and at P came from I and
                  --  from P, both of which this ancestor already dominated.

                  pragma Assert (Is_Ancestor (A, P));
                  pragma Assert (Is_Ancestor (A, I));
                  pragma Assert
                    (Ordered (Min_Level (A), After.Keys (A), After.Keys (D)));

               else

                  --  Untouched pair.

                  pragma Assert
                    (Ordered (Min_Level (A), After.Keys (A), After.Keys (D)));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E) and then A /= M
                  then Ordered (Min_Level (A), After.Keys (A),
                                After.Keys (E))));
         end loop;

         pragma Loop_Invariant
           (for all B in N .. A =>
              (for all E in 1 .. After.Last =>
                 (if Is_Ancestor (B, E) and then B /= M
                  then Ordered (Min_Level (B), After.Keys (B),
                                After.Keys (E)))));
      end loop;
   end Lemma_Step_Down_Far;

   procedure Lemma_Settled_Above (H : Heap; I : Index) is
   begin
      for A in 1 .. H.Last loop
         if A /= I and then Is_Ancestor (A, I)
           and then Min_Level (A) = Min_Level (I)
         then
            Lemma_Skip_Level (A, I);
            Lemma_Grandparent_Level (I);
         end if;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (if Is_Ancestor (B, I)
               then Ordered (Min_Level (B), H.Keys (B), H.Keys (I))));
      end loop;
   end Lemma_Settled_Above;

   procedure Lemma_Settled_Below
     (H : Heap; I : Index; N : Claim_Bound)
   is
      pragma Unreferenced (N);
      --  The bound only narrows the conclusion; the walk down from I is the
      --  same one whatever it is.
   begin
      for D in 1 .. H.Last loop
         if D /= I and then Is_Ancestor (I, D)
           and then not Is_Near (I, D)
         then
            Lemma_Parent_Level (D);
            Lemma_Grandparent_Level (D);
         end if;

         pragma Loop_Invariant
           (for all E in 1 .. D =>
              (if Is_Ancestor (I, E)
               then Ordered (Min_Level (I), H.Keys (I), H.Keys (E))));
      end loop;
   end Lemma_Settled_Below;

   procedure Lemma_Leaf_Placed (H : Heap; I : Index) is null;

   procedure Lemma_Leaf_Promoted (Before, After : Heap; I : Index) is null;

end Heaps.Min_Max;
