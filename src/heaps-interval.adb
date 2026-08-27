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

package body Heaps.Interval with SPARK_Mode is

   package KM renames Key_Multisets;

   ------------------------------------
   -- Weakenings of the heap property --
   ------------------------------------

   --  A sift travels with one key that is not yet where it belongs. Since the
   --  key only ever moves along one side, exactly one of the two nesting
   --  properties is suspended, and only for the node the key currently sits
   --  in: the claims that node makes about its subtree (sift-down), or the
   --  claims its ancestors make about it (sift-up).

   function Nested_Except_Below
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (for all A in 1 .. Node_Count (H) =>
        (for all D in 1 .. Node_Count (H) =>
           (if Is_Ancestor (A, D) and then A /= I
            then Ordered (Min_Side,
                          H.Keys (Slot (H.Last, Min_Side, A)),
                          H.Keys (Slot (H.Last, Min_Side, D))))))
     with Ghost;

   function Nested_Except_Above
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (for all A in 1 .. Node_Count (H) =>
        (for all D in 1 .. Node_Count (H) =>
           (if Is_Ancestor (A, D) and then D /= I
            then Ordered (Min_Side,
                          H.Keys (Slot (H.Last, Min_Side, A)),
                          H.Keys (Slot (H.Last, Min_Side, D))))))
     with Ghost;

   function Heap_Except_Below
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (Is_Paired (H)
      and then Nested_Except_Below (H, Min_Side, I)
      and then Nested_On (H, not Min_Side))
     with Ghost;

   function Heap_Except_Above
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (Is_Paired (H)
      and then Nested_Except_Above (H, Min_Side, I)
      and then Nested_On (H, not Min_Side))
     with Ghost;

   function Fits_Above
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (I = 1
      or else Ordered (not Min_Side,
                       H.Keys (Slot (H.Last, not Min_Side, I)),
                       H.Keys (Slot (H.Last, Min_Side, Parent (I)))))
     with Ghost, Pre => I <= Node_Count (H);
   --  The end of node I that a sift-up does *not* carry still lies inside the
   --  interval of the parent. This is what makes the exchange of two ends
   --  leave two well-formed intervals behind: the key coming down lands next
   --  to a key that is already on the right side of it.

   function Children_Bounded
     (H : Heap; Min_Side : Boolean; I : Index) return Boolean
   is
     (for all J in 1 .. Node_Count (H) =>
        (if Parent (J) = I
         then Ordered (Min_Side,
                       H.Keys (Slot (H.Last, Min_Side, I)),
                       H.Keys (Slot (H.Last, Min_Side, J)))))
     with Ghost, Pre => I <= Node_Count (H);
   --  Node I is where a sift-down comes to rest: it dominates its children,
   --  and hence, one step at a time, its whole subtree

   ---------------------------
   -- Paths through the tree --
   ---------------------------

   function Ridge (A, D : Index) return Index is
     (if D / 2 = A then D else Ridge (A, D / 2))
     with Ghost,
          Pre  => Is_Ancestor (A, D) and then A /= D,
          Post => Parent (Ridge'Result) = A
                  and then Is_Ancestor (Ridge'Result, D)
                  and then Ridge'Result <= D,
          Subprogram_Variant => (Decreases => D);
   --  The child of A the path down to D goes through. Because the nesting
   --  property in its strong form already relates any node to its whole
   --  subtree, one step through this child is all a proof ever needs: there
   --  is no induction down the path to carry out.

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

   procedure Best_Child
     (H : Heap; N : Index; Min_Side : Boolean; C : out Index)
     with Pre  => 2 * N <= Node_Count (H),
          Post => C in 2 * N .. 2 * N + 1
                  and then C <= Node_Count (H)
                  and then (for all J in 1 .. Node_Count (H) =>
                              (if Parent (J) = N
                               then Ordered
                                      (Min_Side,
                                       H.Keys (Slot (H.Last, Min_Side, C)),
                                       H.Keys (Slot (H.Last, Min_Side, J)))));
   --  The child of N whose given end comes first

   procedure Sift_Up (H : in out Heap; Start : Index; Min_Side : Boolean)
     with Pre  => 2 * Start <= H.Last
                  and then Start <= Node_Count (H)
                  and then Heap_Except_Above (H, Min_Side, Start)
                  and then Fits_Above (H, Min_Side, Start),
          Post => Is_Heap (H)
                  and then H.Last = H.Last'Old
                  and then Model (H) = Model (H)'Old;
   --  Carry the given end of node Start up until its ancestors accept it.
   --  Start is required to hold two keys; the callers arrange for that, so
   --  that a lone key -- whose two ends share a slot -- never has to be
   --  considered here.

   procedure Sift_Down (H : in out Heap; Start : Index; Min_Side : Boolean)
     with Pre  => Start <= Node_Count (H)
                  and then Heap_Except_Below (H, Min_Side, Start),
          Post => Is_Heap (H)
                  and then H.Last = H.Last'Old
                  and then Model (H) = Model (H)'Old;

   ---------------------
   -- Steps of a sift --
   ---------------------

   --  The two lemmas below are the heart of the unit: each takes the state
   --  before one elementary rearrangement and the state after it, and says
   --  which weakened property comes out. They are stated on two heap values
   --  rather than on an in-out parameter so that the case analysis has both
   --  states in hand at once.

   procedure Lemma_Step_Up
     (Before, After : Heap; Min_Side : Boolean; I : Index)
     with Ghost,
          Pre  => I > 1
                  and then I <= Node_Count (Before)
                  and then 2 * I <= Before.Last
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Above (Before, Min_Side, I)
                  and then Fits_Above (Before, Min_Side, I)
                  and then Better
                             (Min_Side,
                              Before.Keys (Slot (Before.Last, Min_Side, I)),
                              Before.Keys
                                (Slot (Before.Last, Min_Side, Parent (I))))
                  and then After.Keys
                             (Slot (Before.Last, Min_Side, Parent (I)))
                           = Before.Keys (Slot (Before.Last, Min_Side, I))
                  and then After.Keys (Slot (Before.Last, Min_Side, I))
                           = Before.Keys
                               (Slot (Before.Last, Min_Side, Parent (I)))
                  and then
                    (for all M in 1 .. Before.Last =>
                       (if M /= Slot (Before.Last, Min_Side, I)
                          and M /= Slot (Before.Last, Min_Side, Parent (I))
                        then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Above (After, Min_Side, Parent (I))
                  and then Fits_Above (After, Min_Side, Parent (I));

   procedure Lemma_Step_Down
     (Before, After : Heap; Min_Side : Boolean; I, C : Index)
     with Ghost,
          Pre  => 2 * I <= Node_Count (Before)
                  and then C in 2 * I .. 2 * I + 1
                  and then C <= Node_Count (Before)
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Heap_Except_Below (Before, Min_Side, I)
                  and then
                    (for all J in 1 .. Node_Count (Before) =>
                       (if Parent (J) = I
                        then Ordered
                               (Min_Side,
                                Before.Keys (Slot (Before.Last, Min_Side, C)),
                                Before.Keys
                                  (Slot (Before.Last, Min_Side, J)))))
                  and then Better
                             (Min_Side,
                              Before.Keys (Slot (Before.Last, Min_Side, C)),
                              Before.Keys (Slot (Before.Last, Min_Side, I)))
                  and then After.Keys (Slot (Before.Last, Min_Side, I))
                           = Before.Keys (Slot (Before.Last, Min_Side, C))
                  and then Ordered
                             (Min_Side,
                              After.Keys (Slot (Before.Last, Min_Side, C)),
                              After.Keys
                                (Slot (Before.Last, not Min_Side, C)))
                  and then Ordered
                             (Min_Side,
                              Before.Keys (Slot (Before.Last, Min_Side, C)),
                              After.Keys (Slot (Before.Last, Min_Side, C)))
                  and then Ordered
                             (not Min_Side,
                              Before.Keys
                                (Slot (Before.Last, not Min_Side, I)),
                              After.Keys
                                (Slot (Before.Last, not Min_Side, C)))
                  and then Ordered
                             (not Min_Side,
                              After.Keys
                                (Slot (Before.Last, not Min_Side, C)),
                              Before.Keys
                                (Slot (Before.Last, not Min_Side, C)))
                  and then
                    (for all M in 1 .. Before.Last =>
                       (if M /= Slot (Before.Last, Min_Side, I)
                          and M /= Slot (Before.Last, True, C)
                          and M /= Slot (Before.Last, False, C)
                        then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Below (After, Min_Side, C);
   --  Exchanging one end of a node with the corresponding end of its best
   --  child. The key that comes down may fall outside the child's interval,
   --  in which case it takes the other end of that node and the end it
   --  displaces becomes the key that carries on downwards. What the three
   --  ordering constraints above say is what all the outcomes -- including a
   --  child holding a lone key, whose two ends are one slot -- have in
   --  common: the end of the child that the sift carries on with is no better
   --  than the one it replaces, and the other end of the child stayed between
   --  where it was and the end of the parent that did not move.

   -----------------------
   -- Settling of a sift --
   -----------------------

   procedure Lemma_Settled_Above
     (H : Heap; Min_Side : Boolean; I : Index)
     with Ghost,
          Pre  => I <= Node_Count (H)
                  and then Heap_Except_Above (H, Min_Side, I)
                  and then
                    (I = 1
                     or else Ordered
                               (Min_Side,
                                H.Keys (Slot (H.Last, Min_Side, Parent (I))),
                                H.Keys (Slot (H.Last, Min_Side, I)))),
          Post => Is_Heap (H);

   procedure Lemma_Settled_Below
     (H : Heap; Min_Side : Boolean; I : Index)
     with Ghost,
          Pre  => I <= Node_Count (H)
                  and then Heap_Except_Below (H, Min_Side, I)
                  and then Children_Bounded (H, Min_Side, I),
          Post => Is_Heap (H);

   procedure Lemma_Pair_Completed
     (Before, After : Heap; Min_Side : Boolean; N : Index)
     with Ghost,
          Pre  => Before.Last = 2 * N - 1
                  and then After.Last = 2 * N
                  and then After.Capacity = Before.Capacity
                  and then 2 * N <= After.Capacity
                  and then Is_Heap (Before)
                  and then (for all M in 1 .. Before.Last - 1 =>
                              After.Keys (M) = Before.Keys (M))
                  and then After.Keys
                             (Slot (After.Last, not Min_Side, N))
                           = Before.Keys (Before.Last)
                  and then Ordered
                             (Min_Side,
                              After.Keys (Slot (After.Last, Min_Side, N)),
                              After.Keys
                                (Slot (After.Last, not Min_Side, N))),
          Post => Heap_Except_Above (After, Min_Side, N)
                  and then Fits_Above (After, Min_Side, N);
   --  A second key joins the deepest node. The key that was alone there is
   --  still inside the interval of every node above, whichever end it now
   --  takes, so only the arriving key has anywhere to go.

   procedure Lemma_Leaf_Appended (Before, After : Heap; N : Index)
     with Ghost,
          Pre  => N > 1
                  and then Before.Last = 2 * N - 2
                  and then After.Last = 2 * N - 1
                  and then After.Capacity = Before.Capacity
                  and then 2 * N - 1 <= After.Capacity
                  and then Is_Heap (Before)
                  and then (for all M in 1 .. Before.Last =>
                              After.Keys (M) = Before.Keys (M)),
          Post => Node_Count (After) = N
                  and then Slot (After.Last, True, N) = 2 * N - 1
                  and then Slot (After.Last, False, N) = 2 * N - 1
                  and then Is_Paired (After)
                  and then Nested_Except_Above (After, True, N)
                  and then Nested_Except_Above (After, False, N);
   --  A key appended on its own opens a node holding it as both ends. Nothing
   --  else moves, so the only claims in doubt are those the nodes above make
   --  about the new one.

   procedure Lemma_Leaf_Promoted
     (Before, After : Heap; Min_Side : Boolean; N : Index)
     with Ghost,
          Pre  => N > 1
                  and then N = Node_Count (Before)
                  and then Before.Last = 2 * N - 1
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Is_Paired (Before)
                  and then Nested_Except_Above (Before, True, N)
                  and then Nested_Except_Above (Before, False, N)
                  and then Better
                             (Min_Side,
                              Before.Keys (2 * N - 1),
                              Before.Keys
                                (Slot (Before.Last, Min_Side, Parent (N))))
                  and then After.Keys
                             (Slot (Before.Last, Min_Side, Parent (N)))
                           = Before.Keys (2 * N - 1)
                  and then After.Keys (2 * N - 1)
                           = Before.Keys
                               (Slot (Before.Last, Min_Side, Parent (N)))
                  and then
                    (for all M in 1 .. Before.Last =>
                       (if M /= 2 * N - 1
                          and M /= Slot (Before.Last, Min_Side, Parent (N))
                        then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Above (After, Min_Side, Parent (N))
                  and then Fits_Above (After, Min_Side, Parent (N));
   --  A lone key that went past one end of its parent is exchanged with it.
   --  The end it displaces comes down into a node that has nothing below it
   --  and is bounded by everything above it, so it is where the parent's own
   --  end now sits that the sift carries on.

   procedure Lemma_Leaf_Fits (H : Heap; N : Index)
     with Ghost,
          Pre  => N > 1
                  and then N <= Node_Count (H)
                  and then Is_Paired (H)
                  and then Nested_Except_Above (H, True, N)
                  and then Nested_Except_Above (H, False, N)
                  and then Ordered
                             (True,
                              H.Keys (Slot (H.Last, True, Parent (N))),
                              H.Keys (Slot (H.Last, True, N)))
                  and then Ordered
                             (False,
                              H.Keys (Slot (H.Last, False, Parent (N))),
                              H.Keys (Slot (H.Last, False, N))),
          Post => Is_Heap (H);
   --  A lone key that landed inside the interval of its parent is inside the
   --  interval of every node above it, both ends at once

   -------------------------
   -- Shrinking the array --
   -------------------------

   procedure Lemma_Truncate (Before, After : Heap)
     with Ghost,
          Pre  => Before.Last >= 3
                  and then Is_Heap (Before)
                  and then After.Last = Before.Last - 1
                  and then After.Capacity = Before.Capacity
                  and then (for all M in 1 .. After.Last =>
                              After.Keys (M) = Before.Keys (M)),
          Post => Is_Heap (After);
   --  Dropping the deepest key. The node it came from either disappears or is
   --  left holding a single key, and a lone key is trivially an interval.

   procedure Lemma_Replace_Root
     (Before, After : Heap; Min_Side : Boolean)
     with Ghost,
          Pre  => Before.Last >= 2
                  and then Is_Heap (Before)
                  and then After.Last = Before.Last
                  and then After.Capacity = Before.Capacity
                  and then Ordered
                             (Min_Side,
                              After.Keys (Slot (Before.Last, Min_Side, 1)),
                              Before.Keys
                                (Slot (Before.Last, not Min_Side, 1)))
                  and then (for all M in 1 .. Before.Last =>
                              (if M /= Slot (Before.Last, Min_Side, 1)
                               then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Below (After, Min_Side, 1);
   --  Overwriting one end of the root with a key that still fits under the
   --  other end. Everything below the root is untouched, so the root is the
   --  only node whose claims about its subtree are in doubt.

   procedure Lemma_Drop_Last
     (Before, After : Heap; Min_Side : Boolean)
     with Ghost,
          Pre  => Before.Last >= 3
                  and then Is_Heap (Before)
                  and then After.Last = Before.Last - 1
                  and then After.Capacity = Before.Capacity
                  and then After.Keys (Slot (Before.Last, Min_Side, 1))
                           = Before.Keys (Before.Last)
                  and then (for all M in 1 .. After.Last =>
                              (if M /= Slot (Before.Last, Min_Side, 1)
                               then After.Keys (M) = Before.Keys (M))),
          Post => Heap_Except_Below (After, Min_Side, 1);
   --  What both removals do to the array: the deepest key is dropped and put
   --  back at the end of the root that has just been vacated. It lands inside
   --  the interval of the root, because it was inside it before.

   -----------
   -- Ridge --
   -----------

   --  Nothing to do: the recursive expression function carries its own proof.

   ------------------------------
   -- Lemma_Root_Is_Ancestor   --
   ------------------------------

   procedure Lemma_Root_Is_Ancestor (D : Index) is
   begin
      if D > 1 then
         Lemma_Root_Is_Ancestor (D / 2);
      end if;
   end Lemma_Root_Is_Ancestor;

   -------------------------------
   -- Lemma_Ancestor_Transitive --
   -------------------------------

   procedure Lemma_Ancestor_Transitive (A, B, D : Index) is
   begin
      if B /= D then
         Lemma_Ancestor_Transitive (A, B, D / 2);
      end if;
   end Lemma_Ancestor_Transitive;

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

   ----------------
   -- Best_Child --
   ----------------

   procedure Best_Child
     (H : Heap; N : Index; Min_Side : Boolean; C : out Index)
   is
      Right : constant Index := 2 * N + 1;
   begin
      C := 2 * N;

      if Right <= Node_Count (H)
        and then Better (Min_Side,
                         H.Keys (Slot (H.Last, Min_Side, Right)),
                         H.Keys (Slot (H.Last, Min_Side, C)))
      then
         C := Right;
      end if;

      --  The children of N are exactly the two nodes 2 * N and 2 * N + 1

      pragma Assert
        (for all J in 1 .. Node_Count (H) =>
           (if Parent (J) = N then J = 2 * N or else J = Right));
   end Best_Child;

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
         declare
            N : constant Index := Node_Of (I);
         begin
            Lemma_Root_Is_Ancestor (N);
            pragma Assert (I = Slot (H.Last, True, N)
                           or else I = Slot (H.Last, False, N));
         end;

         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (1) <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   ---------------------------
   -- Lemma_Root_Is_Maximum --
   ---------------------------

   procedure Lemma_Root_Is_Maximum (H : Heap) is
   begin
      for I in 1 .. H.Last loop
         declare
            N : constant Index := Node_Of (I);
         begin
            Lemma_Root_Is_Ancestor (N);
            pragma Assert (I = Slot (H.Last, True, N)
                           or else I = Slot (H.Last, False, N));
         end;

         pragma Loop_Invariant
           (for all J in 1 .. I => H.Keys (J) <= H.Keys (Max_Index (H)));
      end loop;
   end Lemma_Root_Is_Maximum;

   -------------
   -- Sift_Up --
   -------------

   procedure Sift_Up (H : in out Heap; Start : Index; Min_Side : Boolean) is
      I : Index := Start;
   begin
      while I > 1
        and then Better (Min_Side,
                         H.Keys (Slot (H.Last, Min_Side, I)),
                         H.Keys (Slot (H.Last, Min_Side, Parent (I))))
      loop
         pragma Loop_Invariant (I <= Node_Count (H));
         pragma Loop_Invariant (2 * I <= H.Last);
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (Heap_Except_Above (H, Min_Side, I));
         pragma Loop_Invariant (Fits_Above (H, Min_Side, I));
         pragma Loop_Invariant (Model (H) = Model (H)'Loop_Entry);
         pragma Loop_Variant (Decreases => I);

         declare
            P      : constant Index := Parent (I);
            Before : constant Heap  := H with Ghost;
         begin
            Swap (H,
                  Slot (H.Last, Min_Side, P),
                  Slot (H.Last, Min_Side, I));
            Lemma_Step_Up (Before, H, Min_Side, I);
            I := P;
         end;
      end loop;

      Lemma_Settled_Above (H, Min_Side, I);
   end Sift_Up;

   ---------------
   -- Sift_Down --
   ---------------

   procedure Sift_Down (H : in out Heap; Start : Index; Min_Side : Boolean) is
      I : Index := Start;
      C : Index;
   begin
      loop
         pragma Loop_Invariant (I <= Node_Count (H));
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (Heap_Except_Below (H, Min_Side, I));
         pragma Loop_Invariant (Model (H) = Model (H)'Loop_Entry);
         pragma Loop_Variant (Increases => I);

         if 2 * I > Node_Count (H) then
            pragma Assert (for all J in 1 .. Node_Count (H) => Parent (J) /= I);
            pragma Assert (Children_Bounded (H, Min_Side, I));
            exit;
         end if;

         Best_Child (H, I, Min_Side, C);

         if not Better (Min_Side,
                        H.Keys (Slot (H.Last, Min_Side, C)),
                        H.Keys (Slot (H.Last, Min_Side, I)))
         then
            pragma Assert (Children_Bounded (H, Min_Side, I));
            exit;
         end if;

         declare
            Before : constant Heap := H with Ghost;
         begin
            Swap (H,
                  Slot (H.Last, Min_Side, I),
                  Slot (H.Last, Min_Side, C));

            if H.Keys (Slot (H.Last, True, C))
               > H.Keys (Slot (H.Last, False, C))
            then
               --  The key that came down went past the far end of the child;
               --  it takes that end, and the key it displaces is the one that
               --  carries on downwards.

               pragma Assert (Slot (H.Last, False, C) = 2 * C);
               Swap (H,
                     Slot (H.Last, True, C),
                     Slot (H.Last, False, C));

               pragma Assert
                 (H.Keys (Slot (H.Last, Min_Side, C))
                  = Before.Keys (Slot (H.Last, not Min_Side, C))
                  and then H.Keys (Slot (H.Last, not Min_Side, C))
                           = Before.Keys (Slot (H.Last, Min_Side, I)));
            else

               --  Either the child holds two keys and the one that came down
               --  fits between them, or it holds a lone key, which is now
               --  that very key.

               pragma Assert
                 (H.Keys (Slot (H.Last, Min_Side, C))
                  = Before.Keys (Slot (H.Last, Min_Side, I)));
               pragma Assert
                 (H.Keys (Slot (H.Last, not Min_Side, C))
                  = Before.Keys (Slot (H.Last, Min_Side, I))
                  or else H.Keys (Slot (H.Last, not Min_Side, C))
                          = Before.Keys (Slot (H.Last, not Min_Side, C)));
            end if;

            pragma Assert (H.Keys (Slot (H.Last, True, C))
                           <= H.Keys (Slot (H.Last, False, C)));

            --  The key the sift carries on with is no better than the end of
            --  the child it replaces, and the other end of the child stayed
            --  inside the interval the parent kept.

            pragma Assert
              (Ordered (not Min_Side,
                        Before.Keys (Slot (H.Last, not Min_Side, I)),
                        Before.Keys (Slot (H.Last, Min_Side, I))));
            pragma Assert
              (Ordered (not Min_Side,
                        Before.Keys (Slot (H.Last, not Min_Side, I)),
                        Before.Keys (Slot (H.Last, not Min_Side, C))));

            Lemma_Step_Down (Before, H, Min_Side, I, C);
            I := C;
         end;
      end loop;

      Lemma_Settled_Below (H, Min_Side, I);
   end Sift_Down;

   ------------
   -- Insert --
   ------------

   procedure Insert (H : in out Heap; K : Key_Type) is
      Base   : constant KM.Multiset := Model (H) with Ghost;
      Old_A  : constant Key_Array   := H.Keys with Ghost;
      Before : constant Heap        := H with Ghost;
      P      : constant Index       := H.Last + 1;
      N      : constant Index       := Node_Of (P);
   begin
      H.Keys (P) := K;
      Models.Lemma_Same_Prefix (Old_A, H.Keys, H.Last);
      H.Last := P;

      pragma Assert (Model (H) = KM.Add (Base, K));
      pragma Assert (N = Node_Count (H));

      if P = 2 * N then

         --  The deepest node was holding a single key and now holds two. The
         --  key that was already there stays inside the interval of every
         --  node above, so only the end K takes can be out of place, and it
         --  is that end which travels up.

         if K < H.Keys (2 * N - 1) then
            Swap (H, 2 * N - 1, 2 * N);
            Lemma_Pair_Completed (Before, H, True, N);

            if N > 1 then
               Sift_Up (H, N, True);
            end if;
         else
            Lemma_Pair_Completed (Before, H, False, N);

            if N > 1 then
               Sift_Up (H, N, False);
            end if;
         end if;

      elsif N = 1 then

         --  The first key of the heap: a node on its own, with nothing above
         --  it and nothing below.

         null;

      else

         --  K opens a node of its own and is both of its ends. If it fits
         --  inside the interval of the parent there is nothing to do;
         --  otherwise it is exchanged with the end of the parent it went
         --  past, and that end -- now holding K -- travels up.

         declare
            Q   : constant Index := Parent (N);
            Mid : constant Heap  := H with Ghost;
         begin
            Lemma_Leaf_Appended (Before, H, N);

            if K < H.Keys (Slot (H.Last, True, Q)) then
               Swap (H, Slot (H.Last, True, Q), P);
               Lemma_Leaf_Promoted (Mid, H, True, N);
               Sift_Up (H, Q, True);

            elsif K > H.Keys (Slot (H.Last, False, Q)) then
               Swap (H, Slot (H.Last, False, Q), P);
               Lemma_Leaf_Promoted (Mid, H, False, N);
               Sift_Up (H, Q, False);

            else
               Lemma_Leaf_Fits (H, N);
            end if;
         end;
      end if;
   end Insert;

   -----------------
   -- Extract_Min --
   -----------------

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Base   : constant KM.Multiset := Model (H) with Ghost;
      Old_A  : constant Key_Array   := H.Keys with Ghost;
      Before : constant Heap        := H with Ghost;
      Moved  : constant Key_Type    := H.Keys (H.Last);
   begin
      Lemma_Root_Is_Minimum (H);

      K := H.Keys (1);
      H.Keys (1) := Moved;
      Models.Lemma_Set (Old_A, H.Keys, 1, H.Last);
      H.Last := H.Last - 1;

      pragma Assert (KM.Add (Model (H), Moved)
                     = Models.Occurrences (H.Keys, H.Last + 1));
      Models.Lemma_Add_Commutes (Model (H), Moved, K);
      Models.Lemma_Add_Cancels (KM.Add (Model (H), K), Base, Moved);

      if H.Last >= 2 then
         Lemma_Drop_Last (Before, H, True);
         Sift_Down (H, 1, True);
      end if;
   end Extract_Min;

   -----------------
   -- Extract_Max --
   -----------------

   procedure Extract_Max (H : in out Heap; K : out Key_Type) is
      Base   : constant KM.Multiset := Model (H) with Ghost;
      Old_A  : constant Key_Array   := H.Keys with Ghost;
      Before : constant Heap        := H with Ghost;
      Moved  : constant Key_Type    := H.Keys (H.Last);
      T      : constant Index       := Max_Index (H);
   begin
      Lemma_Root_Is_Maximum (H);

      K := H.Keys (T);
      H.Keys (T) := Moved;
      Models.Lemma_Set (Old_A, H.Keys, T, H.Last);
      H.Last := H.Last - 1;

      pragma Assert (KM.Add (Model (H), Moved)
                     = Models.Occurrences (H.Keys, H.Last + 1));
      Models.Lemma_Add_Commutes (Model (H), Moved, K);
      Models.Lemma_Add_Cancels (KM.Add (Model (H), K), Base, Moved);

      if H.Last >= 2 then
         Lemma_Drop_Last (Before, H, False);
         Sift_Down (H, 1, False);
      end if;
   end Extract_Max;


   -------------------------------------------------------------------
   -- The case analyses behind the sift steps                       --
   -------------------------------------------------------------------

   procedure Lemma_Step_Up
     (Before, After : Heap; Min_Side : Boolean; I : Index)
   is
      S : constant Boolean         := Min_Side;
      L : constant Extended_Index  := Before.Last;
      P : constant Index           := Parent (I);
   begin
      --  Both nodes hold two keys, so the side that is not being carried
      --  keeps its slot in each of them, and the two slots that change are
      --  the only ones on side S that move.

      pragma Assert (2 * P <= L);
      pragma Assert (Slot (L, not S, I) /= Slot (L, S, I));
      pragma Assert (Slot (L, not S, P) /= Slot (L, S, P));

      for M in 1 .. Node_Count (After) loop
         pragma Assert (After.Keys (Slot (L, not S, M))
                        = Before.Keys (Slot (L, not S, M)));
         pragma Assert (if M /= I and then M /= P
                        then After.Keys (Slot (L, S, M))
                             = Before.Keys (Slot (L, S, M)));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              After.Keys (Slot (L, not S, B))
              = Before.Keys (Slot (L, not S, B))
              and then (if B /= I and then B /= P
                        then After.Keys (Slot (L, S, B))
                             = Before.Keys (Slot (L, S, B))));
      end loop;

      pragma Assert (Nested_On (After, not S));

      --  Each of the two nodes ends up holding a well-formed interval: the
      --  key that comes down was already on the right side of the end it
      --  lands next to, and the key that goes up was on the right side of the
      --  end it now shares a node with.

      for M in 1 .. Node_Count (After) loop
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              After.Keys (Slot (L, True, B)) <= After.Keys (Slot (L, False, B)));
      end loop;

      pragma Assert (Is_Paired (After));

      for A in 1 .. Node_Count (After) loop
         for D in 1 .. Node_Count (After) loop

            if Is_Ancestor (A, D) and then D /= P then
               if A = I then

                  --  I now holds what P held, and P is above everything I is
                  --  above.

                  Lemma_Ancestor_Transitive (P, I, D);

               elsif A = P and then D /= I then

                  --  P now holds what I held, which was better than what P
                  --  held, and P dominated the rest of its subtree already.

                  pragma Assert
                    (Ordered (S, Before.Keys (Slot (L, S, P)),
                                 Before.Keys (Slot (L, S, D))));

               elsif A /= P and then D = I then

                  --  Above the pair nothing moved, and I now holds what P
                  --  held.

                  pragma Assert (Is_Ancestor (A, P));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E) and then E /= P
                  then Ordered (S, After.Keys (Slot (L, S, A)),
                                   After.Keys (Slot (L, S, E)))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E) and then E /= P
                  then Ordered (S, After.Keys (Slot (L, S, B)),
                                   After.Keys (Slot (L, S, E))))));
      end loop;
   end Lemma_Step_Up;

   procedure Lemma_Step_Down
     (Before, After : Heap; Min_Side : Boolean; I, C : Index)
   is
      S : constant Boolean        := Min_Side;
      L : constant Extended_Index := Before.Last;
   begin
      pragma Assert (2 * I <= L);
      pragma Assert (Parent (C) = I);
      pragma Assert (Slot (L, not S, I) /= Slot (L, S, I));
      pragma Assert (Slot (L, not S, I) /= Slot (L, True, C));
      pragma Assert (Slot (L, not S, I) /= Slot (L, False, C));

      --  Outside the two nodes nothing changed at all.

      for M in 1 .. Node_Count (After) loop
         pragma Assert (if M /= I and then M /= C
                        then After.Keys (Slot (L, True, M))
                             = Before.Keys (Slot (L, True, M))
                             and then After.Keys (Slot (L, False, M))
                                      = Before.Keys (Slot (L, False, M)));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              (if B /= I and then B /= C
               then After.Keys (Slot (L, True, B))
                    = Before.Keys (Slot (L, True, B))
                    and then After.Keys (Slot (L, False, B))
                             = Before.Keys (Slot (L, False, B))));
      end loop;

      pragma Assert (After.Keys (Slot (L, not S, I))
                     = Before.Keys (Slot (L, not S, I)));

      --  Node I is still a well-formed interval, and node C was repaired on
      --  the way.

      for M in 1 .. Node_Count (After) loop
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              After.Keys (Slot (L, True, B))
              <= After.Keys (Slot (L, False, B)));
      end loop;

      pragma Assert (Is_Paired (After));

      --  The key that came down cannot have gone past the end of node I that
      --  stayed behind, so wherever it ended up in node C it is still inside
      --  the interval of every node above.

      pragma Assert
        (Ordered (not S, After.Keys (Slot (L, not S, I)),
                         After.Keys (Slot (L, not S, C))));

      for A in 1 .. Node_Count (After) loop
         for D in 1 .. Node_Count (After) loop

            if Is_Ancestor (A, D) then
               if A = C then
                  pragma Assert
                    (Ordered (not S, After.Keys (Slot (L, not S, A)),
                                     After.Keys (Slot (L, not S, D))));
               elsif D = C or else D = I then
                  pragma Assert (A = I or else Is_Ancestor (A, I));
                  pragma Assert
                    (Ordered (not S, After.Keys (Slot (L, not S, A)),
                                     After.Keys (Slot (L, not S, D))));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E)
                  then Ordered (not S, After.Keys (Slot (L, not S, A)),
                                       After.Keys (Slot (L, not S, E)))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E)
                  then Ordered (not S, After.Keys (Slot (L, not S, B)),
                                       After.Keys (Slot (L, not S, E))))));
      end loop;

      pragma Assert (Nested_On (After, not S));

      for A in 1 .. Node_Count (After) loop
         for D in 1 .. Node_Count (After) loop

            if Is_Ancestor (A, D) and then A /= C then
               if A = I and then D /= I then

                  --  I holds the best end among its children, so it bounds
                  --  both subtrees below it; which one D sits in is what the
                  --  child on the path down to it tells.

                  declare
                     J : constant Index := Ridge (I, D);
                  begin
                     pragma Assert (Parent (J) = I);
                     pragma Assert (J <= Node_Count (After));
                     pragma Assert
                       (Ordered (S, Before.Keys (Slot (L, S, C)),
                                    Before.Keys (Slot (L, S, J))));
                     pragma Assert (if J /= C then D /= C);
                  end;

               elsif A /= I and then (D = I or else D = C) then

                  --  Above the pair nothing moved, and both keys that ended
                  --  up there came from inside the interval of node I.

                  pragma Assert (Is_Ancestor (A, I));
                  pragma Assert
                    (Ordered (S, After.Keys (Slot (L, S, A)),
                                 Before.Keys (Slot (L, S, C))));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E) and then A /= C
                  then Ordered (S, After.Keys (Slot (L, S, A)),
                                   After.Keys (Slot (L, S, E)))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E) and then B /= C
                  then Ordered (S, After.Keys (Slot (L, S, B)),
                                   After.Keys (Slot (L, S, E))))));
      end loop;
   end Lemma_Step_Down;

   --------------------------
   -- Lemma_Settled_Above  --
   --------------------------

   procedure Lemma_Settled_Above (H : Heap; Min_Side : Boolean; I : Index) is
   begin
      for A in 1 .. Node_Count (H) loop
         if A /= I and then Is_Ancestor (A, I) then
            pragma Assert (Is_Ancestor (A, Parent (I)));
         end if;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (if Is_Ancestor (B, I)
               then Ordered (Min_Side,
                             H.Keys (Slot (H.Last, Min_Side, B)),
                             H.Keys (Slot (H.Last, Min_Side, I)))));
      end loop;
   end Lemma_Settled_Above;

   --------------------------
   -- Lemma_Settled_Below  --
   --------------------------

   procedure Lemma_Settled_Below (H : Heap; Min_Side : Boolean; I : Index) is
   begin
      for D in 1 .. Node_Count (H) loop
         if D /= I and then Is_Ancestor (I, D) then
            declare
               J : constant Index := Ridge (I, D);
            begin
               pragma Assert (Parent (J) = I);
               pragma Assert (J <= Node_Count (H));
               pragma Assert (Is_Ancestor (J, D));
            end;
         end if;

         pragma Loop_Invariant
           (for all E in 1 .. D =>
              (if Is_Ancestor (I, E)
               then Ordered (Min_Side,
                             H.Keys (Slot (H.Last, Min_Side, I)),
                             H.Keys (Slot (H.Last, Min_Side, E)))));
      end loop;
   end Lemma_Settled_Below;

   ---------------------------
   -- Lemma_Pair_Completed  --
   ---------------------------

   procedure Lemma_Pair_Completed
     (Before, After : Heap; Min_Side : Boolean; N : Index)
   is
      S  : constant Boolean        := Min_Side;
      LB : constant Extended_Index := Before.Last;
      LA : constant Extended_Index := After.Last;
   begin
      pragma Assert (Node_Count (Before) = N);
      pragma Assert (Node_Count (After) = N);
      pragma Assert (Slot (LB, True, N) = LB and then Slot (LB, False, N) = LB);

      --  Below the deepest node nothing moved at all.

      for M in 1 .. N - 1 loop
         pragma Assert (Slot (LA, True, M) = Slot (LB, True, M)
                        and then Slot (LA, False, M) = Slot (LB, False, M));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              Slot (LA, True, B) = Slot (LB, True, B)
              and then Slot (LA, False, B) = Slot (LB, False, B)
              and then After.Keys (Slot (LA, True, B))
                       = Before.Keys (Slot (LB, True, B))
              and then After.Keys (Slot (LA, False, B))
                       = Before.Keys (Slot (LB, False, B)));
      end loop;

      --  The deepest node keeps, on the side the new key did not take, the
      --  very key it was holding on its own.

      pragma Assert (After.Keys (Slot (LA, not S, N))
                     = Before.Keys (Slot (LB, not S, N)));
      pragma Assert (Is_Paired (After));
      pragma Assert (Nested_On (After, not S));
      pragma Assert (Nested_Except_Above (After, S, N));
   end Lemma_Pair_Completed;

   --------------------------
   -- Lemma_Leaf_Appended  --
   --------------------------

   procedure Lemma_Leaf_Appended (Before, After : Heap; N : Index) is
      LB : constant Extended_Index := Before.Last;
      LA : constant Extended_Index := After.Last;
   begin
      pragma Assert (Node_Count (Before) = N - 1);
      pragma Assert (Node_Count (After) = N);

      for M in 1 .. N - 1 loop
         pragma Assert (Slot (LA, True, M) = Slot (LB, True, M)
                        and then Slot (LA, False, M) = Slot (LB, False, M));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              Slot (LA, True, B) = Slot (LB, True, B)
              and then Slot (LA, False, B) = Slot (LB, False, B)
              and then After.Keys (Slot (LA, True, B))
                       = Before.Keys (Slot (LB, True, B))
              and then After.Keys (Slot (LA, False, B))
                       = Before.Keys (Slot (LB, False, B)));
      end loop;

      --  The new node is a leaf, so the only claims it takes part in are
      --  those made about it from above.

      pragma Assert (for all D in 1 .. N => (if Is_Ancestor (N, D) then D = N));
      pragma Assert (Is_Paired (After));
      pragma Assert (Nested_Except_Above (After, True, N));
      pragma Assert (Nested_Except_Above (After, False, N));
   end Lemma_Leaf_Appended;

   --------------------------
   -- Lemma_Leaf_Promoted  --
   --------------------------

   procedure Lemma_Leaf_Promoted
     (Before, After : Heap; Min_Side : Boolean; N : Index)
   is
      S : constant Boolean        := Min_Side;
      L : constant Extended_Index := Before.Last;
      Q : constant Index          := Parent (N);
   begin
      pragma Assert (2 * Q <= L);
      pragma Assert (Slot (L, True, N) = 2 * N - 1
                     and then Slot (L, False, N) = 2 * N - 1);
      pragma Assert (Slot (L, not S, Q) /= Slot (L, S, Q));

      for M in 1 .. Node_Count (After) loop
         pragma Assert (if M /= N and then M /= Q
                        then After.Keys (Slot (L, True, M))
                             = Before.Keys (Slot (L, True, M))
                             and then After.Keys (Slot (L, False, M))
                                      = Before.Keys (Slot (L, False, M)));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              (if B /= N and then B /= Q
               then After.Keys (Slot (L, True, B))
                    = Before.Keys (Slot (L, True, B))
                    and then After.Keys (Slot (L, False, B))
                             = Before.Keys (Slot (L, False, B))));
      end loop;

      pragma Assert (After.Keys (Slot (L, not S, Q))
                     = Before.Keys (Slot (L, not S, Q)));
      pragma Assert (Is_Paired (After));

      --  The end that came down lands in a node with nothing below it, and it
      --  was inside the interval of every node above already.

      for A in 1 .. Node_Count (After) loop
         if A /= N and then Is_Ancestor (A, N) then
            pragma Assert (Is_Ancestor (A, Q));
         end if;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E)
                  then Ordered (not S, After.Keys (Slot (L, not S, B)),
                                       After.Keys (Slot (L, not S, E))))));
      end loop;

      pragma Assert (Nested_On (After, not S));

      for A in 1 .. Node_Count (After) loop
         for D in 1 .. Node_Count (After) loop

            if Is_Ancestor (A, D) and then D /= Q then
               if A /= Q and then A /= N and then D = N then
                  pragma Assert (Is_Ancestor (A, Q));
               end if;
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E) and then E /= Q
                  then Ordered (S, After.Keys (Slot (L, S, A)),
                                   After.Keys (Slot (L, S, E)))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E) and then E /= Q
                  then Ordered (S, After.Keys (Slot (L, S, B)),
                                   After.Keys (Slot (L, S, E))))));
      end loop;
   end Lemma_Leaf_Promoted;

   -----------------------
   -- Lemma_Leaf_Fits   --
   -----------------------

   procedure Lemma_Leaf_Fits (H : Heap; N : Index) is
   begin
      for A in 1 .. Node_Count (H) loop
         if A /= N and then Is_Ancestor (A, N) then
            pragma Assert (Is_Ancestor (A, Parent (N)));
         end if;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (if Is_Ancestor (B, N)
               then Ordered (True, H.Keys (Slot (H.Last, True, B)),
                                   H.Keys (Slot (H.Last, True, N)))
                    and then
                    Ordered (False, H.Keys (Slot (H.Last, False, B)),
                                    H.Keys (Slot (H.Last, False, N)))));
      end loop;
   end Lemma_Leaf_Fits;

   ---------------------
   -- Lemma_Truncate  --
   ---------------------

   procedure Lemma_Truncate (Before, After : Heap) is
      LB : constant Extended_Index := Before.Last;
      LA : constant Extended_Index := After.Last;
   begin
      --  Only the node the dropped key belonged to can see its slots move,
      --  and it then holds a single key, which is an interval by itself.

      for M in 1 .. Node_Count (After) loop
         pragma Assert (Slot (LA, True, M) = Slot (LB, True, M));
         pragma Assert
           (if 2 * M /= LB
            then Slot (LA, False, M) = Slot (LB, False, M)
            else Slot (LA, False, M) = Slot (LA, True, M));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              Slot (LA, True, B) = Slot (LB, True, B)
              and then (if 2 * B /= LB
                        then Slot (LA, False, B) = Slot (LB, False, B)
                        else Slot (LA, False, B) = Slot (LA, True, B)));
      end loop;

      pragma Assert (Is_Paired (After));
      pragma Assert (Nested_On (After, True));

      for A in 1 .. Node_Count (After) loop
         for D in 1 .. Node_Count (After) loop

            if Is_Ancestor (A, D) and then 2 * D = LB then
               pragma Assert (Before.Keys (Slot (LB, True, D))
                              <= Before.Keys (Slot (LB, False, D)));
            end if;

            pragma Loop_Invariant
              (for all E in 1 .. D =>
                 (if Is_Ancestor (A, E)
                  then Ordered (False, After.Keys (Slot (LA, False, A)),
                                       After.Keys (Slot (LA, False, E)))));
         end loop;

         pragma Loop_Invariant
           (for all B in 1 .. A =>
              (for all E in 1 .. Node_Count (After) =>
                 (if Is_Ancestor (B, E)
                  then Ordered (False, After.Keys (Slot (LA, False, B)),
                                       After.Keys (Slot (LA, False, E))))));
      end loop;
   end Lemma_Truncate;

   -------------------------
   -- Lemma_Replace_Root  --
   -------------------------

   procedure Lemma_Replace_Root
     (Before, After : Heap; Min_Side : Boolean) is
      L : constant Extended_Index := Before.Last;
      S : constant Boolean        := Min_Side;
   begin
      pragma Assert (Slot (L, True, 1) = 1 and then Slot (L, False, 1) = 2);

      for M in 1 .. Node_Count (After) loop
         pragma Assert (if M /= 1
                        then After.Keys (Slot (L, True, M))
                             = Before.Keys (Slot (L, True, M))
                             and then After.Keys (Slot (L, False, M))
                                      = Before.Keys (Slot (L, False, M)));
         pragma Loop_Invariant
           (for all B in 1 .. M =>
              (if B /= 1
               then After.Keys (Slot (L, True, B))
                    = Before.Keys (Slot (L, True, B))
                    and then After.Keys (Slot (L, False, B))
                             = Before.Keys (Slot (L, False, B))));
      end loop;

      pragma Assert (After.Keys (Slot (L, not S, 1))
                     = Before.Keys (Slot (L, not S, 1)));
      pragma Assert (Is_Paired (After));
      pragma Assert (Nested_On (After, not S));
   end Lemma_Replace_Root;

   ----------------------
   -- Lemma_Drop_Last  --
   ----------------------

   procedure Lemma_Drop_Last
     (Before, After : Heap; Min_Side : Boolean)
   is
      L   : constant Extended_Index := Before.Last;
      S   : constant Boolean        := Min_Side;
      W   : constant Index          := Node_Of (L);
      Mid : Heap (Before.Capacity)  := Before;
   begin
      Mid.Last := L - 1;
      Lemma_Truncate (Before, Mid);

      --  The key that moves up to the root was inside the interval of the
      --  root, so it still fits under the end that stays.

      Lemma_Root_Is_Ancestor (W);
      pragma Assert (Slot (L, False, W) = L);
      pragma Assert (Before.Keys (Slot (L, True, W)) <= Before.Keys (L));
      pragma Assert (Before.Keys (L) <= Before.Keys (Slot (L, False, 1)));
      pragma Assert (Before.Keys (Slot (L, True, 1))
                     <= Before.Keys (Slot (L, True, W)));
      pragma Assert (Slot (Mid.Last, S, 1) = Slot (L, S, 1));
      pragma Assert (Slot (Mid.Last, not S, 1) = Slot (L, not S, 1));

      Lemma_Replace_Root (Mid, After, S);
   end Lemma_Drop_Last;

end Heaps.Interval;
