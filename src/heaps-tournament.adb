--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Tournament with SPARK_Mode is

   package KM renames Key_Multisets;

   function Valid_Except_Through
     (H : Heap; Bad : Tree_Index_Base; Last_Node : Extended_Index)
      return Boolean is
     (if Last_Node = 0 then True
      elsif Last_Node = Bad then
        Valid_Except_Through (H, Bad, Last_Node - 1)
      else Node_Valid (H, Last_Node)
        and then Valid_Except_Through (H, Bad, Last_Node - 1))
     with Ghost,
          Pre => Last_Node <= Internal_Last (H),
          Subprogram_Variant => (Decreases => Last_Node);

   function Valid_Except (H : Heap; Bad : Tree_Index_Base) return Boolean is
     (if Bad = 0 then Is_Heap (H)
      else Valid_Except_Through (H, Bad, Internal_Last (H)))
     with Ghost;

   function Valid_From (H : Heap; First : Extended_Index) return Boolean is
     (if First <= 1 then Is_Heap (H)
      else Valid_Range (H, First, Internal_Last (H)))
     with Ghost;

   procedure Lemma_Heap_Node (H : Heap; Node : Index)
     with Ghost,
          Pre  => Is_Heap (H) and then Node < H.Capacity,
          Post => Node_Valid (H, Node);

   procedure Lemma_Heap_Node (H : Heap; Node : Index) is
      procedure Prove (Last_Node : Extended_Index)
        with Ghost,
             Pre  => Last_Node <= Internal_Last (H)
                     and then Node <= Last_Node
                     and then Valid_Range (H, 1, Last_Node),
             Post => Node_Valid (H, Node),
             Subprogram_Variant => (Decreases => Last_Node);

      procedure Prove (Last_Node : Extended_Index) is
      begin
         if Last_Node /= Node then
            Prove (Last_Node - 1);
         end if;
      end Prove;
   begin
      Prove (Internal_Last (H));
   end Lemma_Heap_Node;

   procedure Lemma_Except_Node
     (H : Heap; Bad : Tree_Index_Base; Node : Index)
     with Ghost,
          Pre  => Bad > 0
                  and then Valid_Except (H, Bad)
                  and then Node < H.Capacity
                  and then Node /= Bad,
          Post => Node_Valid (H, Node);

   procedure Lemma_Except_Node
     (H : Heap; Bad : Tree_Index_Base; Node : Index) is
      procedure Prove (Last_Node : Extended_Index)
        with Ghost,
             Pre  => Last_Node <= Internal_Last (H)
                     and then Node <= Last_Node
                     and then Node /= Bad
                     and then Valid_Except_Through (H, Bad, Last_Node),
             Post => Node_Valid (H, Node),
             Subprogram_Variant => (Decreases => Last_Node);

      procedure Prove (Last_Node : Extended_Index) is
      begin
         if Last_Node /= Node then
            Prove (Last_Node - 1);
         end if;
      end Prove;
   begin
      Prove (Internal_Last (H));
   end Lemma_Except_Node;

   procedure Lemma_From_Node
      (H : Heap; First : Extended_Index; Node : Index)
     with Ghost,
          Pre  => First > 1
                  and then Valid_From (H, First)
                  and then Node >= First
                  and then Node < H.Capacity,
          Post => Node_Valid (H, Node);

   procedure Lemma_From_Node
     (H : Heap; First : Extended_Index; Node : Index) is
      procedure Prove (Last_Node : Extended_Index)
        with Ghost,
             Pre  => First > 0
                     and then Last_Node <= Internal_Last (H)
                     and then Node in First .. Last_Node
                     and then Valid_Range (H, First, Last_Node),
             Post => Node_Valid (H, Node),
             Subprogram_Variant => (Decreases => Last_Node);

      procedure Prove (Last_Node : Extended_Index) is
      begin
         if Last_Node /= Node then
            Prove (Last_Node - 1);
         end if;
      end Prove;
   begin
      Prove (Internal_Last (H));
   end Lemma_From_Node;

   procedure Lemma_Prepend_Range (H : Heap; First : Index)
     with Ghost,
          Pre  => First <= Internal_Last (H)
                  and then Node_Valid (H, First)
                  and then Valid_Range
                    (H, First + 1, Internal_Last (H)),
          Post => Valid_Range (H, First, Internal_Last (H));

   procedure Lemma_Prepend_Range (H : Heap; First : Index) is
      procedure Prove (Last_Node : Extended_Index)
        with Ghost,
             Pre  => Last_Node in First .. Internal_Last (H)
                     and then Node_Valid (H, First)
                     and then Valid_Range (H, First + 1, Last_Node),
             Post => Valid_Range (H, First, Last_Node),
             Subprogram_Variant => (Decreases => Last_Node);

      procedure Prove (Last_Node : Extended_Index) is
      begin
         if Last_Node > First then
            Prove (Last_Node - 1);
         end if;
      end Prove;
   begin
      Prove (Internal_Last (H));
   end Lemma_Prepend_Range;

   procedure Recompute (H : in out Heap; Node : Index)
     with Pre  => H.Capacity > 1 and then Node < H.Capacity,
          Post => Node_Valid (H, Node)
                  and H.Last = H.Last'Old
                  and H.Keys = H.Keys'Old
                  and (for all I in H.Winners'Range =>
                         (if I /= Node then
                            H.Winners (I) = H.Winners'Old (I)
                            and H.Winner_Keys (I) = H.Winner_Keys'Old (I)));

   procedure Recompute (H : in out Heap; Node : Index) is
      Left  : constant Tree_Index := 2 * Node;
      Right : constant Tree_Index := Left + 1;
      LP    : constant Extended_Index := Position_At (H, Left);
      RP    : constant Extended_Index := Position_At (H, Right);
   begin
      if LP = 0 then
         if RP = 0 then
            H.Winners (Node) := 0;
         else
            H.Winners (Node) := RP;
            H.Winner_Keys (Node) := Key_At (H, Right);
         end if;
      elsif RP = 0 or else Key_At (H, Left) <= Key_At (H, Right) then
         H.Winners (Node) := LP;
         H.Winner_Keys (Node) := Key_At (H, Left);
      else
         H.Winners (Node) := RP;
         H.Winner_Keys (Node) := Key_At (H, Right);
      end if;
   end Recompute;

   procedure Lemma_Recomputed_Frame
     (Before, After : Heap; Changed : Index)
     with Ghost,
          Pre  => Before.Capacity = After.Capacity
                  and then Before.Last = After.Last
                  and then Before.Keys = After.Keys
                  and then Changed < After.Capacity
                  and then Node_Valid (After, Changed)
                  and then Valid_Except (Before, Changed)
                  and then
                    (for all I in After.Winners'Range =>
                       (if I /= Changed then
                          After.Winners (I) = Before.Winners (I)
                          and After.Winner_Keys (I) = Before.Winner_Keys (I))),
          Post => Valid_Except (After, Changed / 2);

   procedure Lemma_Node_Unchanged
     (Before, After : Heap; Node : Index)
     with Ghost,
          Pre  => Before.Capacity = After.Capacity
                  and then Node < After.Capacity
                  and then Node_Valid (Before, Node)
                  and then Position_At (After, Node)
                             = Position_At (Before, Node)
                  and then Position_At (After, 2 * Node)
                             = Position_At (Before, 2 * Node)
                  and then Position_At (After, 2 * Node + 1)
                             = Position_At (Before, 2 * Node + 1)
                  and then
                    (if Position_At (After, Node) > 0 then
                       Key_At (After, Node) = Key_At (Before, Node))
                  and then
                    (if Position_At (After, 2 * Node) > 0 then
                       Key_At (After, 2 * Node) = Key_At (Before, 2 * Node))
                  and then
                    (if Position_At (After, 2 * Node + 1) > 0 then
                       Key_At (After, 2 * Node + 1)
                         = Key_At (Before, 2 * Node + 1)),
          Post => Node_Valid (After, Node);

   procedure Lemma_Node_Unchanged
     (Before, After : Heap; Node : Index) is null;

   procedure Lemma_Recomputed_Frame
     (Before, After : Heap; Changed : Index)
   is
   begin
      for Node in 1 .. Internal_Last (After) loop
         pragma Loop_Invariant
           (if Changed = 1 then Valid_Range (After, 1, Node - 1)
            else Valid_Except_Through (After, Changed / 2, Node - 1));

         if Node /= Changed / 2 then
            if Node = Changed then
               pragma Assert (Node_Valid (After, Changed));
            else
               pragma Assert (2 * Node /= Changed);
               pragma Assert (2 * Node + 1 /= Changed);
               Lemma_Except_Node (Before, Changed, Node);
               Lemma_Node_Unchanged (Before, After, Node);
            end if;
         end if;
      end loop;
   end Lemma_Recomputed_Frame;

   procedure Refresh_Path (H : in out Heap; Changed : Tree_Index)
     with Pre  => H.Capacity > 0
                  and then Changed <= 2 * H.Capacity - 1
                  and then Valid_Except (H, Changed / 2),
          Post => Is_Heap (H)
                  and H.Last = H.Last'Old
                  and H.Keys = H.Keys'Old;

   procedure Refresh_Path (H : in out Heap; Changed : Tree_Index) is
      Node   : Tree_Index := Changed;
      Before : Heap := H with Ghost;
   begin
      while Node > 1 loop
         declare
            Parent : constant Index := Node / 2;
         begin
            Before := H;
            Recompute (H, Parent);
            Lemma_Recomputed_Frame (Before, H, Parent);
            Node := Parent;
         end;

         pragma Loop_Invariant (Node <= 2 * H.Capacity - 1);
         pragma Loop_Invariant (Valid_Except (H, Node / 2));
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (H.Keys = H.Keys'Loop_Entry);
         pragma Loop_Variant (Decreases => Node);
      end loop;
   end Refresh_Path;

   procedure Lemma_Leaf_Changed
     (Before, After : Heap; Leaf : Tree_Index)
     with Ghost,
          Pre  => Is_Heap (Before)
                  and then Before.Capacity = After.Capacity
                  and then After.Capacity > 0
                  and then Leaf in After.Capacity .. 2 * After.Capacity - 1
                  and then Before.Winners = After.Winners
                  and then Before.Winner_Keys = After.Winner_Keys
                  and then
                    (for all Node in After.Capacity .. 2 * After.Capacity - 1 =>
                       (if Node /= Leaf then
                          Position_At (After, Node) = Position_At (Before, Node)
                          and then
                            (if Position_At (After, Node) > 0 then
                               Key_At (After, Node) = Key_At (Before, Node)))),
          Post => Valid_Except (After, Leaf / 2);

   procedure Lemma_Leaf_Changed
     (Before, After : Heap; Leaf : Tree_Index)
   is
   begin
      for Node in 1 .. Internal_Last (After) loop
         pragma Loop_Invariant
           (Valid_Except_Through (After, Leaf / 2, Node - 1));

         if Node /= Leaf / 2 then
            pragma Assert (2 * Node /= Leaf);
            pragma Assert (2 * Node + 1 /= Leaf);
            Lemma_Heap_Node (Before, Node);
            Lemma_Node_Unchanged (Before, After, Node);
         end if;
      end loop;
   end Lemma_Leaf_Changed;

   procedure Lemma_Higher_Unchanged
     (Before, After : Heap; Changed : Index)
     with Ghost,
          Pre  => Before.Capacity = After.Capacity
                  and then Before.Last = After.Last
                  and then Before.Keys = After.Keys
                  and then Changed < After.Capacity
                  and then Valid_From (Before, Changed + 1)
                  and then
                    (for all I in After.Winners'Range =>
                       (if I /= Changed then
                          After.Winners (I) = Before.Winners (I)
                          and After.Winner_Keys (I) = Before.Winner_Keys (I))),
          Post => Valid_From (After, Changed + 1);

   procedure Lemma_Higher_Unchanged
     (Before, After : Heap; Changed : Index)
   is
   begin
      for Node in reverse Changed + 1 .. Internal_Last (After) loop
         pragma Loop_Invariant
           (Valid_Range (After, Node + 1, Internal_Last (After)));
         Lemma_From_Node (Before, Changed + 1, Node);
         Lemma_Node_Unchanged (Before, After, Node);
         Lemma_Prepend_Range (After, Node);
      end loop;
   end Lemma_Higher_Unchanged;

   procedure Build (H : in out Heap)
     with Post => Is_Heap (H)
                  and H.Last = H.Last'Old
                  and H.Keys = H.Keys'Old;

   procedure Build (H : in out Heap) is
      Before : Heap := H with Ghost;
   begin
      for Node in reverse 1 .. Internal_Last (H) loop
         Before := H;
         Recompute (H, Node);
         Lemma_Higher_Unchanged (Before, H, Node);

         pragma Assert (Node_Valid (H, Node));
         pragma Assert (Valid_From (H, Node + 1));
         Lemma_Prepend_Range (H, Node);

         pragma Loop_Invariant
           (Valid_From (H, Node));
         pragma Loop_Invariant (H.Last = H.Last'Loop_Entry);
         pragma Loop_Invariant (H.Keys = H.Keys'Loop_Entry);
      end loop;
   end Build;

   procedure Lemma_Parent_Beats_Child
     (H : Heap; Parent : Index; Child : Tree_Index)
     with Ghost,
          Pre  => Parent < H.Capacity
                  and then Child in 2 * Parent .. 2 * Parent + 1
                  and then Position_At (H, Child) > 0
                  and then Node_Valid (H, Parent),
          Post => Position_At (H, Parent) > 0
                  and then Key_At (H, Parent) <= Key_At (H, Child);

   procedure Lemma_Parent_Beats_Child
     (H : Heap; Parent : Index; Child : Tree_Index) is null;

   procedure Lemma_Root_Is_Minimum (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Position_At (H, 1) > 0
                  and then Is_Minimum
                    (H, (if H.Capacity = 1
                         then H.Keys (1)
                         else H.Winner_Keys (1)));

   procedure Lemma_Root_Is_Minimum (H : Heap) is
      Node : Tree_Index;
   begin
      for I in 1 .. H.Last loop
         Node := Leaf_Node (H, I);

         while Node > 1 loop
            Lemma_Heap_Node (H, Node / 2);
            Lemma_Parent_Beats_Child (H, Node / 2, Node);
            Node := Node / 2;

            pragma Loop_Invariant (Node <= 2 * H.Capacity - 1);
            pragma Loop_Invariant (Position_At (H, Node) > 0);
            pragma Loop_Invariant (Key_At (H, Node) <= H.Keys (I));
            pragma Loop_Variant (Decreases => Node);
         end loop;

         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if H.Capacity = 1 then H.Keys (1) else H.Winner_Keys (1))
                <= H.Keys (J));
      end loop;
   end Lemma_Root_Is_Minimum;

   procedure Lemma_Root_Represents_Key (H : Heap)
     with Ghost,
          Pre  => not Is_Empty (H) and then Is_Heap (H),
          Post => Root_Position (H) in 1 .. H.Last
                  and then
                    (if H.Capacity = 1
                     then H.Keys (1)
                     else H.Winner_Keys (1))
                      = H.Keys (Root_Position (H));

   procedure Lemma_Root_Represents_Key (H : Heap) is
      Node : Tree_Index := 1;

      procedure Lemma_Winner_Comes_From_Child (Parent : Index)
        with Ghost,
             Pre  => Parent < H.Capacity
                     and then Position_At (H, Parent) > 0
                     and then Node_Valid (H, Parent),
             Post =>
               (Position_At (H, 2 * Parent) = Position_At (H, Parent)
                and then Position_At (H, 2 * Parent) > 0
                and then Key_At (H, 2 * Parent) = Key_At (H, Parent))
               or else
               (Position_At (H, 2 * Parent + 1) = Position_At (H, Parent)
                and then Position_At (H, 2 * Parent + 1) > 0
                and then Key_At (H, 2 * Parent + 1) = Key_At (H, Parent));

      procedure Lemma_Winner_Comes_From_Child (Parent : Index) is null;
   begin
      Lemma_Root_Is_Minimum (H);

      if H.Capacity = 1 then
         return;
      end if;

      while Node < H.Capacity loop
         declare
            Left  : constant Tree_Index := 2 * Node;
            Right : constant Tree_Index := Left + 1;
         begin
            pragma Assert (Position_At (H, Node) > 0);
            Lemma_Heap_Node (H, Node);
            Lemma_Winner_Comes_From_Child (Node);
            if Position_At (H, Left) = Position_At (H, Node)
              and then Position_At (H, Left) > 0
              and then Key_At (H, Left) = Key_At (H, Node)
            then
               Node := Left;
            else
               pragma Assert (Position_At (H, Right) = Position_At (H, Node));
               pragma Assert (Position_At (H, Right) > 0);
               pragma Assert (Key_At (H, Right) = Key_At (H, Node));
               Node := Right;
            end if;
         end;

         pragma Loop_Invariant (Node <= 2 * H.Capacity - 1);
         pragma Loop_Invariant (Position_At (H, Node) = H.Winners (1));
         pragma Loop_Invariant (Position_At (H, Node) > 0);
         pragma Loop_Invariant (Key_At (H, Node) = H.Winner_Keys (1));
         pragma Loop_Variant (Increases => Node);
      end loop;

      pragma Assert (Position_At (H, Node) = Node - H.Capacity + 1);
      pragma Assert (Key_At (H, Node) = H.Keys (Root_Position (H)));
   end Lemma_Root_Represents_Key;

   procedure Clear (H : in out Heap) is
   begin
      H.Last := 0;
      Build (H);
   end Clear;

   function Peek_Min (H : Heap) return Key_Type is
   begin
      Lemma_Root_Is_Minimum (H);
      Lemma_Root_Represents_Key (H);
      return (if H.Capacity = 1 then H.Keys (1) else H.Winner_Keys (1));
   end Peek_Min;

   function Min_Of (H : Heap) return Key_Type is
      Result : Key_Type := H.Keys (1);
   begin
      for I in 2 .. H.Last loop
         if H.Keys (I) < Result then
            Result := H.Keys (I);
         end if;

         pragma Loop_Invariant (for all J in 1 .. I => Result <= H.Keys (J));
         pragma Loop_Invariant
           (for some J in 1 .. I => Result = H.Keys (J));
      end loop;
      return Result;
   end Min_Of;

   procedure Insert (H : in out Heap; K : Key_Type) is
      Before : constant Heap := H with Ghost;
      Keys_0 : constant Key_Array := H.Keys with Ghost;
      Slot   : constant Index := H.Last + 1;
      Leaf   : constant Tree_Index := Leaf_Node (H, Slot);
   begin
      H.Keys (Slot) := K;
      H.Last := Slot;

      Lemma_Leaf_Changed (Before, H, Leaf);
      Refresh_Path (H, Leaf);

      Models.Lemma_Same_Prefix (Keys_0, H.Keys, H.Last - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Keys_0, H.Last - 1),
         Models.Occurrences (H.Keys, H.Last - 1), K);
   end Insert;

   procedure Append (H : in out Heap; K : Key_Type)
     with Pre  => not Is_Full (H),
          Post => H.Last = H.Last'Old + 1
                  and Model (H) = KM.Add (Model (H)'Old, K);

   procedure Append (H : in out Heap; K : Key_Type) is
      Before : constant Key_Array := H.Keys with Ghost;
   begin
      H.Last := H.Last + 1;
      H.Keys (H.Last) := K;
      Models.Lemma_Same_Prefix (Before, H.Keys, H.Last - 1);
      Models.Lemma_Add_Congruent
        (Models.Occurrences (Before, H.Last - 1),
         Models.Occurrences (H.Keys, H.Last - 1), K);
   end Append;

   procedure Meld (Into : in out Heap; From : in out Heap) is
      Base   : constant Extended_Index := Into.Last;
      Extra  : constant Extended_Index := From.Last;
      Cap    : constant Extended_Index := Into.Capacity;
      M0     : constant KM.Multiset := Model (Into) with Ghost;
      F0     : constant KM.Multiset :=
        Models.Occurrences (From.Keys, Extra) with Ghost;
      Prev_Model  : KM.Multiset with Ghost;
      Joined      : KM.Multiset with Ghost;
      Joined_Keys : Key_Array (1 .. Cap) with Ghost;
   begin
      for I in 1 .. Extra loop
         Prev_Model := Model (Into);
         Append (Into, From.Keys (I));

         Models.Lemma_Add_Congruent
           (Prev_Model, M0 + Models.Occurrences (From.Keys, I - 1),
            From.Keys (I));
         Models.Lemma_Sum_Add
           (M0,
            Models.Occurrences (From.Keys, I - 1), From.Keys (I));
         Models.Lemma_Sum_Empty (M0);

         pragma Loop_Invariant (Into.Last = Base + I);
         pragma Loop_Invariant (From.Last = Extra);
         pragma Loop_Invariant
           (Model (Into) = M0 + Models.Occurrences (From.Keys, I));
      end loop;

      if From.Last = 0 then
         Models.Lemma_Sum_Empty (M0);
      end if;

      pragma Assert
        (Model (Into) = M0 + Models.Occurrences (From.Keys, Extra));
      Joined := Model (Into);
      Joined_Keys := Into.Keys;
      Build (Into);
      Models.Lemma_Same_Prefix (Joined_Keys, Into.Keys, Into.Last);
      pragma Assert (Model (Into) = Joined);
      pragma Assert (Models.Occurrences (From.Keys, Extra) = F0);
      Models.Lemma_Sum_Symmetric
        (M0, Models.Occurrences (From.Keys, Extra));
      Models.Lemma_Sum_Congruent
        (Models.Occurrences (From.Keys, Extra), F0, M0);
      Models.Lemma_Sum_Symmetric (F0, M0);
      pragma Assert (Model (Into) = M0 + F0);
      From.Last := 0;
      Build (From);
   end Meld;

   procedure Extract_Min (H : in out Heap; K : out Key_Type) is
      Before : Heap := H with Ghost;
      Keys_0 : constant Key_Array := H.Keys with Ghost;
      Slot   : Index;
      Last   : constant Index := H.Last;
      Moved  : constant Key_Type := H.Keys (Last);
      Leaf   : Tree_Index;
   begin
      Lemma_Root_Is_Minimum (H);
      Lemma_Root_Represents_Key (H);
      Slot := Index (Root_Position (H));
      K := Peek_Min (H);

      H.Keys (Slot) := Moved;
      Leaf := Leaf_Node (H, Slot);
      Lemma_Leaf_Changed (Before, H, Leaf);
      Refresh_Path (H, Leaf);

      Before := H;
      H.Last := H.Last - 1;
      Leaf := Leaf_Node (H, Last);
      Lemma_Leaf_Changed (Before, H, Leaf);
      Refresh_Path (H, Leaf);

      if Slot < Last then
         Models.Lemma_Set (Keys_0, H.Keys, Slot, Last - 1);
         pragma Assert
           (KM.Add (Models.Occurrences (H.Keys, Last - 1), K)
            = KM.Add (Models.Occurrences (Keys_0, Last - 1), Moved));
      else
         Models.Lemma_Same_Prefix (Keys_0, H.Keys, Last - 1);
      end if;
   end Extract_Min;

end Heaps.Tournament;
