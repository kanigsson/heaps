--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The ghost model, a multiset built by recursion over the key array, cannot
--  reasonably be evaluated at run time, and the contracts are discharged by
--  proof, so assertions are disabled here.

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

package body Heaps.Models with SPARK_Mode is

   use KM;

   ---------------------------
   -- Lemma_Add_Congruent --
   ---------------------------

   procedure Lemma_Add_Congruent (X, Y : Model; E : Key_Type) is null;

   --------------------------
   -- Lemma_Add_Commutes --
   --------------------------

   procedure Lemma_Add_Commutes (M : Model; E, F : Key_Type) is null;

   -------------------------
   -- Lemma_Add_Cancels --
   -------------------------

   procedure Lemma_Add_Cancels (X, Y : Model; E : Key_Type) is null;

   ----------------------
   -- Lemma_Sum_Empty --
   ----------------------

   procedure Lemma_Sum_Empty (X : Model) is null;

   --------------------------
   -- Lemma_Sum_Congruent --
   --------------------------

   procedure Lemma_Sum_Congruent (X, Y, Z : Model) is null;

   ----------------------
   -- Lemma_Sum_Assoc --
   ----------------------

   procedure Lemma_Sum_Assoc (X, Y, Z : Model) is null;

   --------------------
   -- Lemma_Sum_Add --
   --------------------

   procedure Lemma_Sum_Add (X, Y : Model; E : Key_Type) is null;

   -------------------------
   -- Lemma_Sum_Add_Left --
   -------------------------

   procedure Lemma_Sum_Add_Left (X, Y : Model; E : Key_Type) is null;

   ---------------------------
   -- Lemma_Sum_Empty_Left --
   ---------------------------

   procedure Lemma_Sum_Empty_Left (X : Model) is null;

   ------------------------------
   -- Lemma_Sum_Symmetric     --
   ------------------------------

   procedure Lemma_Sum_Symmetric (X, Y : Model) is null;

   ------------------------
   -- Lemma_Same_Prefix --
   ------------------------

   procedure Lemma_Same_Prefix (A, B : Key_Array; Lst : Extended_Index) is
   begin
      if Lst = 0 then
         return;
      end if;

      Lemma_Same_Prefix (A, B, Lst - 1);
      Lemma_Add_Congruent
        (Occurrences (A, Lst - 1), Occurrences (B, Lst - 1), A (Lst));
   end Lemma_Same_Prefix;

   ---------------
   -- Lemma_Set --
   ---------------

   procedure Lemma_Set (A, R : Key_Array; I : Index; Lst : Extended_Index) is
   begin
      if Lst = I then

         --  The two arrays agree below Lst, so the goal reduces to swapping
         --  the order of two Add on a common model.

         Lemma_Same_Prefix (A, R, Lst - 1);
         Lemma_Add_Congruent
           (Occurrences (R, Lst - 1), Occurrences (A, Lst - 1), R (Lst));
         Lemma_Add_Congruent
           (Add (Occurrences (R, Lst - 1), R (Lst)),
            Add (Occurrences (A, Lst - 1), R (Lst)),
            A (I));
         Lemma_Add_Commutes (Occurrences (A, Lst - 1), R (I), A (I));

      else

         --  Slot Lst is the same in both arrays; peel it off and recurse.

         Lemma_Set (A, R, I, Lst - 1);
         Lemma_Add_Congruent
           (Add (Occurrences (R, Lst - 1), A (I)),
            Add (Occurrences (A, Lst - 1), R (I)),
            A (Lst));
         Lemma_Add_Commutes (Occurrences (R, Lst - 1), A (I), A (Lst));
         Lemma_Add_Commutes (Occurrences (A, Lst - 1), R (I), A (Lst));
      end if;
   end Lemma_Set;

   ------------------------------
   -- Lemma_Range_Is_Prefix   --
   ------------------------------

   procedure Lemma_Range_Is_Prefix (A : Key_Array; Lst : Extended_Index) is
   begin
      if Lst = 0 then
         return;
      end if;

      Lemma_Range_Is_Prefix (A, Lst - 1);
      Lemma_Add_Congruent
        (Occurrences_In (A, 1, Lst - 1), Occurrences (A, Lst - 1), A (Lst));
   end Lemma_Range_Is_Prefix;

   -----------------------
   -- Lemma_Range_Same --
   -----------------------

   procedure Lemma_Range_Same
     (A, B : Key_Array; Fst : Positive; Lst : Extended_Index) is
   begin
      if Lst < Fst then
         return;
      end if;

      Lemma_Range_Same (A, B, Fst, Lst - 1);
      Lemma_Add_Congruent
        (Occurrences_In (A, Fst, Lst - 1),
         Occurrences_In (B, Fst, Lst - 1),
         A (Lst));
   end Lemma_Range_Same;

   -----------------------
   -- Lemma_Range_Peel --
   -----------------------

   procedure Lemma_Range_Peel
     (A : Key_Array; Fst : Positive; Lst : Extended_Index) is
   begin
      if Fst = Lst then
         return;
      end if;

      --  Both sides peel slot Lst off the top; below it the statement is the
      --  same one about a shorter range, and the two Add then commute.

      Lemma_Range_Peel (A, Fst, Lst - 1);
      Lemma_Add_Congruent
        (Occurrences_In (A, Fst, Lst - 1),
         Add (Occurrences_In (A, Fst + 1, Lst - 1), A (Fst)),
         A (Lst));
      Lemma_Add_Commutes
        (Occurrences_In (A, Fst + 1, Lst - 1), A (Fst), A (Lst));
   end Lemma_Range_Peel;

   -------------------------
   -- Lemma_Range_Split  --
   -------------------------

   procedure Lemma_Range_Split
     (A : Key_Array; Mid : Extended_Index; Lst : Extended_Index) is
   begin
      if Mid = Lst then
         Lemma_Sum_Empty (Occurrences (A, Mid));
         return;
      end if;

      --  Slot Lst belongs to the upper range on both sides; peel it off and
      --  carry the Add out through the sum.

      Lemma_Range_Split (A, Mid, Lst - 1);
      Lemma_Add_Congruent
        (Occurrences (A, Lst - 1),
         Sum (Occurrences (A, Mid), Occurrences_In (A, Mid + 1, Lst - 1)),
         A (Lst));
      Lemma_Sum_Add
        (Occurrences (A, Mid), Occurrences_In (A, Mid + 1, Lst - 1), A (Lst));
   end Lemma_Range_Split;

   ----------------
   -- Lemma_Swap --
   ----------------

   procedure Lemma_Swap
     (A, R : Key_Array; I, J : Index; Lst : Extended_Index) is
   begin
      if Lst = J then

         --  Below J the two arrays differ in the single slot I, so the prefix
         --  models differ by one exchanged key; adding back the two swapped
         --  keys -- R (J) = A (I) on one side, A (J) = R (I) on the other --
         --  makes the two sides equal.

         Lemma_Set (A, R, I, Lst - 1);

      else

         --  Slot Lst is untouched by the swap; peel it off and recurse.

         Lemma_Swap (A, R, I, J, Lst - 1);
         Lemma_Add_Congruent
           (Occurrences (R, Lst - 1), Occurrences (A, Lst - 1), A (Lst));
      end if;
   end Lemma_Swap;

end Heaps.Models;
