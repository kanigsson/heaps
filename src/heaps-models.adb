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
