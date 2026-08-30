--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  An instance of the pairing arena.
--
--  A library-level instantiation is where the generic's verification
--  conditions are generated: GNATprove analyses instances, not the generic
--  itself, and an instantiation defaults to SPARK_Mode off, so without the
--  pragma below the body would be silently unverified rather than proved.
--
--  Unevaluated_Use_Of_Old and Assertion_Policy both have to be repeated here.
--  Neither is inherited from the generic's own source: the pragmas in effect
--  for an instance are the ones at the point of instantiation. The first is
--  needed because the frame clauses of the arena put Snap'Old inside an
--  implication. The second because the policy would otherwise come from
--  whichever client pulls this unit in, so a client compiled with assertions
--  enabled would try to evaluate the multiset model at run time -- which the
--  generic's own header says must not happen, and which clashes outright with
--  the multiset instance in Heaps.Key_Multisets, compiled with ghost code
--  ignored.

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Pairing;

package Heaps.Pairing_Pool is new Heaps.Pairing (Capacity => 2 ** 20);
