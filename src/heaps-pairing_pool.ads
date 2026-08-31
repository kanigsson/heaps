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
--  Unevaluated_Use_Of_Old and Assertion_Policy have to be repeated here: the
--  pragmas in effect for an instance are the ones at the point of
--  instantiation, not those of the generic's own source. Without the second,
--  the policy would come from whichever client pulls this unit in, and a
--  client compiled with assertions enabled would try to evaluate the multiset
--  model at run time.

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Pairing;

package Heaps.Pairing_Pool is new Heaps.Pairing (Capacity => 2 ** 20);
