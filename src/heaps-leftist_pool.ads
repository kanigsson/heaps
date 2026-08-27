--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  An instance of the arena.
--
--  A library-level instantiation is where the generic's verification
--  conditions are generated: GNATprove analyses instances, not the generic
--  itself, and an instantiation defaults to SPARK_Mode off, so without the
--  pragma below the body would be silently unverified rather than proved.
--
--  Unevaluated_Use_Of_Old has to be repeated here. It is not inherited from
--  the generic's own source, and the frame clauses of the arena put Snap'Old
--  inside an implication.

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

with Heaps.Leftist_Arena;

package Heaps.Leftist_Pool is new Heaps.Leftist_Arena (Capacity => 2 ** 20);
