--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Skew_Binomial;

package Heaps.Skew_Binomial_Pool is new Heaps.Skew_Binomial
  (Capacity => 2 ** 15);
--  Instance the test suite drives
