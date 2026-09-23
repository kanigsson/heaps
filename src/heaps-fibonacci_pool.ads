--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore,
                         Loop_Variant   => Ignore);

with Heaps.Fibonacci;

package Heaps.Fibonacci_Pool is new Heaps.Fibonacci
  (Capacity => 2 ** 15);
--  Instance the test suite drives
