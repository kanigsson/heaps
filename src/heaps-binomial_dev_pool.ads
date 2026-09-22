--  Small proof instance used while developing the binomial arena.

pragma SPARK_Mode (On);
pragma Unevaluated_Use_Of_Old (Allow);

pragma Assertion_Policy (Ghost          => Ignore,
                         Pre            => Ignore,
                         Post           => Ignore,
                         Assert         => Ignore,
                         Loop_Invariant => Ignore);

with Heaps.Binomial;

package Heaps.Binomial_Dev_Pool is new Heaps.Binomial
  (Capacity => 64);
