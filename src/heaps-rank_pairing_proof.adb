--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Instantiate with a symbolic capacity so the generic body is checked for
--  every supported capacity, including 1 and Max_Capacity.

pragma Unevaluated_Use_Of_Old (Allow);
pragma Assertion_Policy (Ghost => Ignore, Pre => Ignore, Post => Ignore,
                         Assert => Ignore, Loop_Invariant => Ignore,
                         Loop_Variant => Ignore);

with Heaps.Rank_Pairing;

procedure Heaps.Rank_Pairing_Proof (Capacity : Index) with SPARK_Mode, Ghost is
   package Arena is new Heaps.Rank_Pairing (Capacity);
   pragma Unreferenced (Arena);
begin
   --  Instantiation alone makes GNATprove check every body in Arena.
   null;
end Heaps.Rank_Pairing_Proof;
