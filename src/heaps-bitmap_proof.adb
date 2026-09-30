--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Instantiate with a symbolic universe so the generic body is checked for
--  every supported universe, including 1 and 2 ** 24.

pragma Unevaluated_Use_Of_Old (Allow);
pragma Assertion_Policy (Ghost => Ignore, Pre => Ignore, Post => Ignore,
                         Assert => Ignore, Loop_Invariant => Ignore,
                         Loop_Variant => Ignore);

with Heaps.Bitmap;

procedure Heaps.Bitmap_Proof (Universe : Index) with SPARK_Mode, Ghost is
   package Queue is new Heaps.Bitmap (Universe);
   pragma Unreferenced (Queue);
begin
   --  Instantiation alone makes GNATprove check every body in Queue.
   null;
end Heaps.Bitmap_Proof;
