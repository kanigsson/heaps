--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The 4-ary instance of the benchmark adapter. Instantiating at library
--  level rather than inside the driver keeps the (large) heap array out of
--  the stack.

with Bench.Dary_Heap;

package Bench.Dary_4 is new Bench.Dary_Heap (4, "4-ary");
