--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  The multiset of keys used as the mathematical model of every heap.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Multisets;

package Heaps.Key_Multisets is new
  SPARK.Containers.Functional.Multisets (Key_Type, "=");
