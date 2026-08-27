--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  Root of a collection of SPARK examples of heap (priority queue) data
--  structures, all of them represented inside arrays: either implicitly
--  (the position in the array encodes the tree structure) or explicitly
--  (a pool array of nodes linked by indices instead of pointers).
--
--  See the top-level README.md for the catalogue of heap kinds and for the
--  verification level reached by each of them.

package Heaps with SPARK_Mode, Pure is

   --  All the heaps in this collection are keyed by this type. Giving it a
   --  default value makes every array of keys default-initialized, which
   --  removes any question of reading an uninitialized slot in the unused
   --  part of a heap array.

   type Key_Type is new Integer with Default_Value => 0;

   --  Capacities are bounded so that computing the index of a child, which
   --  multiplies an index by the arity of the tree, never overflows.

   Max_Capacity : constant := 2 ** 24;

   subtype Extended_Index is Natural range 0 .. Max_Capacity;
   subtype Index is Extended_Index range 1 .. Max_Capacity;

   type Key_Array is array (Index range <>) of Key_Type;
   --  Every heap in the collection stores its keys in such an array, indexed
   --  from 1. Sharing the type lets all of them share the multiset model in
   --  Heaps.Models.

end Heaps;
