--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

with Ada.Text_IO;             use Ada.Text_IO;
with Ada.Integer_Text_IO;     use Ada.Integer_Text_IO;
with Interfaces;              use Interfaces;

package body Bench is

   ------------
   -- Seeded --
   ------------

   function Seeded (Seed : Long_Long_Integer := 88_172_645_463_325_252)
                     return Generator is
   begin
      return (State => Interfaces.Unsigned_64'Mod (Seed));
   end Seeded;

   ----------
   -- Next --
   ----------

   procedure Next (G : in out Generator; K : out Key_Type) is
      --  xorshift64: cheap enough that the generator does not dominate the
      --  measurement, and reproducible across platforms.
      X : Unsigned_64 := G.State;
   begin
      X := X xor Shift_Left (X, 13);
      X := X xor Shift_Right (X, 7);
      X := X xor Shift_Left (X, 17);
      G.State := X;
      K := Key_Type (X mod 2 ** 30);
   end Next;

   ------------------
   -- Print_Header --
   ------------------

   procedure Print_Header is
   begin
      Put_Line
        ("heap                 scenario           "
         & "n        ns/op        checksum");
      Put_Line (String'(1 .. 74 => '-'));
   end Print_Header;

   ---------------
   -- Print_Row --
   ---------------

   procedure Print_Row
     (Heap_Name : String;
      Scenario  : String;
      N         : Positive;
      Seconds   : Duration;
      Ops       : Long_Long_Integer;
      Checksum  : Checksum_Type)
   is
      Ns_Per_Op : constant Float :=
        (if Ops = 0 then 0.0
         else Float (Seconds) * 1.0E9 / Float (Ops));

      procedure Pad (S : String; Width : Positive);
      procedure Pad (S : String; Width : Positive) is
      begin
         Put (S);
         if S'Length < Width then
            Put (String'(1 .. Width - S'Length => ' '));
         end if;
      end Pad;

      Rounded : constant Integer := Integer (Ns_Per_Op * 100.0);
      Frac    : constant String  := Integer'Image (100 + Rounded mod 100);
      --  " 1dd": take the last two characters to get a zero-padded fraction
   begin
      Pad (Heap_Name, 21);
      Pad (Scenario, 15);
      Put (N, Width => 10);
      Put ("  ");
      Put (Rounded / 100, Width => 6);
      Put ('.');
      Put (Frac (Frac'Last - 1 .. Frac'Last));
      Put ("  ");
      Put (Checksum_Type'Image (Checksum));
      New_Line;
   end Print_Row;

end Bench;
