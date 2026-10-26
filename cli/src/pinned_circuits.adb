pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Sha256;

package body Pinned_Circuits is

   subtype Hex_64 is String (1 .. 64);
   type Path_Access is access constant String;

   type Pin is record
      Path   : Path_Access;
      Binary : Boolean;
      Digest : Hex_64;
      Id     : Hex_64;
   end record;

   Mdoc : constant String := "tests/vectors/upstream/mdoc/";

   --  The mDoc circuits of the two v7 archives at d5e6be7. Both archives
   --  carry the same signature circuit, so it has one entry.
   Pins : constant array (Entry_Index) of Pin :=
     [1 => (new String'(Mdoc & "8d079211715200ff06c5109639245502"
                        & "bfe94aa869908d31176aae4016182121_hash.lfc2"),
            True,
            "13a6d1569240dc4e9acc0f47373bf35b"
            & "f19f45b85d282f9c04c70cec471cb58e",
            "58248d20ded3b19b0996e478dda6afac"
            & "ba794fa2b1f0802771430bc0dca7d106"),
      2 => (new String'(Mdoc & "137e5a75ce72735a37c8a72da1a8a0a5"
                        & "df8d13365c2ae3d2c2bd6a0e7197c7c6_hash.lfc2"),
            True,
            "11b567699cfda1d6b6d0aa251f0d2659"
            & "d96fd3dfc4eeb255532648901aae15e3",
            "039bed19b94d5d732e1de555fa5c5c4b"
            & "9b189b8c7908d3f1ee4ecb9e72f38532"),
      3 => (new String'(Mdoc & "8d079211715200ff06c5109639245502"
                        & "bfe94aa869908d31176aae4016182121_sig.lfc2"),
            False,
            "21d2ab3a62bdbe015dfe163290bd4063"
            & "1f15351d5145a9b2b053359d9fe6e1e4",
            "2845210af05740e6e3e054762f9e35ff"
            & "5fc4fb23088716e369f7cf73eb61df2d")];

   function From_Hex (S : Hex_64) return Bytes_32 is
      function Digit (Ch : Character) return Unsigned_8 is
        (case Ch is
            when '0' .. '9' => Character'Pos (Ch) - Character'Pos ('0'),
            when 'a' .. 'f' => Character'Pos (Ch) - Character'Pos ('a') + 10,
            when others     => raise Program_Error);
      R : Bytes_32;
   begin
      for I in R'Range loop
         R (I) := 16 * Digit (S (S'First + 2 * I))
                  + Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end From_Hex;

   function Path (E : Entry_Index) return String is (Pins (E).Path.all);

   function Binary (E : Entry_Index) return Boolean is (Pins (E).Binary);

   function File_Digest (E : Entry_Index) return Bytes_32 is
     (From_Hex (Pins (E).Digest));

   function Id (E : Entry_Index) return Bytes_32 is (From_Hex (Pins (E).Id));

   procedure Lookup (B : Byte_Array; Found : out Boolean; Id : out Bytes_32)
   is
      Ctx : Sha256.Context := Sha256.Initial;
      D   : Bytes_32;
   begin
      Sha256.Update (Ctx, B);
      D := Sha256.Digest (Ctx);
      for E in Entry_Index loop
         if File_Digest (E) = D then
            Found := True;
            Id := Pinned_Circuits.Id (E);
            return;
         end if;
      end loop;
      Found := False;
      Id := [others => 0];
   end Lookup;

   procedure Read
     (B    : Byte_Array;
      Full : Boolean;
      C    : out CR.Circuit_Access;
      H    : out CR.Header;
      St   : out Circuit_Status.Status)
   is
      Found : Boolean := False;
      Pid   : Bytes_32 := [others => 0];
   begin
      if not Full then
         Lookup (B, Found, Pid);
      end if;
      if Found then
         CR.Read_Pinned (B, Pid, C, H, St);
      else
         CR.Read (B, C, H, St);
      end if;
   end Read;

end Pinned_Circuits;
