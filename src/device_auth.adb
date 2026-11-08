pragma SPARK_Mode (On);

with Sha256;
with Cbor_Encode; use Cbor_Encode;

package body Device_Auth is

   --  84 6A "Signature1" 43 A1 01 26 40.
   Sig1_Head : constant Byte_Array (0 .. 16) :=
     [16#84#, 16#6A#,
      Character'Pos ('S'), Character'Pos ('i'), Character'Pos ('g'),
      Character'Pos ('n'), Character'Pos ('a'), Character'Pos ('t'),
      Character'Pos ('u'), Character'Pos ('r'), Character'Pos ('e'),
      Character'Pos ('1'),
      16#43#, 16#A1#, 16#01#, 16#26#, 16#40#];

   --  84 74 "DeviceAuthentication".
   Auth_Head : constant Byte_Array (0 .. 21) :=
     [16#84#, 16#74#,
      Character'Pos ('D'), Character'Pos ('e'), Character'Pos ('v'),
      Character'Pos ('i'), Character'Pos ('c'), Character'Pos ('e'),
      Character'Pos ('A'), Character'Pos ('u'), Character'Pos ('t'),
      Character'Pos ('h'), Character'Pos ('e'), Character'Pos ('n'),
      Character'Pos ('t'), Character'Pos ('i'), Character'Pos ('c'),
      Character'Pos ('a'), Character'Pos ('t'), Character'Pos ('i'),
      Character'Pos ('o'), Character'Pos ('n')];

   Tag_24      : constant Byte_Array (0 .. 1) := [16#D8#, 16#18#];
   Name_Spaces : constant Byte_Array (0 .. 3) :=
     [16#D8#, 16#18#, 16#41#, 16#A0#];

   function Digest (Session, Doc_Type : Byte_Array) return Bytes_32 is
      --  The DeviceAuthentication array, then the payload around it.
      Auth_Len : constant Natural :=
        Auth_Head'Length + Session'Length
        + Head_Len (Doc_Type'Length) + Doc_Type'Length + Name_Spaces'Length;
      Payload_Len : constant Natural :=
        Tag_24'Length + Head_Len (Auth_Len) + Auth_Len;
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Sha256.Update (Ctx, Sig1_Head);
      Sha256.Update (Ctx, Head (Bytes_Major, Payload_Len));
      Sha256.Update (Ctx, Tag_24);
      Sha256.Update (Ctx, Head (Bytes_Major, Auth_Len));
      Sha256.Update (Ctx, Auth_Head);
      Sha256.Update (Ctx, Session);
      Sha256.Update (Ctx, Head (Text_Major, Doc_Type'Length));
      Sha256.Update (Ctx, Doc_Type);
      Sha256.Update (Ctx, Name_Spaces);
      return Sha256.Digest (Ctx);
   end Digest;

end Device_Auth;
