pragma SPARK_Mode (On);

with Sha256;

package body Mdoc_Spec is

   --  The signature circuit is the same in both archives.
   Sig_Circuit : constant Bytes_32 :=
     [16#28#, 16#45#, 16#21#, 16#0a#, 16#f0#, 16#57#, 16#40#, 16#e6#,
      16#e3#, 16#e0#, 16#54#, 16#76#, 16#2f#, 16#9e#, 16#35#, 16#ff#,
      16#5f#, 16#c4#, 16#fb#, 16#23#, 16#08#, 16#87#, 16#16#, 16#e3#,
      16#69#, 16#f7#, 16#cf#, 16#73#, 16#eb#, 16#61#, 16#df#, 16#2d#];

   --  Version 7, one attribute: the archive 8d079211...
   V7_Combined : constant Bytes_32 :=
     [16#8d#, 16#07#, 16#92#, 16#11#, 16#71#, 16#52#, 16#00#, 16#ff#,
      16#06#, 16#c5#, 16#10#, 16#96#, 16#39#, 16#24#, 16#55#, 16#02#,
      16#bf#, 16#e9#, 16#4a#, 16#a8#, 16#69#, 16#90#, 16#8d#, 16#31#,
      16#17#, 16#6a#, 16#ae#, 16#40#, 16#16#, 16#18#, 16#21#, 16#21#];
   V7_Hash : constant Bytes_32 :=
     [16#58#, 16#24#, 16#8d#, 16#20#, 16#de#, 16#d3#, 16#b1#, 16#9b#,
      16#09#, 16#96#, 16#e4#, 16#78#, 16#dd#, 16#a6#, 16#af#, 16#ac#,
      16#ba#, 16#79#, 16#4f#, 16#a2#, 16#b1#, 16#f0#, 16#80#, 16#27#,
      16#71#, 16#43#, 16#0b#, 16#c0#, 16#dc#, 16#a7#, 16#d1#, 16#06#];

   --  Version 6, one attribute: the archive 137e5a75...
   V6_Combined : constant Bytes_32 :=
     [16#13#, 16#7e#, 16#5a#, 16#75#, 16#ce#, 16#72#, 16#73#, 16#5a#,
      16#37#, 16#c8#, 16#a7#, 16#2d#, 16#a1#, 16#a8#, 16#a0#, 16#a5#,
      16#df#, 16#8d#, 16#13#, 16#36#, 16#5c#, 16#2a#, 16#e3#, 16#d2#,
      16#c2#, 16#bd#, 16#6a#, 16#0e#, 16#71#, 16#97#, 16#c7#, 16#c6#];
   V6_Hash : constant Bytes_32 :=
     [16#03#, 16#9b#, 16#ed#, 16#19#, 16#b9#, 16#4d#, 16#5d#, 16#73#,
      16#2e#, 16#1d#, 16#e5#, 16#55#, 16#fa#, 16#5c#, 16#5c#, 16#4b#,
      16#9b#, 16#18#, 16#9b#, 16#8c#, 16#79#, 16#08#, 16#d3#, 16#f1#,
      16#ee#, 16#4e#, 16#cb#, 16#9e#, 16#72#, 16#f3#, 16#85#, 16#32#];

   Table : constant array (Spec_Index) of Specification :=
     [1 => (Version        => 7,
            Num_Attributes => 1,
            Combined       => V7_Combined,
            Hash_Id        => V7_Hash,
            Sig_Id         => Sig_Circuit,
            Hash_Cfg       => (Rate_Inv => 7, Num_Queries => 132,
                               Encoded_Len => 4151),
            Sig_Cfg        => (Rate_Inv => 7, Num_Queries => 132,
                               Encoded_Len => 4096)),
      2 => (Version        => 6,
            Num_Attributes => 1,
            Combined       => V6_Combined,
            Hash_Id        => V6_Hash,
            Sig_Id         => Sig_Circuit,
            Hash_Cfg       => (Rate_Inv => 4, Num_Queries => 128,
                               Encoded_Len => 4096),
            Sig_Cfg        => (Rate_Inv => 4, Num_Queries => 128,
                               Encoded_Len => 2945))];

   function Spec (I : Spec_Index) return Specification is (Table (I));

   procedure Lookup
     (Combined : Bytes_32; Found : out Boolean; I : out Spec_Index)
   is
   begin
      Found := False;
      I     := Spec_Index'First;
      for J in Spec_Index loop
         if Table (J).Combined = Combined then
            Found := True;
            I     := J;
            return;
         end if;
      end loop;
   end Lookup;

   procedure Select_Profile
     (Combined         : Bytes_32;
      Hash_Id, Sig_Id  : Bytes_32;
      Nattrs           : Natural;
      I                : out Spec_Index;
      St               : out Mdoc_Status.Status)
   is
      Found : Boolean;
   begin
      Lookup (Combined, Found, I);
      if not Found then
         St := Mdoc_Status.Profile_Unknown;
      elsif Table (I).Hash_Id /= Hash_Id or else Table (I).Sig_Id /= Sig_Id
      then
         St := Mdoc_Status.Profile_Mismatch;
      elsif Table (I).Num_Attributes /= Nattrs then
         St := Mdoc_Status.Attribute_Count;
      else
         St := Mdoc_Status.Ok;
      end if;
   end Select_Profile;

   function Combined_Of (Sig_Id, Hash_Id : Bytes_32) return Bytes_32 is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Sha256.Update (Ctx, Sig_Id);
      Sha256.Update (Ctx, Hash_Id);
      return Sha256.Digest (Ctx);
   end Combined_Of;

end Mdoc_Spec;
