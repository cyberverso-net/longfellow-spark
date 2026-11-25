pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Gadgets;    use Gadgets;

package body Block_Checks is

   use type Sha256.State;
   use type Netlist.Values;

   procedure Traced
     (H : Sha256.State; Block : Bytes_64;
      T : out Sha256.Trace.Block_Trace; H1 : out Sha256.State) is
   begin
      H1 := H;
      Sha256.Trace.Compress_Traced (H1, Block, 0, T);
   end Traced;

   procedure Honest
     (H     : Sha256.State;
      Block : Bytes_64;
      T     : Sha256.Trace.Block_Trace;
      H1    : Sha256.State;
      M     : out Gadget.Message_Bits;
      H0    : out Gadget.State_Bits;
      X     : out Gadget.Block_Witness) is
   begin
      for I in 0 .. 15 loop
         M (I) := Bits_Of (Netlist.Message_Word (Block, I));
      end loop;
      for J in Sha256.Word_Index loop
         H0 (J) := Bits_Of (H (J));
         X.H1 (J) := Bits_Of (H1 (J));
      end loop;
      for I in Netlist.Schedule_Step loop
         X.W (I) := Bits_Of (T.W (I - 16));
      end loop;
      for R in Netlist.Round loop
         X.E (R) := Bits_Of (T.E (R));
         X.A (R) := Bits_Of (T.A (R));
      end loop;
   end Honest;

   function Check_Netlist (H : Sha256.State; Block : Bytes_64) return Boolean
   is
      T  : Sha256.Trace.Block_Trace;
      H1 : Sha256.State;
      V  : Netlist.Values;
   begin
      Traced (H, Block, T, H1);
      V := Netlist.Interpret (H, Block);
      if Netlist.Output (V) /= H1 or else not Netlist.Holds (V, H, Block) then
         return False;
      end if;
      for I in Netlist.Schedule_Step loop
         if V (Netlist.W_Ix (I)) /= T.W (I - 16) then
            return False;
         end if;
      end loop;
      for R in Netlist.Round loop
         if V (Netlist.E_Ix (R)) /= T.E (R)
           or else V (Netlist.A_Ix (R)) /= T.A (R)
         then
            return False;
         end if;
      end loop;
      return True;
   end Check_Netlist;

   function Check_Gadget (H : Sha256.State; Block : Bytes_64) return Boolean
   is
      T  : Sha256.Trace.Block_Trace;
      H1 : Sha256.State;
      M  : Gadget.Message_Bits;
      H0 : Gadget.State_Bits;
      X  : Gadget.Block_Witness;
   begin
      Traced (H, Block, T, H1);
      Honest (H, Block, T, H1, M, H0, X);
      return Gadget.Witness_Bits (X)
        and then Gadget.Assertions_Hold (M, H0, X)
        and then Gadget.Decoded (M, H0, X) = Netlist.Interpret (H, Block);
   end Check_Gadget;

end Block_Checks;
