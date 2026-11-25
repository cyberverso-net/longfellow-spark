pragma SPARK_Mode (Off);

--  Block_Checks: the checks of one block of SHA-256's compression shared
--  by gadgets_kat (the NIST vectors, random blocks) and relation_cases
--  (every block of the test documents).
--
--    Check_Netlist : Sha256.Trace.Netlist.Interpret against the traced
--                    compression of the library: the state after the
--                    block, and the schedule words, the e and the a of
--                    the trace at their named values; Holds on the
--                    result.
--    Check_Gadget  : the assertions of Sha256.Trace.Netlist.Gadget on
--                    the honest trace of the block all hold, and the
--                    decoded values are Interpret's.

with Bytes;  use Bytes;
with Sha256;
with Sha256.Trace;
with Sha256.Trace.Netlist.Gadget;

package Block_Checks is

   package Netlist renames Sha256.Trace.Netlist;
   package Gadget renames Sha256.Trace.Netlist.Gadget;

   --  The gadget's inputs and witness from the state before the block,
   --  the block, its trace and the state after it.
   procedure Honest
     (H     : Sha256.State;
      Block : Bytes_64;
      T     : Sha256.Trace.Block_Trace;
      H1    : Sha256.State;
      M     : out Gadget.Message_Bits;
      H0    : out Gadget.State_Bits;
      X     : out Gadget.Block_Witness);

   function Check_Netlist (H : Sha256.State; Block : Bytes_64) return Boolean;

   function Check_Gadget (H : Sha256.State; Block : Bytes_64) return Boolean;

end Block_Checks;
