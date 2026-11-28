--  Circuit_Certificates: the certificate of the circuit checker as data
--  (ADR 0093, ADR 0094), and its reader from bytes.
--
--  For each layer, in the order of the walk (from the last layer, which
--  reads the inputs, to layer 0), the certificate gives each wire's
--  number of slots. It carries no slot of any pair: the walk finds each
--  pair's slot among its wire's slots (ADR 0094). It carries no
--  coefficient, no meaning, no kind and no fact either: the checker
--  computes them from the circuit, and a wrong count makes it refuse.
--  The gadget instances are added by the catalogue's block, in a section
--  of their own.
--
--  The bytes, all integers ULEB128 as in the circuit file (Uleb128):
--
--    "LFCK"  magic
--    2       version
--    32      the identifier of the circuit the certificate is for
--    NL      the number of layers
--    then, for each layer from the last to 0:
--      NW      its wires (the layer's outputs)
--      NW times: the wire's slot count
--
--  and nothing after. Read refuses a file that does not follow it, or
--  whose counts exceed the bounds below, with a status of its own.
--
--  Documentation: docs/guide/10-certified-circuits.md, Section 3.
--  Decisions: ADR 0091 (the certificate), ADR 0093 (the model), ADR 0094
--  (no hints).
--
--  Proof status: Silver (absence of run-time errors on any bytes, and
--  the Post of Read). Nothing here relates the certificate to a circuit:
--  the walk checks it against one.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, circuits and
--  their certificates are public data (ADR 0037; register row S4).

pragma SPARK_Mode (On);

with Bytes;      use Bytes;

package Circuit_Certificates is

   --  Capacities of the reader, above every circuit the checker accepts:
   --  the layers of Sumcheck_Algebra, and room for the one-attribute pair
   --  (3,366,957 wires on the hash circuit).
   Max_Layers    : constant := 64;
   Max_All_Wires : constant := 2 ** 23;
   Max_Count     : constant := 2 ** 16 - 1;

   --  The length of a linear meaning, besides the constant, that the
   --  checker's instances may take (ADR 0093: 3 for GF(2^128), 2 for
   --  P-256); a meaning then has at most four entries.
   subtype Form_Bound is Positive range 1 .. 3;

   --  The capacities an instance may take for its declared variables and
   --  for the slots of one layer: room above the measured values (ADR
   --  0093), small enough that sums of them with wire counts do not
   --  overflow.
   subtype Capacity is Positive range 1 .. 2 ** 26;

   subtype Layer_Count is Natural range 0 .. Max_Layers;
   subtype Slot_Count is Natural range 0 .. Max_Count;

   --  The part of the flat arrays that is one layer's.
   type Layer_Span is record
      First_Wire : Natural;
      Wires      : Natural;
   end record;
   type Span_Array is array (Natural range <>) of Layer_Span;

   type Count_Array is array (Natural range <>) of Slot_Count;

   --  Layers (I) is the I-th layer of the walk: the circuit's layer
   --  NL - I. The spans tile the array of counts in that order;
   --  First_Wire is an offset: wire J of the layer (from 0) is
   --  Counts (First_Wire + J + 1).
   type Certificate (NL : Layer_Count; NW : Natural) is record
      Circuit_Id : Bytes_32;
      Layers     : Span_Array (1 .. NL);
      Counts     : Count_Array (1 .. NW);
   end record;

   --  The spans tile the array, layer after layer, from the first entry
   --  to the last: no entry outside a span.
   function Spans_Ok (K : Certificate) return Boolean is
     (K.NW <= Max_All_Wires
      and then (K.NL = 0 or else K.Layers (1).First_Wire = 0)
      and then (for all I in 1 .. K.NL =>
                  K.Layers (I).Wires <= K.NW
                  and then K.Layers (I).First_Wire
                             <= K.NW - K.Layers (I).Wires)
      and then (for all I in 2 .. K.NL =>
                  K.Layers (I).First_Wire
                    = K.Layers (I - 1).First_Wire + K.Layers (I - 1).Wires)
      and then (if K.NL = 0 then K.NW = 0
                else K.Layers (K.NL).First_Wire + K.Layers (K.NL).Wires
                     = K.NW))
   with Global => null;

   type Cert_Access is access Certificate;

   type Status is
     (Ok,
      Bad_Magic,       --  not "LFCK"
      Bad_Version,     --  a version other than 2
      Truncated,       --  the bytes end inside the certificate
      Bad_Integer,     --  an integer of more than four bytes
      Bound_Exceeded,  --  a count beyond the capacities above
      Trailing);       --  bytes after the certificate

   procedure Read
     (B  : Byte_Array;
      K  : out Cert_Access;
      St : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   => (St = Ok) = (K /= null)
               and then (if St = Ok then Spans_Ok (K.all));

   procedure Free (K : in out Cert_Access) with
     Global => null,
     Post   => K = null;

end Circuit_Certificates;
