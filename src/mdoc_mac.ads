--  Mdoc_Mac: the tags that bind the two circuits of an mDoc proof, in
--  the legacy form of circuit versions 5 to 7 (longfellow-zk/
--  longfellow-zk d5e6be7, rust/applications/mdoc_zk/runtime/src/mac.rs,
--  push_legacy_macs; Phase D, block 5, ADR 0058).
--
--  Why there are tags at all. The hash circuit, over GF(2^128), proves
--  facts about the credential's bytes: the digest the issuer signed,
--  and the device key the credential carries. The signature circuit,
--  over P-256, verifies the two ECDSA signatures on those values. The
--  two proofs would say nothing about each other unless the values are
--  the same on both sides, and they are secret, so they cannot be
--  public inputs. Instead each circuit checks, on its own copy of the
--  value, a message authentication code of it under a one-time key the
--  prover keeps secret (mac_ap, drawn at random for each proof) and a
--  public challenge av drawn from the transcript after both
--  commitments: tag = (av + ap) * m in GF(2^128), where m is one half
--  of the 256-bit value. The six tags are public inputs of both
--  circuits, so a verifier that accepts both proofs knows that both
--  circuits spoke of the same value, and learns nothing of it when it
--  is not zero: the tag is the product of the secret message by a
--  secret, uniform element, uniform itself. The limit, upstream's as
--  well: a zero half gives a zero tag whatever the pad, so a tag tells
--  a zero half from a non-zero one; the halves are a SHA-256 digest and
--  the coordinates of a point on P-256, never zero in practice, and
--  neither this unit nor upstream checks for it.
--
--  The three values, in order: the digest of the MSO that the issuer
--  signed (issuer_sig_digest), the x and the y coordinate of the device
--  key (device_pk). Each is a 256-bit integer written as 32 little-
--  endian bytes (nat_to_32bytes); m0 is the field element of bytes 0
--  to 15 and m1 that of bytes 16 to 31, with the little-endian
--  convention of GF2_128.From_Bytes. tag (2 i) = (av + ap (i, 0)) * m0,
--  tag (2 i + 1) = (av + ap (i, 1)) * m1; av and the pads are elements
--  by their 128-bit value. The verifier recomputes nothing here: it
--  reads the six tags from the proof and puts them in the public
--  inputs; the circuits check the equation.
--
--  Documentation: docs/guide/09-mdoc.md. The modern form of version 8
--  (circuits_mac::concrete::compute_tag) is not in the project: no
--  version 8 archive is among upstream's artifacts at d5e6be7 (ADR
--  0055).
--
--  Proof status. Gold: Legacy_Tags returns the six products of the
--  equation above, stated with the field's Mul and Add and the halves
--  of each message. Silver on everything.
--
--  Constant-time discipline (ADR 0006): APPLIES. The messages and the
--  pads are secret (they are in the witness); av and the tags are
--  public. The six products and the six additions are the field's
--  constant-time operations; the byte conversions index on constants.

pragma SPARK_Mode (On);

with Bytes;   use Bytes;
with GF2_128; use GF2_128;

package Mdoc_Mac is

   --  mac_ap: three pairs of one-time pads, one pair per message.
   subtype Message_Index is Natural range 0 .. 2;
   subtype Half_Index is Natural range 0 .. 1;

   type Pad_Pair is array (Half_Index) of Element;
   type Pads is array (Message_Index) of Pad_Pair;

   --  The three 256-bit values as 32 little-endian bytes each.
   type Messages is array (Message_Index) of Bytes_32;

   subtype Tag_Index is Natural range 0 .. 5;
   type Tags is array (Tag_Index) of Element;

   --  The field element of half H of a message: bytes 0 to 15 for
   --  H = 0, 16 to 31 for H = 1.
   function Half (M : Bytes_32; H : Half_Index) return Element is
     (Element'(Limbs => Limbs_Of_Bytes (M (16 * H .. 16 * H + 15))))
   with Global => null;

   function Legacy_Tags (Av : Element; Ap : Pads; M : Messages) return Tags
   with
     Global => null,
     Post   =>
       (for all I in Message_Index =>
          Legacy_Tags'Result (2 * I)
            = Mul (Add (Av, Ap (I) (0)), Half (M (I), 0))
          and then Legacy_Tags'Result (2 * I + 1)
            = Mul (Add (Av, Ap (I) (1)), Half (M (I), 1)));

end Mdoc_Mac;
