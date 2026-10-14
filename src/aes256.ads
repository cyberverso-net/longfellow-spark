--  Aes256: AES-256 single-block encryption of FIPS 197 (key expansion
--  and the forward cipher only, no decryption), for the keystream
--  generator FsPrf of the Fiat-Shamir transcript (draft Section 3.1.1:
--  Block[i] = AES256(SEED, ID(i)); the counter mode is built over this
--  package by Transcript).
--
--  Documentation: docs/guide/04-transcript.md. Decisions implemented
--  here: ADR 0029 (written in SPARK, Silver, functional correctness by
--  NIST vectors, table-based, constant-time exemption); frame: ADR
--  0002, 0003, 0020. Index: docs/adr/README.md.
--
--  Proof status (Silver = absence of run-time errors).
--
--    Expand_Key, Encrypt : Silver. That Encrypt is the AES-256 forward
--              cipher is NOT proved; it is tested against FIPS 197
--              Appendix C.3 and the counter blocks of NIST SP 800-38A
--              Appendix F.5.5 (tests/vectors/aes256.txt, harness
--              transcript_kat) and, through the transcript, against
--              draft Appendix B.2.
--
--  Representation. The state is the 16 bytes of the block in order,
--  column-major as in FIPS 197 Section 3.4: state (r, c) is at index
--  4 c + r. The key schedule holds the fifteen round keys as bytes.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0029.
--  The S-box is a table indexed by data bytes, the textbook case the
--  discipline excludes; it is acceptable because this package
--  processes public data only, the seed and counter of a transcript
--  whose content is the proof string. This package MUST NOT be used
--  on secret data; a future use on secrets is a new decision (a
--  bitsliced implementation, ADR 0029).

pragma SPARK_Mode (On);

with Bytes; use Bytes;

package Aes256 is

   type Key_Schedule is private;

   --  FIPS 197 Section 5.2 with Nk = 8.
   function Expand_Key (Key : Bytes_32) return Key_Schedule with
     Global => null;

   --  FIPS 197 Section 5.1: fourteen rounds.
   function Encrypt (KS : Key_Schedule; Input : Bytes_16) return Bytes_16
   with
     Global => null;

private

   Rounds : constant := 14;

   type Round_Index is range 0 .. Rounds;
   type Round_Keys is array (Round_Index) of Bytes_16;

   type Key_Schedule is record
      Keys : Round_Keys;
   end record;

end Aes256;
