--  Circuit_Status: the outcome of loading a circuit file (Phase B, ADR
--  0046). One value per cause the loader can produce, no exceptions,
--  as Verifier_Status does for the verifier (ADR 0039).
--
--    Ok                 the circuit is loaded, well formed, its
--                       identifier matches
--    Bad_Magic          the file does not start with "LFC2"
--    Field_Mismatch     the field identifier is not the instance's
--    Unsupported_Copies ncopies is not 1
--    Bad_Integer        a ULEB128 integer of more than four bytes
--    Bound_Exceeded     a count outside this project's bounds (wires,
--                       layers, logw, terms) or no layer at all
--    Bad_Element        a constant that is not a canonical element
--    Bad_Index          a constant, delta or segment index out of range,
--                       or a wire index outside 0 .. Max_Wires - 1
--    Truncated          bytes missing
--    Trailing_Bytes     bytes after the identifier
--    Id_Mismatch        the stored identifier is not the circuit's
--    Not_Well_Formed    the loaded circuit violates Well_Formed of the
--                       core (a wire outside its layer's width, a width
--                       above 2^logw, a last layer not reading ninput
--                       wires, npublic above ninput)
--
--  Documentation: docs/guide/06-circuits.md. Proof status: an
--  enumeration, nothing to prove.

pragma SPARK_Mode (On);

package Circuit_Status is

   type Status is
     (Ok,
      Bad_Magic,
      Field_Mismatch,
      Unsupported_Copies,
      Bad_Integer,
      Bound_Exceeded,
      Bad_Element,
      Bad_Index,
      Truncated,
      Trailing_Bytes,
      Id_Mismatch,
      Not_Well_Formed);

end Circuit_Status;
