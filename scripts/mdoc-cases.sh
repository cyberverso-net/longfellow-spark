#!/bin/bash
#  The proof of age from every test document of upstream (Phase D,
#  block 6, ADR 0086): longfellow_prove_mdoc --mdoc on each of the 38
#  documents under tests/vectors/upstream/mdoc/testcases/, under the
#  parameters of its case (request.txt, transcript.bin) and one
#  requested attribute, then longfellow_verify_mdoc on the proof.
#
#  The requests follow upstream's own tests (runtime/tests/all/
#  current_zk.rs at d5e6be7): a positive case requests the document's
#  attributes with their own values, a negative case (fail-*) the same
#  with one value changed, age_over_18 false or a birth date the
#  document does not hold. The archives hold one attribute, so each
#  proof here requests one: age_over_18 where the document has it, else
#  its first attribute. Every positive case must prove and verify; every
#  negative case must be refused by the prover with hash_failed
#  not_satisfied (the circuit is not satisfied by a value the document
#  contradicts). At version 6 the two documents whose MSO exceeds the
#  capacity of the version 6 circuit must be refused at the parse, and
#  the eight documents whose issuer-signed item does not hold the
#  elementValue entry right after the elementIdentifier entry must be
#  refused by the builder (item_order_unsupported, #150): the version 6
#  circuit checks the identifier's text, the key elementValue and the
#  value as one span, where the version 7 circuit reads the order of
#  the four entries from the witness. Upstream's test skips every order
#  but the standard one for the prior versions
#  (is_supported_by_prior_version of runtime/tests/all/prior_zk.rs);
#  the circuit itself accepts the two EUAV documents whose identifier
#  comes first and value second, and so does the builder.
#
#  Usage: scripts/mdoc-cases.sh [v7|v6]     (default: both)
#  Needs the release build (make cli). The cli step of make check runs
#  it after the round trips of measure-mdoc.sh, about seven minutes on
#  the proving machine, and skips it on GitHub Actions, whose job would
#  exceed its 30 minutes; `make mdoc-cases` runs it alone.

set -euo pipefail
cd "$(dirname "$0")/.."
BIN="${MEASURE_BIN:-cli/bin}"
M=tests/vectors/upstream/mdoc
VERSIONS="${1:-v7 v6}"
hash_of() {
   case $1 in
      v7) echo 8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121 ;;
      v6) echo 137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6 ;;
   esac
}
#  The cases: the directory, the requested attribute (ID:CBORHEX), and
#  what the prover must say: ok, or its status. The values are the
#  documents' (tests/vectors/mdoc_witness.txt lists every item), except
#  in the negative cases, where upstream's test changes them.
CASES='
AADHAAR_AGE_ABOVE18_MDOC_25 age_above18:63596573 ok
AGE_BIRTH_YEAR_MDOC_8 age_birth_year:1907b0 ok
AGE_OVER_18_WEBSITE_MDOC_5 age_over_18:f5 ok
AZ_PROD_AGE_OVER_18_MDOC_13 age_over_18:f5 ok
BIRTHDATE_1968_04_27_ISSUE_DATE_2025_07_21T04_00_00Z_MDOC_8 age_birth_year:1907b0 ok
BIRTHDATE_1971_09_01_MDOC_3 birth_date:d903ec6a313937312d30392d3031 ok
BIRTHDATE_1998_09_04_IDPASS_MDOC_4 birth_date:d903ec6a313939382d30392d3034 ok
CASE_18PLUS__BIRTHDATE_1971_09_01_MDOC_3 age_over_18:f5 ok
CASE_18PLUS__FAMILYNAME_MUSTERMANN_MDOC_3 age_over_18:f5 ok
DHS_COMPLIANCE_MDOC_10 DHS_compliance:6146 ok
EUAV_AGE_OVER_18_MDOC_15 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_16 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_17 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_18 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_19 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_20 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_21 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_22 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_23 age_over_18:f5 ok
EUAV_AGE_OVER_18_MDOC_24 age_over_18:f5 ok
FAIL_BIRTHDATE_0971_09_01_MDOC_3 birth_date:d903ec6a303937312d30392d3031 hash_failed_not_satisfied
FAIL_BIRTHDATE_1871_09_01_MDOC_3 birth_date:d903ec6a313837312d30392d3031 hash_failed_not_satisfied
FAIL_BIRTHDATE_1971_09_01_EXTRA_0_MDOC_3 birth_date:d903ec6b313937312d30392d303130 hash_failed_not_satisfied
FAIL_NOT_OVER_18_MDOC_0 age_over_18:f4 hash_failed_not_satisfied
FAIL_NOT_OVER_18_MDOC_1 age_over_18:f4 hash_failed_not_satisfied
FAIL_NOT_OVER_18_MDOC_2 age_over_18:f4 hash_failed_not_satisfied
FAMILYNAME_MUSTERMANN_MDOC_3 family_name:6a4d75737465726d616e6e ok
HEIGHT175_ISSUE_DATE_2024_03_15_MDOC_3 height:18af ok
HEIGHT_175_MDOC_3 height:18af ok
MT_PROD_AGE_OVER_18_MDOC_12 age_over_18:f5 ok
MT_PROD_AGE_OVER_18_MDOC_14 age_over_18:f5 ok
NOT_OVER_18_LARGE_MDOC_6 age_over_18:f4 ok
PLUS_18_MDOC_0 age_over_18:f5 ok
PLUS_18_MDOC_1 age_over_18:f5 ok
PLUS_18_MDOC_2 age_over_18:f5 ok
PLUS_18_MDOC_9 age_over_18:f5 ok
SPARKASSE_AGE_MDOC_11 age_over_18:f5 ok
TEST_DATA age_over_18:f5 ok
'
#  At version 6 the MSO of these two documents (2,300 and 2,374 bytes
#  of map) exceeds the capacity of the circuit (2,211 of wrapped MSO).
V6_TOO_BIG="MT_PROD_AGE_OVER_18_MDOC_12 MT_PROD_AGE_OVER_18_MDOC_14"
#  At version 6 the item of these eight documents does not hold the
#  value right after the identifier (the permutations 177, 198, 27, 39,
#  54, 201, 45, 57 of mdoc_parse.txt; EUAV 20 and 21, with 75 and 78,
#  identifier first and value second, prove): the builder refuses them.
V6_UNFRAMED="AZ_PROD_AGE_OVER_18_MDOC_13 EUAV_AGE_OVER_18_MDOC_16 EUAV_AGE_OVER_18_MDOC_17 EUAV_AGE_OVER_18_MDOC_18 EUAV_AGE_OVER_18_MDOC_19 EUAV_AGE_OVER_18_MDOC_22 EUAV_AGE_OVER_18_MDOC_23 EUAV_AGE_OVER_18_MDOC_24"
mkdir -p cli/out
for v in $VERSIONS; do
   h=$(hash_of "$v")
   echo "$CASES" | while read -r name attr want; do
      [ -n "$name" ] || continue
      d=$M/testcases/$name
      pkx=$(sed -n 's/^pkx //p' "$d/request.txt")
      pky=$(sed -n 's/^pky //p' "$d/request.txt")
      now=$(sed -n 's/^now //p' "$d/request.txt")
      doc_type=$(sed -n 's/^doc_type //p' "$d/request.txt")
      if [ "$v" = v6 ] && echo "$V6_TOO_BIG" | grep -qw "$name"; then
         want=parse_failed_too_big
      elif [ "$v" = v6 ] && echo "$V6_UNFRAMED" | grep -qw "$name"; then
         want=item_order_unsupported
      fi
      proof=cli/out/mdoc_case_${v}_$name.bin
      status=0
      out="$("$BIN/longfellow_prove_mdoc" --spec "$h" --mdoc "$d/mdoc.bin" --pkx "$pkx" --pky "$pky" \
         --transcript-file "$d/transcript.bin" --now "$now" --doc-type "$doc_type" --attr "$attr" \
         --seed 1 --out "$proof" 2>&1)" || status=$?
      got="$(echo "$out" | head -1 | sed 's/^ok:.*/ok/; s/ /_/g')"
      if [ "$want" = ok ]; then
         if [ "$status" -ne 0 ] || [ "$got" != ok ]; then
            echo "FAIL $v $name: prover said '$(echo "$out" | head -1)' (exit $status), expected a proof"
            exit 1
         fi
         if ! vout="$("$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" --pkx "$pkx" --pky "$pky" \
               --transcript-file "$d/transcript.bin" --now "$now" --doc-type "$doc_type" --attr "$attr" 2>&1)"; then
            echo "FAIL $v $name: verifier said '$(echo "$vout" | head -1)'"
            exit 1
         fi
         echo "ok   $v $name ($attr): proved and verified"
      else
         if [ "$status" -ne 1 ] || [ "$got" != "$want" ]; then
            echo "FAIL $v $name: prover said '$(echo "$out" | head -1)' (exit $status), expected $want"
            exit 1
         fi
         echo "ok   $v $name ($attr): refused, $(echo "$out" | head -1)"
      fi
      rm -f "$proof"
   done || exit 1
done
echo "mdoc-cases: every case as expected"
