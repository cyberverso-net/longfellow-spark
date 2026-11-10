# Upstream's test documents (block 6 of Phase D, ADR 0086)

One directory per test case of `rust/applications/mdoc_zk/testcases/src/vectors.rs`
of longfellow-zk at commit d5e6be77336933d50bf7f25a954f8ec273eb51ce, the pin
(ADR 0002, ADR 0079), with the case's data as files:

- `mdoc.bin`: the bytes of the `mdoc` array, the credential as the holder
  presents it (CBOR: `documents[0]` with `issuerSigned` and `deviceSigned`);
- `transcript.bin`: the bytes of the `transcript` array, the session transcript;
- `request.txt`: `pkx`, `pky` (the issuer's public key, as upstream writes them),
  `now` (the date the proof is evaluated at) and `doc_type`, one per line.

The files are copied unchanged from the Rust source (the hex arrays as bytes, the
strings as they are). Licence: Apache-2.0, the project's own.

## The 38 cases

The index: the directory, upstream's name of the case (the JSON file its data came from), the document type, the date `now`, the sizes of the document and the transcript, and the SHA-256 of the three files. `FAMILYNAME_MUSTERMANN_MDOC_3` is the document from which upstream made the witness files and the example proofs of both archives under `../` (chapter 9, Section 2.2): `family_name` = `"Mustermann"`, a transcript of 143 bytes, a document of 3,173 bytes; block 6a (#134) checked the ECDSA witnesses of its two signatures against the signature witness files, block 6b (#135) parses all 38 and checks the front of the hash witness files against the parse, block 6c (#136) builds both witnesses of all 38 (`mdoc_witness.txt`, the four witness files reproduced from this document) and proves and verifies every one with upstream's own requests (`make mdoc-cases`). The eight `FAIL_*` cases parse like the others: they fail at the proof, not at the parse; their documents are those of the positive cases of the same number, and upstream's test changes one value of the request (`age_over_18` false, a birth date the document does not hold).

| Directory | Upstream's case | Document type | now | mdoc | transcript | SHA-256 of mdoc.bin, transcript.bin, request.txt |
| --- | --- | --- | --- | ---: | ---: | --- |
| `AADHAAR_AGE_ABOVE18_MDOC_25` | `Aadhaar_age_above18-mdoc[25].json` | `in.gov.uidai.aadhaar.1` | 2026-02-19T23:59:59Z | 2,870 | 61 | `7daa7c3c18d7bb5e…` `37af10cad9a705bb…` `fb61585346aed38f…` |
| `AGE_BIRTH_YEAR_MDOC_8` | `age_birth_year-mdoc[8].json` | `org.iso.18013.5.1.mDL` | 2025-08-01T23:59:59Z | 3,224 | 61 | `5d8d27ba7cb62429…` `1417713f918343ec…` `31bda304c453e880…` |
| `AGE_OVER_18_WEBSITE_MDOC_5` | `age_over_18-website-mdoc[5].json` | `org.iso.18013.5.1.mDL` | 2025-04-30T00:00:00Z | 1,298 | 145 | `490f9871e53e2ad4…` `940c4e23d9b4cd66…` `5e4b18fc08465461…` |
| `AZ_PROD_AGE_OVER_18_MDOC_13` | `AZ_Prod_Age_Over_18-mdoc[13].json` | `org.iso.18013.5.1.mDL` | 2025-12-18T23:59:59Z | 2,585 | 61 | `fd5432ed02577a07…` `1417713f918343ec…` `68f8216e21698e25…` |
| `BIRTHDATE_1968_04_27_ISSUE_DATE_2025_07_21T04_00_00Z_MDOC_8` | `birthdate_1968_04_27,issue_date_2025-07-21T04:00:00Z-mdoc[8].json` | `org.iso.18013.5.1.mDL` | 2025-08-01T23:59:59Z | 3,224 | 61 | `5d8d27ba7cb62429…` `1417713f918343ec…` `31bda304c453e880…` |
| `BIRTHDATE_1971_09_01_MDOC_3` | `birthdate_1971_09_01-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `BIRTHDATE_1998_09_04_IDPASS_MDOC_4` | `birthdate_1998_09_04-idpass-mdoc[4].json` | `com.google.wallet.idcard.1` | 2025-01-29T18:00:00Z | 2,211 | 188 | `1957a5a3bc60c197…` `cbdba50d1c3241e7…` `164989f80749b578…` |
| `CASE_18PLUS__BIRTHDATE_1971_09_01_MDOC_3` | `18+,birthdate_1971_09_01-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `CASE_18PLUS__FAMILYNAME_MUSTERMANN_MDOC_3` | `18+,familyname_mustermann-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `DHS_COMPLIANCE_MDOC_10` | `DHS_compliance-mdoc[10].json` | `org.iso.18013.5.1.mDL` | 2025-08-25T23:59:59Z | 3,331 | 61 | `3283ad8b63b3625d…` `1417713f918343ec…` `687e62122f8192e5…` |
| `EUAV_AGE_OVER_18_MDOC_15` | `EUAV_Age_Over_18-mdoc[15].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,265 | 145 | `f7a9066c377063b5…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_16` | `EUAV_Age_Over_18-mdoc[16].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,265 | 145 | `4e2e8e55f161c4ac…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_17` | `EUAV_Age_Over_18-mdoc[17].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,266 | 145 | `30fdef29547ce1fc…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_18` | `EUAV_Age_Over_18-mdoc[18].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,264 | 145 | `07db99f7f7571d71…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_19` | `EUAV_Age_Over_18-mdoc[19].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,264 | 145 | `aa703cbb1827632a…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_20` | `EUAV_Age_Over_18-mdoc[20].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,265 | 145 | `0ebebd300a000747…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_21` | `EUAV_Age_Over_18-mdoc[21].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,266 | 145 | `37698efa0ffe5ea8…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_22` | `EUAV_Age_Over_18-mdoc[22].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,265 | 145 | `e64350bbcf29c32f…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_23` | `EUAV_Age_Over_18-mdoc[23].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,264 | 145 | `ca0fef19961040f8…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `EUAV_AGE_OVER_18_MDOC_24` | `EUAV_Age_Over_18-mdoc[24].json` | `eu.europa.ec.av.1` | 2026-01-15T09:00:00Z | 1,264 | 145 | `70bcd830f5cb5204…` `940c4e23d9b4cd66…` `49f659d23cb5a7c0…` |
| `FAIL_BIRTHDATE_0971_09_01_MDOC_3` | `fail-birthdate_0971_09_01-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `FAIL_BIRTHDATE_1871_09_01_MDOC_3` | `fail-birthdate_1871_09_01-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `FAIL_BIRTHDATE_1971_09_01_EXTRA_0_MDOC_3` | `fail-birthdate_1971_09_01_extra_0-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `FAIL_NOT_OVER_18_MDOC_0` | `fail-not_over_18-mdoc[0].json` | `org.iso.18013.5.1.mDL` | 2024-01-30T09:00:00Z | 1,451 | 117 | `efe1f06b4fbb81dc…` `3bac193c5c371e8a…` `0e4c129357d8ca6d…` |
| `FAIL_NOT_OVER_18_MDOC_1` | `fail-not_over_18-mdoc[1].json` | `org.iso.18013.5.1.mDL` | 2024-01-31T09:00:00Z | 1,486 | 117 | `b4f38c79cd919642…` `3bac193c5c371e8a…` `d5c0c8ae9a987faa…` |
| `FAIL_NOT_OVER_18_MDOC_2` | `fail-not_over_18-mdoc[2].json` | `org.iso.18013.5.1.mDL` | 2024-05-05T09:00:00Z | 3,272 | 102 | `8994da26c9527da7…` `ebc9628a951ca99e…` `c04542ece8b25433…` |
| `FAMILYNAME_MUSTERMANN_MDOC_3` | `familyname_mustermann-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `HEIGHT175_ISSUE_DATE_2024_03_15_MDOC_3` | `height175,issue_date_2024-03-15-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `HEIGHT_175_MDOC_3` | `height_175-mdoc[3].json` | `org.iso.18013.5.1.mDL` | 2024-10-01T09:00:00Z | 3,173 | 143 | `8583f7eb06731c4d…` `63aa38f9523ee40b…` `e0cfc3d0096db938…` |
| `MT_PROD_AGE_OVER_18_MDOC_12` | `MT_Prod_Age_Over_18-mdoc[12].json` | `org.iso.18013.5.1.mDL` | 2026-01-09T23:59:59Z | 3,475 | 61 | `c1b8bde5d2f38aa2…` `1417713f918343ec…` `f272a6f2480746d5…` |
| `MT_PROD_AGE_OVER_18_MDOC_14` | `MT_Prod_Age_Over_18-mdoc[14].json` | `org.iso.18013.5.1.mDL` | 2025-12-18T23:59:59Z | 3,549 | 61 | `b3fe666578715949…` `1417713f918343ec…` `844eefa672c5e805…` |
| `NOT_OVER_18_LARGE_MDOC_6` | `not_over_18-large-mdoc[6].json` | `org.iso.18013.5.1.mDL` | 2025-06-10T23:59:59Z | 3,321 | 61 | `0107cbaaedc5c252…` `4ada8b03dd6ee867…` `2aa9fe99e9619eac…` |
| `PLUS_18_MDOC_0` | `+18-mdoc[0].json` | `org.iso.18013.5.1.mDL` | 2024-01-30T09:00:00Z | 1,451 | 117 | `efe1f06b4fbb81dc…` `3bac193c5c371e8a…` `0e4c129357d8ca6d…` |
| `PLUS_18_MDOC_1` | `+18-mdoc[1].json` | `org.iso.18013.5.1.mDL` | 2024-01-31T09:00:00Z | 1,486 | 117 | `b4f38c79cd919642…` `3bac193c5c371e8a…` `d5c0c8ae9a987faa…` |
| `PLUS_18_MDOC_2` | `+18-mdoc[2].json` | `org.iso.18013.5.1.mDL` | 2024-05-05T09:00:00Z | 3,272 | 102 | `8994da26c9527da7…` `ebc9628a951ca99e…` `c04542ece8b25433…` |
| `PLUS_18_MDOC_9` | `+18-mdoc[9].json` | `eu.europa.ec.av.1` | 2025-08-25T23:59:59Z | 1,265 | 145 | `112ef502b2339ffd…` `940c4e23d9b4cd66…` `500f06801fca96cb…` |
| `SPARKASSE_AGE_MDOC_11` | `Sparkasse_Age-mdoc[11].json` | `eu.europa.ec.av.1` | 2025-11-06T23:59:59Z | 1,599 | 61 | `83a5069d74cb5fdf…` `dc77e72caaf60066…` `7698b44a5fa268db…` |
| `TEST_DATA` | `` | `org.iso.18013.5.1.mDL` | 2025-04-30T00:00:00Z | 1,298 | 145 | `490f9871e53e2ad4…` `940c4e23d9b4cd66…` `5e4b18fc08465461…` |

The full digests, one per line, so that a copy can be checked with `shasum -a 256 -c`:

```
7daa7c3c18d7bb5e4a62565cc1b1886501456cd0d056a70793fbb54ab4b05afe  AADHAAR_AGE_ABOVE18_MDOC_25/mdoc.bin
37af10cad9a705bb8db99a5b640c4785d79641fd5fd9b3059217bff6a4fe4e93  AADHAAR_AGE_ABOVE18_MDOC_25/transcript.bin
fb61585346aed38f5a337755c696d6e5c398adfa56d7a3a670748b4b4cfdc510  AADHAAR_AGE_ABOVE18_MDOC_25/request.txt
5d8d27ba7cb62429638d9beaf2159917939b8129d326daf5ed7880af5cd2a4fd  AGE_BIRTH_YEAR_MDOC_8/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  AGE_BIRTH_YEAR_MDOC_8/transcript.bin
31bda304c453e880be298efd0078e45c9c2eaef27653a812660a29d0f37f5a45  AGE_BIRTH_YEAR_MDOC_8/request.txt
490f9871e53e2ad469aa0f876cb27c0b86ad175ffe211867991409eb8e412fb8  AGE_OVER_18_WEBSITE_MDOC_5/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  AGE_OVER_18_WEBSITE_MDOC_5/transcript.bin
5e4b18fc0846546177ab438f8fcd5453146ec5649e4059366526c29849cf5757  AGE_OVER_18_WEBSITE_MDOC_5/request.txt
fd5432ed02577a0794b291dffc1d828a922994a0a782a5dae8511ebf2ec99e53  AZ_PROD_AGE_OVER_18_MDOC_13/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  AZ_PROD_AGE_OVER_18_MDOC_13/transcript.bin
68f8216e21698e257e76fd73f2241f2c5c407644cf41c243308f8c4ada4e1be5  AZ_PROD_AGE_OVER_18_MDOC_13/request.txt
5d8d27ba7cb62429638d9beaf2159917939b8129d326daf5ed7880af5cd2a4fd  BIRTHDATE_1968_04_27_ISSUE_DATE_2025_07_21T04_00_00Z_MDOC_8/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  BIRTHDATE_1968_04_27_ISSUE_DATE_2025_07_21T04_00_00Z_MDOC_8/transcript.bin
31bda304c453e880be298efd0078e45c9c2eaef27653a812660a29d0f37f5a45  BIRTHDATE_1968_04_27_ISSUE_DATE_2025_07_21T04_00_00Z_MDOC_8/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  BIRTHDATE_1971_09_01_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  BIRTHDATE_1971_09_01_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  BIRTHDATE_1971_09_01_MDOC_3/request.txt
1957a5a3bc60c19718902aec8512067fdb93a83af92cb23f1c722bf6e5505196  BIRTHDATE_1998_09_04_IDPASS_MDOC_4/mdoc.bin
cbdba50d1c3241e7b7188de27b7b1b763ea821ee0a1036017640bc0f8c655da5  BIRTHDATE_1998_09_04_IDPASS_MDOC_4/transcript.bin
164989f80749b578c17dba2ed99136288fb83b2d6dbe87ffb2d21bb2333f3bc7  BIRTHDATE_1998_09_04_IDPASS_MDOC_4/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  CASE_18PLUS__BIRTHDATE_1971_09_01_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  CASE_18PLUS__BIRTHDATE_1971_09_01_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  CASE_18PLUS__BIRTHDATE_1971_09_01_MDOC_3/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  CASE_18PLUS__FAMILYNAME_MUSTERMANN_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  CASE_18PLUS__FAMILYNAME_MUSTERMANN_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  CASE_18PLUS__FAMILYNAME_MUSTERMANN_MDOC_3/request.txt
3283ad8b63b3625d76034f5a7a94b521123212ff0eed9aa554b699a19260392b  DHS_COMPLIANCE_MDOC_10/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  DHS_COMPLIANCE_MDOC_10/transcript.bin
687e62122f8192e5ddfb24ab1345d0a3d9eca643662017009cb8929f6b2149ad  DHS_COMPLIANCE_MDOC_10/request.txt
f7a9066c377063b5108b5baa29c1145bbf262069be05a2f24b42e81a1ef9f4a1  EUAV_AGE_OVER_18_MDOC_15/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_15/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_15/request.txt
4e2e8e55f161c4acfbd38f6fa9d49a6e216a026b6039534947a2d45ec16f6c3a  EUAV_AGE_OVER_18_MDOC_16/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_16/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_16/request.txt
30fdef29547ce1fc88e1451bac23439adc19637a17607324663e29a00bcf4e13  EUAV_AGE_OVER_18_MDOC_17/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_17/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_17/request.txt
07db99f7f7571d717c0d6e8b6d6240261e37246e4ce9f0a796172695ed949e40  EUAV_AGE_OVER_18_MDOC_18/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_18/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_18/request.txt
aa703cbb1827632a16fd5c002f2c027f1ce0dc088c982bb0365f917cbb799027  EUAV_AGE_OVER_18_MDOC_19/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_19/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_19/request.txt
0ebebd300a00074735c6f295a2a33a9a10f571e5ad29a602cf33884d978746a2  EUAV_AGE_OVER_18_MDOC_20/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_20/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_20/request.txt
37698efa0ffe5ea8674bc2b3db2d2539185ebc05ed8b4ce961d022326584be0c  EUAV_AGE_OVER_18_MDOC_21/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_21/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_21/request.txt
e64350bbcf29c32fcf4ae1c035ef4698ff8d0df91b4d8c3d865d152140c04975  EUAV_AGE_OVER_18_MDOC_22/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_22/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_22/request.txt
ca0fef19961040f834452dfabeefb7f907e04e0813c725ac7e72d4ffbb27d02d  EUAV_AGE_OVER_18_MDOC_23/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_23/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_23/request.txt
70bcd830f5cb5204cd154f6834ec091c9787be732d42b8e93ed740fd47a9e162  EUAV_AGE_OVER_18_MDOC_24/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  EUAV_AGE_OVER_18_MDOC_24/transcript.bin
49f659d23cb5a7c0a4822e3f0768a9ce5426c83ce139a2a6a8bb46fe2f74780b  EUAV_AGE_OVER_18_MDOC_24/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  FAIL_BIRTHDATE_0971_09_01_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  FAIL_BIRTHDATE_0971_09_01_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  FAIL_BIRTHDATE_0971_09_01_MDOC_3/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  FAIL_BIRTHDATE_1871_09_01_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  FAIL_BIRTHDATE_1871_09_01_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  FAIL_BIRTHDATE_1871_09_01_MDOC_3/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  FAIL_BIRTHDATE_1971_09_01_EXTRA_0_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  FAIL_BIRTHDATE_1971_09_01_EXTRA_0_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  FAIL_BIRTHDATE_1971_09_01_EXTRA_0_MDOC_3/request.txt
efe1f06b4fbb81dcdc8784751a6894566979a8ec0154b68b5318be9972b304ca  FAIL_NOT_OVER_18_MDOC_0/mdoc.bin
3bac193c5c371e8a849bf13fbf5f788599f523c7e09d32df1fa59a7931f74e5a  FAIL_NOT_OVER_18_MDOC_0/transcript.bin
0e4c129357d8ca6d11fb77a2c061de29bc76ea6775f022dba62858ab6f3efa95  FAIL_NOT_OVER_18_MDOC_0/request.txt
b4f38c79cd91964246c5c58f1f9660d7d7572de5d8a04a68338438d96c3f96d4  FAIL_NOT_OVER_18_MDOC_1/mdoc.bin
3bac193c5c371e8a849bf13fbf5f788599f523c7e09d32df1fa59a7931f74e5a  FAIL_NOT_OVER_18_MDOC_1/transcript.bin
d5c0c8ae9a987faa82c2446e83b0e5ae13d21033740e9e625473afb1e1aa37a3  FAIL_NOT_OVER_18_MDOC_1/request.txt
8994da26c9527da774f399960135f6deca9d53ff873d81e5cab850d70d0f7ee9  FAIL_NOT_OVER_18_MDOC_2/mdoc.bin
ebc9628a951ca99eca5886814cd76967e866cad82a6ae9ee37596d6241a9a287  FAIL_NOT_OVER_18_MDOC_2/transcript.bin
c04542ece8b2543304c06ff1a6ddca6ba90ee2d3866f6c4c4f9edd05fc98b60e  FAIL_NOT_OVER_18_MDOC_2/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  FAMILYNAME_MUSTERMANN_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  FAMILYNAME_MUSTERMANN_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  FAMILYNAME_MUSTERMANN_MDOC_3/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  HEIGHT175_ISSUE_DATE_2024_03_15_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  HEIGHT175_ISSUE_DATE_2024_03_15_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  HEIGHT175_ISSUE_DATE_2024_03_15_MDOC_3/request.txt
8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  HEIGHT_175_MDOC_3/mdoc.bin
63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  HEIGHT_175_MDOC_3/transcript.bin
e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  HEIGHT_175_MDOC_3/request.txt
c1b8bde5d2f38aa297ca3c8b8d3693913b231e726d447773bca90fd3aab092ba  MT_PROD_AGE_OVER_18_MDOC_12/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  MT_PROD_AGE_OVER_18_MDOC_12/transcript.bin
f272a6f2480746d517ccc52c2df217fd195220a395b788cbf968b1bd355b8ff2  MT_PROD_AGE_OVER_18_MDOC_12/request.txt
b3fe666578715949dd683719c8786c6e2b20626101c5baf409df124a405edc41  MT_PROD_AGE_OVER_18_MDOC_14/mdoc.bin
1417713f918343ec670871d7be257ffc005880ac0acb319bef2f6c139234b3d4  MT_PROD_AGE_OVER_18_MDOC_14/transcript.bin
844eefa672c5e805e8ff3631211da0de652d03c8fd0310a00b00605de0564fd8  MT_PROD_AGE_OVER_18_MDOC_14/request.txt
0107cbaaedc5c252511e9ec44bf6366cec30aa551f4e49d5750c742bf359ccbd  NOT_OVER_18_LARGE_MDOC_6/mdoc.bin
4ada8b03dd6ee86717523a8e1a0957efab6c77525957abf7fe1ba78c4af6cea8  NOT_OVER_18_LARGE_MDOC_6/transcript.bin
2aa9fe99e9619eac2a6bf7d5c9eed37dc21bcbfd453fb2172f3108c478594f16  NOT_OVER_18_LARGE_MDOC_6/request.txt
efe1f06b4fbb81dcdc8784751a6894566979a8ec0154b68b5318be9972b304ca  PLUS_18_MDOC_0/mdoc.bin
3bac193c5c371e8a849bf13fbf5f788599f523c7e09d32df1fa59a7931f74e5a  PLUS_18_MDOC_0/transcript.bin
0e4c129357d8ca6d11fb77a2c061de29bc76ea6775f022dba62858ab6f3efa95  PLUS_18_MDOC_0/request.txt
b4f38c79cd91964246c5c58f1f9660d7d7572de5d8a04a68338438d96c3f96d4  PLUS_18_MDOC_1/mdoc.bin
3bac193c5c371e8a849bf13fbf5f788599f523c7e09d32df1fa59a7931f74e5a  PLUS_18_MDOC_1/transcript.bin
d5c0c8ae9a987faa82c2446e83b0e5ae13d21033740e9e625473afb1e1aa37a3  PLUS_18_MDOC_1/request.txt
8994da26c9527da774f399960135f6deca9d53ff873d81e5cab850d70d0f7ee9  PLUS_18_MDOC_2/mdoc.bin
ebc9628a951ca99eca5886814cd76967e866cad82a6ae9ee37596d6241a9a287  PLUS_18_MDOC_2/transcript.bin
c04542ece8b2543304c06ff1a6ddca6ba90ee2d3866f6c4c4f9edd05fc98b60e  PLUS_18_MDOC_2/request.txt
112ef502b2339ffd96036251376c439e16877fe256fb62aaf3a1b95262cfb1f2  PLUS_18_MDOC_9/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  PLUS_18_MDOC_9/transcript.bin
500f06801fca96cbd9fcf4368aca262d9811794b85f52fc4a5dfd6f48c30c623  PLUS_18_MDOC_9/request.txt
83a5069d74cb5fdf1b7bc8161fa242b4352bae1f9a05e8676a0c642345af7569  SPARKASSE_AGE_MDOC_11/mdoc.bin
dc77e72caaf6006670b9dccb5e1cbbcfb896283adcae45c060cc789b1c4ec7e9  SPARKASSE_AGE_MDOC_11/transcript.bin
7698b44a5fa268db5835c8a3e3efd1ae91c971d9dbc5b423c7670a62fe0d4f62  SPARKASSE_AGE_MDOC_11/request.txt
490f9871e53e2ad469aa0f876cb27c0b86ad175ffe211867991409eb8e412fb8  TEST_DATA/mdoc.bin
940c4e23d9b4cd663c8aad0bc34fc5702b7f53ee1cbd28863c5653049877717c  TEST_DATA/transcript.bin
5e4b18fc0846546177ab438f8fcd5453146ec5649e4059366526c29849cf5757  TEST_DATA/request.txt
```
