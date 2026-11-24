/-
The axiom check of the step `lean` (ADR 0091): every lemma a SPARK contract
cites depends on the standard axioms only, `propext`, `Classical.choice` and
`Quot.sound`. No `sorry` (`sorryAx`), no `native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`), and no axiom of this project's own. On the pattern of
upstream's `formal/scripts/Audit.lean`, restricted to the cited lemmas.

Run with `lake env lean scripts/Axioms.lean` from `lean/`; it fails if a cited
lemma is missing or depends on any other axiom.
-/
import Mathlib
import LongfellowSpark

open Lean Elab Command

/-- The lemmas the SPARK contracts cite, by name. -/
def citedLemmas : List Name :=
  [`LongfellowSpark.Plucker.output_is_bit,
   `LongfellowSpark.BitAdder.assert_eqmod_words,
   `LongfellowSpark.GF128.alpha_order,
   `LongfellowSpark.GF128.assert_eqmod_words_gf128,
   `LongfellowSpark.GF128.ev_mul,
   `LongfellowSpark.GF128.ev_xor,
   `LongfellowSpark.GF128.ev_inj]

def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#check_cited_axioms" : command => do
  let env ← getEnv
  let mut bad := false
  for n in citedLemmas do
    unless env.contains n do
      logError m!"cited lemma missing: {n}"
      bad := true
      continue
    let axs ← liftCoreM (Lean.collectAxioms n)
    let other := axs.filter (fun a => !allowedAxioms.contains a)
    if other.isEmpty then
      logInfo m!"{n}: {axs.toList}"
    else
      logError m!"{n} depends on {other.toList}"
      bad := true
  if bad then
    throwError "axiom check failed"

#check_cited_axioms
