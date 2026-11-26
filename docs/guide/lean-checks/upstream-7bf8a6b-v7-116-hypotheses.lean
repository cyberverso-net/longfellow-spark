/-
  A check of upstream's Lean development, not a proof of this project.

  What it shows: the hypotheses of upstream's 116-bit endpoints for the
  version 7 circuits, at upstream's commit 7bf8a6b (26 October 2026), cannot
  hold together. For each of the four hash profiles (1 to 4 attributes) and
  each of the two endpoints, `v7HashK_deployed_fs_extraction_116_circuit` and
  `v7HashK_deployed_fs_false_statement_116`, it adds a theorem
  `SamplerCheck.<endpoint>_hyps_false : <the binders of the endpoint> -> False`,
  checked by Lean's kernel.

  The argument (the Lean correspondence page, the note on the first row):
  1. `CircuitSide.false_of_card_eq`: the hash side `H` reads the set of opened
     columns from an answer of the transcript, `decodeQuery : C -> Qry`.
     `hkq : kq * card Qry <= card C` with `card C = 2 ^ 256` (`hC`) and
     `card Qry > 2 ^ 256` forces `kq = 0`; then `hbalQuery`, at the share
     `a := c`, any `x`, and the set `decodeQuery c`, bounds by 0 a set of
     answers that contains `c`.
  2. `v7HashK_card_qry`: each hash row has more than 2 ^ 256 sets of 132
     opened columns, C(n, 132) for n = 3230, 3318, 3352, 3436.
  3. `#hyps_false e q`: takes the statement of the endpoint `e` as it is,
     finds its binders `H` and `hC`, applies 1 with the row fact `q`, and adds
     the theorem through the kernel. The axioms of each are printed.

  It builds only inside upstream's `formal/` at 7bf8a6b: it imports
  upstream's modules. It is not part of this project's Lake project (`lean/`)
  or of its gate (`make check`), which do not run it.

  Run on 26 November 2026, Lean 4.31.0, Mathlib v4.31.0, from upstream's
  `formal/` at 7bf8a6b, with Mathlib at `../../mathlib4` as upstream's
  `lakefile.toml` requires:
    lake build LfzkV1.FlatV7All
    lake env lean upstream-7bf8a6b-v7-116-hypotheses.lean
  Expected: eight lines "added SamplerCheck.<endpoint>_hyps_false" and their
  axioms. The carrying lemma uses only `propext`, `Classical.choice` and
  `Quot.sound`; the `native_decide` facts listed with the eight theorems are
  upstream's (`v7HashK_valid`, `v7SigHahn_valid`), named in the endpoints'
  own statements.
-/
import LfzkV1.FlatV7All

namespace LfzkV1.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle LfzkV1.RbrZkLongfellow
  LfzkV1.RbrZkSplit LfzkV1.ZkLigeroV1 LfzkV1.CertifiedV1 LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.ZkArithInit
open LfzkV1.CompiledLongfellow (Col)

namespace CircuitSide

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

theorem false_of_card_eq [Nonempty X]
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (hC : Fintype.card C = 2 ^ 256)
    (hq : 2 ^ 256 < Fintype.card (LigeroV1LayerStep.Qry R.params.row)) : False := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hpos : 0 < Fintype.card C := by rw [hC]; exact Nat.two_pow_pos 256
  obtain ⟨c⟩ := Fintype.card_pos_iff.mp hpos
  have hkq : S.kq = 0 := by
    rcases Nat.eq_zero_or_pos S.kq with h | h
    · exact h
    · exfalso
      have h1 := S.hkq
      have h2 : Fintype.card (LigeroV1LayerStep.Qry R.params.row) ≤
          S.kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) :=
        Nat.le_mul_of_pos_left _ h
      omega
  have hb := S.hbalQuery c x ((S.Vc c x).decodeQuery c)
  rw [hkq, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hb
  exact hb (Finset.mem_univ c) rfl

end CircuitSide

end LfzkV1.CompiledZk

namespace SamplerCheck

open LfzkV1.CertifiedV1

theorem v7Hash1_card_qry : 2 ^ 256 < Fintype.card (LfzkV1.LigeroV1LayerStep.Qry v7Hash1.params.row) := by
  show 2 ^ 256 < Fintype.card (LigeroFamily.QuerySet 3230 132)
  rw [LigeroFamily.QuerySet.fintype_card, Nat.choose_eq_fast_choose]
  decide +kernel

theorem v7Hash2_card_qry : 2 ^ 256 < Fintype.card (LfzkV1.LigeroV1LayerStep.Qry v7Hash2.params.row) := by
  show 2 ^ 256 < Fintype.card (LigeroFamily.QuerySet 3318 132)
  rw [LigeroFamily.QuerySet.fintype_card, Nat.choose_eq_fast_choose]
  decide +kernel

theorem v7Hash3_card_qry : 2 ^ 256 < Fintype.card (LfzkV1.LigeroV1LayerStep.Qry v7Hash3.params.row) := by
  show 2 ^ 256 < Fintype.card (LigeroFamily.QuerySet 3352 132)
  rw [LigeroFamily.QuerySet.fintype_card, Nat.choose_eq_fast_choose]
  decide +kernel

theorem v7Hash4_card_qry : 2 ^ 256 < Fintype.card (LfzkV1.LigeroV1LayerStep.Qry v7Hash4.params.row) := by
  show 2 ^ 256 < Fintype.card (LigeroFamily.QuerySet 3436 132)
  rw [LigeroFamily.QuerySet.fintype_card, Nat.choose_eq_fast_choose]
  decide +kernel

open Lean Meta Elab Command Term in
/-- `#hyps_false e q`: derive `False` from the binders of `e` as stated. -/
elab "#hyps_false " ep:ident q:ident : command => do
  let epName ← liftCoreM <| realizeGlobalConstNoOverloadCore ep.getId
  let qName ← liftCoreM <| realizeGlobalConstNoOverloadCore q.getId
  let newName := `SamplerCheck ++ (epName.updatePrefix .anonymous).appendAfter "_hyps_false"
  liftTermElabM do
    let info ← getConstInfo epName
    let (ty, val) ← forallTelescope info.type fun xs _ => do
      let mut hC? : Option Expr := none
      let mut H? : Option Expr := none
      for x in xs do
        let n ← x.fvarId!.getUserName
        if n == `hC then hC? := some x
        if n == `H then H? := some x
      let some hC := hC? | throwError "no binder hC in {epName}"
      let some H := H? | throwError "no binder H in {epName}"
      logInfo m!"{epName}: H : {← inferType H}; hC : {← inferType hC}"
      let pf ← mkAppM ``LfzkV1.CompiledZk.CircuitSide.false_of_card_eq #[H, hC, mkConst qName]
      let pfTy ← inferType pf
      unless ← isDefEq pfTy (mkConst ``False) do throwError "the proof has type {pfTy}"
      let pf ← instantiateMVars pf
      if pf.hasMVar then throwError "unassigned metavariables in the proof"
      return (← mkForallFVars xs (mkConst ``False), ← mkLambdaFVars xs pf)
    addDecl <| .thmDecl { name := newName, levelParams := info.levelParams, type := ty, value := val }
    logInfo m!"added {newName}"

#hyps_false LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit v7Hash1_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_false_statement_116 v7Hash1_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash2Headline.v7Hash2_deployed_fs_extraction_116_circuit v7Hash2_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash2Headline.v7Hash2_deployed_fs_false_statement_116 v7Hash2_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash3Headline.v7Hash3_deployed_fs_extraction_116_circuit v7Hash3_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash3Headline.v7Hash3_deployed_fs_false_statement_116 v7Hash3_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash4Headline.v7Hash4_deployed_fs_extraction_116_circuit v7Hash4_card_qry
#hyps_false LfzkV1.CompiledZk.FlatV7Hash4Headline.v7Hash4_deployed_fs_false_statement_116 v7Hash4_card_qry

#print axioms v7Hash1_deployed_fs_extraction_116_circuit_hyps_false
#print axioms v7Hash1_deployed_fs_false_statement_116_hyps_false
#print axioms v7Hash2_deployed_fs_extraction_116_circuit_hyps_false
#print axioms v7Hash2_deployed_fs_false_statement_116_hyps_false
#print axioms v7Hash3_deployed_fs_extraction_116_circuit_hyps_false
#print axioms v7Hash3_deployed_fs_false_statement_116_hyps_false
#print axioms v7Hash4_deployed_fs_extraction_116_circuit_hyps_false
#print axioms v7Hash4_deployed_fs_false_statement_116_hyps_false
#print axioms LfzkV1.CompiledZk.CircuitSide.false_of_card_eq

end SamplerCheck
