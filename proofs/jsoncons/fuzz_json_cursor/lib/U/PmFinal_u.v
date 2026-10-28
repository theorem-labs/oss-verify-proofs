(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u PmHeapClosed10_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Pm10DrvLibL_u Pm10DrvG_u Pm10DrvMain_u Pm10HeapBridge_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Definition budget0_ok (Lay0F : word -> lib_layout) : Prop :=
  forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    Pm10DrvG_u.cred (PmHeapInst10_u.L0 (bv_unsigned sp))
      (PmHeapInst10_u.KPM + 4 * fst (ll_credit (Lay0F sp) n)) (n + PmHeapInst10_u.BOV + 4 * snd (ll_credit (Lay0F sp) n)) 0
      (debit (PmHeapInst10_u.L0 (bv_unsigned sp)) (PmHeapInst10_u.K0, PmHeapInst10_u.B0) 65536).
Lemma budget0_of_bounds : forall (Lay0F : word -> lib_layout),
  (forall sp n, 0 <= n < 67108864 -> 0 <= fst (ll_credit (Lay0F sp) n) <= 1976 /\ 0 <= snd (ll_credit (Lay0F sp) n) <= 2 ^ 30) ->
  budget0_ok Lay0F.
Proof.
  intros Lay0F HB sp n Hsp Hn. specialize (HB sp n Hn).
  unfold Pm10DrvG_u.cred, Pm10DrvG_u.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead PmHeapInst10_u.L0].
  replace PmHeapInst10_u.BOV with 6350523 by vmc_refl. replace PmHeapInst10_u.KPM with 8 by vmc_refl.
  replace PmHeapInst10_u.K0 with 8000 by vmc_refl. replace PmHeapInst10_u.B0 with (2 ^ 33) by vmc_refl. lia.
Qed.

End FPX_1.
