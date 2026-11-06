(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10 PmHeapClosed10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm10DrvLibL Pm10DrvG Pm10DrvMain Pm10HeapBridge.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Definition budget0_ok (Lay0F : word -> lib_layout) : Prop :=
  forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    Pm10DrvG.cred (PmHeapInst10.L0 (bv_unsigned sp))
      (PmHeapInst10.KPM + 4 * fst (ll_credit (Lay0F sp) n)) (n + PmHeapInst10.BOV + 4 * snd (ll_credit (Lay0F sp) n)) 0
      (debit (PmHeapInst10.L0 (bv_unsigned sp)) (PmHeapInst10.K0, PmHeapInst10.B0) 65536).
Lemma budget0_of_bounds : forall (Lay0F : word -> lib_layout),
  (forall sp n, 0 <= n < 67108864 -> 0 <= fst (ll_credit (Lay0F sp) n) <= 1976 /\ 0 <= snd (ll_credit (Lay0F sp) n) <= 2 ^ 30) ->
  budget0_ok Lay0F.
Proof.
  intros Lay0F HB sp n Hsp Hn. specialize (HB sp n Hn).
  unfold Pm10DrvG.cred, Pm10DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead PmHeapInst10.L0].
  replace PmHeapInst10.BOV with 6350523 by vmc_refl. replace PmHeapInst10.KPM with 8 by vmc_refl.
  replace PmHeapInst10.K0 with 8000 by vmc_refl. replace PmHeapInst10.B0 with (2 ^ 33) by vmc_refl. lia.
Qed.

End FPX_1.
