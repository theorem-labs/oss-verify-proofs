(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Ub0DrvLibL Src0DrvG Ub0DrvG Src0DrvMain Ub0DrvMain
  Src0HeapBridge Ub0HeapBridge BigintTop2 L5Top L5TopU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Lemma drv_lib_layout_top0 : forall sp, valid_sp sp ->
  Src0DrvLibL.drv_lib_layout (L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp))) (HeapInst0.L0 (bv_unsigned sp)).
Proof.
  intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
  - intros iv [<-|[<-|[<-|[]]]]; cbn; lia.
  - intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
  - intros n Hn. cbn. unfold L5Top.L5TOP.TOPK, L5Top.L5TOP.TOPB. lia.
Qed.

Lemma drv_lib_layout_top1 : forall sp, valid_sp sp ->
  Ub0DrvLibL.drv_lib_layout (L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp))) (HeapInst1.L1 (bv_unsigned sp)).
Proof.
  intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
  - intros iv [<-|[<-|[<-|[]]]]; cbn; lia.
  - intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
  - intros n Hn. cbn. unfold L5TopU.L5TOPU.TOPK, L5TopU.L5TOPU.TOPB. lia.
Qed.

(* [comment removed for export] *)
Lemma budget0 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Src0DrvG.cred (HeapInst0.L0 (bv_unsigned sp))
    (HeapInst0.KPM + 4 * fst (ll_credit (L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp))) n))
    (n + HeapInst0.BOV + 4 * snd (ll_credit (L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp))) n)) 0
    (debit (HeapInst0.L0 (bv_unsigned sp)) (HeapInst0.K0, HeapInst0.B0) 65536).
Proof.
  intros sp n Hsp Hn. unfold Src0DrvG.cred, Src0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeapInst0.L0 ll_credit L5Top.L5TOP.TopLay].
  unfold L5Top.L5TOP.TOPK, L5Top.L5TOP.TOPB.
  replace HeapInst0.BOV with 6350523 by (vm_compute; reflexivity). replace HeapInst0.KPM with 8 by (vm_compute; reflexivity).
  replace HeapInst0.K0 with 8000 by (vm_compute; reflexivity). replace HeapInst0.B0 with (2 ^ 33) by (vm_compute; reflexivity). lia.
Qed.

Lemma budget1 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Ub0DrvG.cred (HeapInst1.L1 (bv_unsigned sp))
    (HeapInst1.KPM + 4 * fst (ll_credit (L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp))) n))
    (n + HeapInst1.BOV + 4 * snd (ll_credit (L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp))) n)) 0
    (debit (HeapInst1.L1 (bv_unsigned sp)) (HeapInst1.K0, HeapInst1.B0) 65536).
Proof.
  intros sp n Hsp Hn. unfold Ub0DrvG.cred, Ub0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeapInst1.L1 ll_credit L5TopU.L5TOPU.TopLay].
  unfold L5TopU.L5TOPU.TOPK, L5TopU.L5TOPU.TOPB.
  replace HeapInst1.BOV with 6350523 by (vm_compute; reflexivity). replace HeapInst1.KPM with 8 by (vm_compute; reflexivity).
  replace HeapInst1.K0 with 8000 by (vm_compute; reflexivity). replace HeapInst1.B0 with (2 ^ 33) by (vm_compute; reflexivity). lia.
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_ubsan_final :
  (forall sp, valid_sp sp ->
     lib_iface_ok (L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp))) cfg0 (HeapInst0.HI0 (bv_unsigned sp))
                  (L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))) ->
  (forall sp, valid_sp sp ->
     lib_iface_ok (L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp))) cfg0 (HeapInst1.HI1 (bv_unsigned sp))
                  (L5TopU.L5TOPU.TopLS (HeapInst1.L1 (bv_unsigned sp)))) ->
  strong_universal_error_free_T_scfg cfg0
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros LIB0 LIB1. apply fuzz_bigint_ubsan_ok2.
  - apply (src0_realizes_spec_heap cfg0 eq_refl eq_refl
             (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
             (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp))));
      [exact drv_lib_layout_top0 | exact LIB0 | exact budget0].
  - apply (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
             (fun sp => L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp)))
             (fun sp => L5TopU.L5TOPU.TopLS (HeapInst1.L1 (bv_unsigned sp))));
      [exact drv_lib_layout_top1 | exact LIB1 | exact budget1].
Qed.

End FPX_1.
