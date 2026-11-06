(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic SymPlan SymPlanSoundA SymPlanSound SymPlanStmts FContract RefATB
  LibCas LibCas2 RefMemcpyBase RefMemcpy
  SymPlanSoundEF SymPlanSoundFP SymPlanSoundSW SymPlanSoundMR SymPlanSoundPF SymPlanSoundEX RefTargetAssembly.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma cas_or_ok : cas_or_stmt RSEGS (SP.t_cas_or REF_ATB) (SP.t_cas_or_k REF_ATB).
Proof.
  unfold cas_or_stmt. intros. cbn [SP.t_cas_or SP.t_cas_or_k REF_ATB].
  replace (Z_to_bv 64 0x1c430) with (0x1c430%bv : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x1c450) with (0x1c450%bv : word) by (apply bv_eq; reflexivity).
  eapply cas_or_1c134; eassumption.
Qed.

Lemma cas_and_ok : cas_and_stmt RSEGS (SP.t_cas_and REF_ATB) (SP.t_cas_and_k REF_ATB).
Proof.
  unfold cas_and_stmt. intros. cbn [SP.t_cas_and SP.t_cas_and_k REF_ATB].
  replace (Z_to_bv 64 0x1cc10) with (0x1cc10%bv : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x1cc30) with (0x1cc30%bv : word) by (apply bv_eq; reflexivity).
  eapply cas_and_1c914; eassumption.
Qed.

Lemma cas_lock_ok : cas_lock_stmt RSEGS (SP.t_cas_lock REF_ATB) (SP.t_cas_lock_k REF_ATB).
Proof.
  unfold cas_lock_stmt. intros. cbn [SP.t_cas_lock SP.t_cas_lock_k REF_ATB].
  replace (Z_to_bv 64 0x1bb18) with (0x1bb18%bv : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x1bb28) with (0x1bb28%bv : word) by (apply bv_eq; reflexivity).
  eapply cas_lock_1b958; eassumption.
Qed.

Lemma memcpy_ok : memcpy_stmt RSEGS (SP.t_memcpy REF_ATB).
Proof.
  intros mem0 dst src n bs rom [H1 H2 H3 H4 H5 H6 H7] regs ret Hret R1 R10 R11 R12.
  cbn [SP.t_memcpy REF_ATB]. replace (Z_to_bv 64 0x23640) with (0x23640%bv : word) by (apply bv_eq; reflexivity).
  exact (ref_memcpy mem0 dst src n bs rom (MCH mem0 dst src n bs H1 H2 H3 H4 H5 H6 H7) regs ret Hret R1 R10 R11 R12).
Qed.

Theorem ref_tphase_hyps_of : F_contract RSEGS FP_src0 -> ref_tphase_hyps.
Proof.
  intros FC. constructor.
  - exact cas_or_ok.
  - exact cas_and_ok.
  - exact cas_lock_ok.
  - exact memcpy_ok.
  - exact call_enframe2_ok.
  - exact call_freepro_ok.
  - exact node_stdio_write_ok.
  - exact call_mainret_ok.
  - exact call_printf_ok.
  - exact node_exitcall_ok.
  - exact FC.
Qed.
