(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec TargetSpec TargetKDefs SymPlanSoundA RefWorld RefWorldK
  RefTargetPre RefTargetPreK RefTargetAssembly RefTargetHyps RefTargetPhase RefTargetPhaseK VFC_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma ref_tphase_hyps_ok : ref_tphase_hyps.
Proof. exact (ref_tphase_hyps_of fc_src0). Qed.

Theorem target_phase_top :
  forall (sp0 gm area brkv mas tid : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof. exact (target_phase ref_tphase_hyps_ok). Qed.

Theorem target_phase_k_top :
  forall k : Z, (1 <= k <= 10)%Z ->
  forall (sp0 B area brkv mas tid : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof. exact (target_phase_k ref_tphase_hyps_ok). Qed.
