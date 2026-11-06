(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths and module names changed; 58 of its 99 lines of code are new or changed and 1232 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntClsS6.v, with its module paths and module names changed; 106 of its 144 lines of code are new or changed and 61 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven
ReacHuntStep ReacHuntVerdictName ReacHuntRole ReacHuntHeardAnything ReacDiscoClassify ReacDiscoClassifyOnSegment
ReacHuntObserve DiscoArm3JsonCallee DiscoArm3JtokSpec ReacBoxName CheckSighting ReacDiscoTableObserve
ReacDiscoTableJson.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
DiscoYEntSeat DiscoYEntBody DiscoYEntBodyCall DiscoYEntRecCuts
DiscoYEntProA DiscoYEntProB DiscoYEntProC DiscoYEntProD DiscoYEntProE DiscoYEntHdr DiscoYEntRec DiscoYEntCls
DiscoYEntHobs DiscoYEntObs DiscoYEntR27 DiscoYEntLatch DiscoYEntExit DiscoYEntTop.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi} {PX : PAXcalls lib_both3_0_listing}
  {PO : PAObjImg lib_both3_0_listing} {PW : PAWinImg lib_both3_0_listing}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

#[local] Notation DENV SF6 := (dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6
  (treac_disco_table_init_spec := ReacDiscoTableInit.treac_disco_table_init_spec B)
  (treac_disco_gate_init_spec := ReacDiscoGateInit.treac_disco_gate_init_spec B)
  (treac_disco_peer_lock_init_spec := ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B)
  (treac_hunt_init_spec := ReacHuntInit.treac_hunt_init_spec B)
  (treac_hunt_pin_spec := ReacHuntPin.treac_hunt_pin_spec B)
  (treac_hunt_silence_proven_spec := ReacHuntSilenceProven.treac_hunt_silence_proven_spec B)
  (treac_hunt_step_spec := ReacHuntStep.treac_hunt_step_spec B)
  (treac_hunt_verdict_name_spec := ReacHuntVerdictName.treac_hunt_verdict_name_spec B)
  (treac_hunt_role_spec := ReacHuntRole.treac_hunt_role_spec B)
  (treac_hunt_heard_anything_spec := ReacHuntHeardAnything.treac_hunt_heard_anything_spec B)
  (treac_disco_classify_spec := ReacDiscoClassify.treac_disco_classify_spec B)
  (treac_disco_classify_on_segment_spec := ReacDiscoClassifyOnSegment.treac_disco_classify_on_segment_spec B)
  (treac_hunt_observe_spec := ReacHuntObserve.treac_hunt_observe_spec B)
  (tjson_scalar_spec := DiscoArm3JsonCallee.tjson_scalar_spec B)
  (tjtok_is_spec := DiscoArm3JtokSpec.tjtok_is_spec B)
  (treac_box_name_spec := ReacBoxName.treac_box_name_spec B)
  (tcheck_sighting_spec := CheckSighting.tcheck_sighting_spec B)
  (treac_disco_table_observe_spec := ReacDiscoTableObserve.treac_disco_table_observe_spec B)
  (treac_disco_table_json_spec := ReacDiscoTableJson.treac_disco_table_json_spec B dimg_tj)).

Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis HARM3 : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> arm3_spec B MT XM_LIB RLO RHI tfib_K.

Ltac d_env_open E :=
  pose proof (conj (de_ail _ _ _ _ _ _ _ _ E) (proj2 (de_kcan _ _ _ _ _ _ _ _ E)) : d_can_hyps B tfib_K) as DCAN;
  pose proof (conj (de_dro _ _ _ _ _ _ _ _ E) (conj (de_gm _ _ _ _ _ _ _ _ E) (de_hv _ _ _ _ _ _ _ _ E))
    : d_ro_hyps B) as DROH;
  pose proof (proj2 (de_kcan _ _ _ _ _ _ _ _ E)) as KCAN;
  pose proof (DiscoYEntSeat.d_seat B MT XM_LIB RLO RHI tfib_K) as SEAT;
  pose proof (DiscoYEntSeat.d_facts_ok B MT XM_LIB RLO RHI tfib_K) as FACTS;
  pose proof (DiscoYEntSeat.d_land B MT XM_LIB RLO RHI tfib_K) as LAND;
  pose proof (DiscoYEntBody.d_body_keep B) as BKEEP;
  pose proof (DiscoYEntBody.d_body_rt B) as BRT;
  pose proof (DiscoYEntBody.d_body_read B) as BREAD;
  pose proof (DiscoYEntBody.d_body_call_keep B MT XM_LIB RLO RHI tfib_K) as BCK;
  pose proof (DiscoYEntBody.d_body_tobs B MT XM_LIB RLO RHI tfib_K) as BTOBS;
  pose proof (DiscoYEntBody.d_body_step B MT XM_LIB RLO RHI tfib_K) as BSTEP;
  pose proof (DiscoYEntBodyCall.d_body_pcall B MT XM_LIB RLO RHI tfib_K BSTEP) as BPCALL;
  pose proof (DiscoYEntBodyCall.d_body_malloc B MT XM_LIB RLO RHI tfib_K BSTEP) as BMALLOC;
  pose proof (DiscoYEntBodyCall.d_body_free B MT XM_LIB RLO RHI tfib_K BSTEP) as BFREE;
  destruct E.

Lemma d_env_pro : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> pro_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros SF6_ENTRY E. d_env_open E.
apply DiscoYEntTop.d_pro_of_segs.
- eapply DiscoYEntProA.pb_proA; eassumption.
- eapply DiscoYEntProB.pb_proB; eassumption.
- eapply DiscoYEntProC.pb_proC; eassumption.
- eapply DiscoYEntProD.pb_proD; eassumption.
- eapply DiscoYEntProE.pb_proE; eassumption.
Qed.

Lemma d_env_hdr : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> hdr_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntHdr.pb_hdr; eassumption. Qed.

Lemma d_env_rec : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> rec_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntRec.pb_rec; eassumption. Qed.

Lemma d_env_cls : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> cls_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntCls.pb_cls; eassumption. Qed.

Lemma d_env_hobs : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> hobs_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply (DiscoYEntHobs.pb_hobs B MT XM_LIB XN_LIB); eassumption. Qed.

Lemma d_env_obs : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntObs.pb_obs; eassumption. Qed.

Lemma d_env_r27 : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> r27_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntR27.pb_r27; eassumption. Qed.

Lemma d_env_latch : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> latch_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoYEntLatch.pb_latch; eassumption. Qed.

Lemma d_env_exit : forall SF6_ENTRY : Z, DENV SF6_ENTRY -> exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof.
intros SF6_ENTRY E. d_env_open E.
eapply (DiscoYEntExit.pb_exit B MT de_mt_triv XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY); eassumption.
Qed.

Theorem d_entry_walk_ok : forall SF6_ENTRY : Z, dentry_walk_ok B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY
  (treac_disco_table_init_spec := ReacDiscoTableInit.treac_disco_table_init_spec B)
  (treac_disco_gate_init_spec := ReacDiscoGateInit.treac_disco_gate_init_spec B)
  (treac_disco_peer_lock_init_spec := ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B)
  (treac_hunt_init_spec := ReacHuntInit.treac_hunt_init_spec B)
  (treac_hunt_pin_spec := ReacHuntPin.treac_hunt_pin_spec B)
  (treac_hunt_silence_proven_spec := ReacHuntSilenceProven.treac_hunt_silence_proven_spec B)
  (treac_hunt_step_spec := ReacHuntStep.treac_hunt_step_spec B)
  (treac_hunt_verdict_name_spec := ReacHuntVerdictName.treac_hunt_verdict_name_spec B)
  (treac_hunt_role_spec := ReacHuntRole.treac_hunt_role_spec B)
  (treac_hunt_heard_anything_spec := ReacHuntHeardAnything.treac_hunt_heard_anything_spec B)
  (treac_disco_classify_spec := ReacDiscoClassify.treac_disco_classify_spec B)
  (treac_disco_classify_on_segment_spec := ReacDiscoClassifyOnSegment.treac_disco_classify_on_segment_spec B)
  (treac_hunt_observe_spec := ReacHuntObserve.treac_hunt_observe_spec B)
  (tjson_scalar_spec := DiscoArm3JsonCallee.tjson_scalar_spec B)
  (tjtok_is_spec := DiscoArm3JtokSpec.tjtok_is_spec B)
  (treac_box_name_spec := ReacBoxName.treac_box_name_spec B)
  (tcheck_sighting_spec := CheckSighting.tcheck_sighting_spec B)
  (treac_disco_table_observe_spec := ReacDiscoTableObserve.treac_disco_table_observe_spec B)
  (treac_disco_table_json_spec := ReacDiscoTableJson.treac_disco_table_json_spec B dimg_tj).
Proof.
intros SF6_ENTRY.
exact (DiscoYEntTop.d_dentry_walk_of_parts B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (d_env_pro SF6_ENTRY) (d_env_hdr SF6_ENTRY) (HARM3 SF6_ENTRY) (d_env_rec SF6_ENTRY) (d_env_cls SF6_ENTRY)
  (d_env_hobs SF6_ENTRY) (d_env_obs SF6_ENTRY) (d_env_r27 SF6_ENTRY) (d_env_latch SF6_ENTRY) (d_env_exit SF6_ENTRY)).
Qed.

End h.
End f.
End d.
