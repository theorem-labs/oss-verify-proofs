(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module names changed; 51 of its 86 lines of code are new or changed and 1238 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoRo DiscoEntBodyStmt JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require
DiscoEntPro DiscoEntHdrPb DiscoArm3Top DiscoEntRec2 DiscoEntCls DiscoEntHobs DiscoEntObsAll DiscoEntR27
DiscoEntLatch DiscoEntExit DiscoEntTop.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis tjsc_roimg : tjson_scalar_roimg.

Ltac d_env_open E :=
  pose proof (conj (de_ail _ _ _ _ _ _ _ _ E) (proj2 (de_kcan _ _ _ _ _ _ _ _ E)) : d_can_hyps B tfib_K) as DCAN;
  pose proof (conj (de_dro _ _ _ _ _ _ _ _ E) (conj (de_gm _ _ _ _ _ _ _ _ E) (de_hv _ _ _ _ _ _ _ _ E))
    : d_ro_hyps B) as DROH;
  pose proof (proj2 (de_kcan _ _ _ _ _ _ _ _ E)) as KCAN;
  destruct E.

Lemma d_env_pro : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  pro_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntPro.pb_pro; eassumption. Qed.

Lemma d_env_hdr : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  hdr_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntHdrPb.pb_hdr; eassumption. Qed.

Lemma d_env_arm3 : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  arm3_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoArm3Top.arm3_proved; eassumption. Qed.

Lemma d_env_rec : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  rec_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntRec2.rec_spec_pf; eassumption. Qed.

Lemma d_env_cls : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  cls_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntCls.cls_spec_pf; eassumption. Qed.

Lemma d_env_hobs : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  hobs_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntHobs.hobs_spec_pf; eassumption. Qed.

Lemma d_env_obs : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntObsAll.pb_obs_spec; eassumption. Qed.

Lemma d_env_r27 : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  r27_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntR27.r27_ok; eassumption. Qed.

Lemma d_env_latch : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  latch_spec B MT XM_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntLatch.pb_latch; eassumption. Qed.

Lemma d_env_exit : forall SF6_ENTRY, dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY ->
  exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof. intros SF6_ENTRY E. d_env_open E. eapply DiscoEntExit.pb_exit; eassumption. Qed.

Theorem d_entry_walk_ok : forall SF6_ENTRY : Z, dentry_walk_ok B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY.
Proof.
  intros SF6_ENTRY.
  exact (DiscoEntTop.d_dentry_walk_of_parts B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY
    (d_env_pro SF6_ENTRY) (d_env_hdr SF6_ENTRY) (d_env_arm3 SF6_ENTRY) (d_env_rec SF6_ENTRY)
    (d_env_cls SF6_ENTRY) (d_env_hobs SF6_ENTRY) (d_env_obs SF6_ENTRY) (d_env_r27 SF6_ENTRY)
    (d_env_latch SF6_ENTRY) (d_env_exit SF6_ENTRY)).
Qed.

End h.
End f.
End d.
