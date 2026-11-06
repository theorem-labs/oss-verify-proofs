(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcCf.v (commit 67deba317dfb, blob cdefed92c53e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase YGcfDIface YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstRcPrim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrcReadsA DMrcSecReadsA DMrcFhCf DMrcSecCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecCutCf DMrcSecMaprCf DMrcPrim DMrcRhA DMrcRhOkA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFg8.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstRcSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRehideAR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Local Notation NMAXD_cf := YGcfInstDrainR.NMAXD_cf.
Local Notation LMAXD_cf := YGcfInstDrainR.LMAXD_cf.
Local Notation RMAXD_cf := YGcfInstDrainR.RMAXD_cf.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.

Lemma SC_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp, YGcfInstBase.IOK_ok B IOK ->
  DMrcSecReadsA.rc_sec_cut_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp).
Proof. exact DMrcSecCutCf.rc_sec_cut_of_cf. Qed.
Lemma SM_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  DMrcSecReadsA.rc_sec_mapr_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp).
Proof. exact DMrcSecMaprCf.rc_sec_mapr_of_cf. Qed.

Lemma cd_model_of_cf : forall R S c off, YGcfInstRcPrim.cd_model_cf R S c off -> DMwalkIFA.cd_model R S c off.
Proof. intros R S c off H. exact H. Qed.

Lemma rc_prim_step_preset : forall (B : asyms) IOK Hp,
  DMrcReadsA.rc_prim_step_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B) (YGcfInstDrainR.DRq_cf B kQuarantineMax)
    RMAXD_cf.
Proof.
intros B IOK Hp inst ly X k ks zs cbp W regs mem md off mem' md' PRE DR Hb AG VIS NEW HK CONST Ev El Ee.
assert (HR : kFreeArrayOffset <= RMAXD_cf) by (unfold RMAXD_cf; lia).
destruct (YGcfInstRcPrim.rc_prim_step_cf B IOK Hp kQuarantineMax RMAXD_cf HR inst ly X k ks zs cbp W regs mem md off mem' md'
  PRE DR Hb AG VIS NEW HK CONST Ev El Ee) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact (cd_model_of_cf _ _ _ _ A2)|].
split; [exact A3|]. split; [exact A4 | exact A5].
Qed.

Lemma rc_prim_mach_rh_cf : forall (B : asyms) IOK Hp,
  DMrcRhOkA.rc_prim_mach_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
intros B IOK Hp TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
eapply YG0dH.amreal'_mono; [| exact (YG0dH.amreal_amreal' tfibsegs YGcfRehidePost.RZ_cf _ _ _ _
  (DMrcPrim.rchunk_prim_m B TB _ (aowned B) _ RMAXD_cf RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb))].
intros r0 W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B _ (aowned B) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.

Lemma rc_sec_pre_rh_cf : forall (B : asyms) IOK Hp,
  DMrcRhOkA.rc_sec_pre_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp).
Proof.
intros B IOK Hp inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hk Hst.
pose proof (proj1 (proj2 (proj1 PRE))) as MR.
pose proof (@YGcfInstRcSec.KFACTS rc ci cp AImg_A B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & EL & _ & _ & GI & _).
pose proof (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ (YGcfInstDrainR.amr_wfr _ _ _ _ _ (proj1 MR))) k Hk) as CK.
assert (EL' : AFg8.LEN sm = YGcfInstRcSec.LEN k) by exact EL.
split.
{
  pose proof MR as (_ & _ & (_ & SA & _) & _). rewrite EL'. exact (proj2 (SA _ GI)). }
split; [exact (YGcfRehideAR.SREAL_of_pre X k r o sm CK Hb Hsm)|].
split; [|exact (YGcfRehideAR.M2_of_pre X k r o sm CK Hb Hsm)].

apply Forall_forall. intros e He. rewrite <- DMrcSecCf.X2_eq in He.
apply YGcfRehideAR.zdisjoint_sym_rh. rewrite EL'.
exact (YGcfInstRcSec.APART2 (IM := AImg_A) B ly X Hp k r o sm i W mem md MR Hk Hb Hsm e He).
Qed.

(* This unit's world carries w_H8 (YA0n.v), so the re-hidden world takes a proof of it: HW8 in DMrcRhA.rc_sec_rehide_t,
   YGcfRehideAR.rh_H8 in ARcfR_rehide. ARcfR reads the world only through w_H and w_A, so the two goals are
   convertible. *)
Lemma rc_sec_rehide_all_cf : forall (B : asyms) IOK Hp,
  DMrcRhOkA.rc_sec_rehide_all_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (DMrcSecCf.ARXsl_cf B IOK Hp).
Proof.
intros B IOK Hp inst ly X k r sm i W2' mem' md' sm2 HO HA HW8 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 (HI & HSL & HX) H12.
split; [exact HI|]. split; [|exact HX].
exact (YGcfRehideAR.ARcfR_rehide tfibsegs B ly _ Hp W2' mem' md' (AFg8.MAP ly r) (AFg8.LEN sm) r sm2 HO HA
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 HSL H12).
Qed.

Theorem rc_reads_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMrcRhOkA.rc_reads_rh B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (DMrcSecCf.ARXsl_cf B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
intros B TB IOK Hp HIOK EAP RLE.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [|split; [|split; [|split]]].
  + exact (YGcfInstRcPrim.rc_head_cf B kQuarantineMax).
  + exact (YGcfInstRcPrim.rc_model_cf B kQuarantineMax).
  + exact (DMrcFhCf.rc_prim_fh_of_cut B TB _ _ (YGcfInstRcPrim.rc_fh_cut_facts_cf B IOK Hp kQuarantineMax HIOK ADIfaceA.img_cover_A)).
  + exact (rc_prim_step_preset B IOK Hp).
  + intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb G.
    exact (YGcfInstRcPrim.rc_prim_room_cf B IOK Hp kQuarantineMax inst ly X k ks zs cbp W regs mem md off PRE RX Hb G).
- exact (rc_prim_mach_rh_cf B IOK Hp).
- exact (SC_cf B TB IOK Hp HIOK).
- exact (SM_cf B TB IOK Hp).
- exact (DMrcSecCf.rc_sec_step_sl_of_cf B TB IOK Hp EAP RLE).
- exact (YGcfInstRcPrim.rc_split_cf B kQuarantineMax).
- exact (rc_sec_pre_rh_cf B IOK Hp).
- exact (rc_sec_rehide_all_cf B IOK Hp).
Qed.

Theorem rchunk_ok_rh_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMwalkIFRhA.rchunk_ok_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B)
    (YGcfInstDrainR.DRq_cf B kQuarantineMax) NMAXD_cf LMAXD_cf RMAXD_cf.
Proof.
intros B TB IOK Hp HIOK EAP RLE.
exact (DMrcRhOkA.rchunk_ok_rh B _ (DMrcSecCf.ARXsl_cf B IOK Hp) _ _ NMAXD_cf LMAXD_cf RMAXD_cf
  (rc_reads_cf B TB IOK Hp HIOK EAP RLE)).
Qed.

Lemma DS_cf : forall (B : asyms), DMwalkIFA.drq_sizes (YGcfInstDrainR.DRq_cf B kQuarantineMax) NMAXD_cf LMAXD_cf.
Proof. intros B. exact (YGcfInstDrainR.drq_sizes_cf B kQuarantineMax ltac:(unfold kMaxSize, kQuarantineMax; lia)). Qed.

Theorem rchunk_ok_rh_cf_closed : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfInstBase.IOK_ok B IOK -> YGcfImgRows.ERRB_QAPART -> DMrcSecCf.REC_LE ->
  DMiface.di_frame_t (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B) ->
  DMwalkIFA.di_rview_x_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (YGcfInstDrainR.DRq_cf B kQuarantineMax) RMAXD_cf ->
  DMwalkIFA.cdealloc_g_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B) RMAXD_cf ->
  DMwalkIFRhA.rchunk_m_rh_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (aowned B) (YGcfInstDrainR.DRq_cf B kQuarantineMax).
Proof.
intros B TB IOK Hp HIOK EAP RLE DF DV CDG.
exact (rchunk_ok_rh_cf B TB IOK Hp HIOK EAP RLE TB YGcfInstDrainR.nmaxd_ok_cf YGcfInstDrainR.lmaxd_ok_cf
  YGcfInstDrainR.rmaxd_ok_cf (DS_cf B) DF DV CDG).
Qed.
End d.
