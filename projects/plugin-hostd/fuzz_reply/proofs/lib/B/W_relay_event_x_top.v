(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, row G-BRE): the B top_x obligation RE_x
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v), word for word, as a corollary of lib/B/W_relay_event_x.v's
   pb_relay_event_x at the B top's instance: PB_fr, TfibB, PST = [], ARX, et_GRE, fr_RG.  Its Section hypotheses are
   the callee contracts the walk composes and the B top does not prove: send_line (SL_x) and strlen (ASTRLEN_x),
   with the mutex entries ALOCK / AUNLOCK (B top_x hypotheses already).  Everything else is discharged here: the laws
   (top_x's ARX_laws / ARX_hp0, W_bx_inst_x.bxi_BLK_cf), gx_ok at et_GRE (top_x's GX_ok with
   W_LLVMFuzzerTestOneInput_G's c_HGlock / c_HG_SL), and the placement facts by computation at fr_globals_b. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x W_sites_x.
(* the walk, the top's instance (ARX and its laws, GX_ok, top_apart_ok, top_HEV), event's G and a12's cf
   witnesses: Require only, cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_relay_event_x W_LLVMFuzzerTestOneInput_top_x W_LLVMFuzzerTestOneInput_arm_event W_bx_inst_x.
(* route R: send_line's contract at R (W_send_line_xR.v), and SRrG / wle' (YA0nH) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_xR W_contract_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section top.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation ARX := W_LLVMFuzzerTestOneInput_top_x.ARX.
Variable MT : ameter_ops.
Variable RP : roomp.
(* send_line's contract at the instance: no proof at ARX yet (row G-BSL) *)
Hypothesis SL_x : sl_spec_x (PI := PB_fr) TfibB [] ARX MT RP CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_send_line).
(* the mutex entries: the B top's own ALOCK / AUNLOCK *)
Hypothesis ALOCK : alock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_unlock).
(* strlen's interceptor at the instance: row G-BRT *)
Hypothesis ASTRLEN_x : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen).
(* route R: RE_x at a world relation R (the cf instance takes R := wle' segs RZ_cf), from the walk's R form
   W_relay_event_x.pb_relay_event_xR with send_line's contract at R; at R := wle it is pb_relay_event_x_top below *)
Section topR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Hypothesis SL_xR : sl_spec_xR (PI := PB_fr) TfibB [] ARX R MT RP CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_send_line).
Theorem pb_relay_event_x_topR : re_spec_xR (PI := PB_fr) TfibB [] ARX R MT RP CfParamsReply.fr_MMAX
  (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG (BASE + AF_fr_relay_event).
Proof.
  refine (W_relay_event_x.pb_relay_event_xR (PI := PB_fr) TfibB [] ARX MT RP CfParamsReply.fr_MMAX
    (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG
    W_LLVMFuzzerTestOneInput_top_x.ARX_laws W_LLVMFuzzerTestOneInput_top_x.ARX_hp0
    (* the block bound at ARX (ARcf, Hp = [], arodata_ok_cf): W_bx_inst_x.bxi_BLK_cf on the first two conjuncts *)
    (fun ly S Hp W mem md p n H => W_bx_inst_x.bxi_BLK_cf (cp := CfParams_reply) TfibB
       (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (conj (proj1 H) (proj1 (proj2 H))))
    _ ALOCK AUNLOCK ASTRLEN_x _ _ _ _ _ _ _ R R_refl R_trans WLE_R SL_xR).
  - (* HG: et_GRE = (g_lock, 12) :: G_SL, both inside G_fr_c *)
    intros a Ha. apply W_LLVMFuzzerTestOneInput_top_x.GX_ok.
    unfold W_LLVMFuzzerTestOneInput_arm_event.et_GRE, inG in Ha. apply Exists_cons in Ha as [Ha | Ha].
    + exact (c_HGlock TfibB a Ha).
    + exact (c_HG_SL TfibB a Ha).
  - (* HV3: g_lock is object 3 *) vm_compute. reflexivity.
  - (* HLA *) vm_compute. reflexivity.
  - (* HLD: g_lock is apart from send_line's G *) intros a Ha Hg.
    exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok (rg_lock fr_RG) 12 (G_SL TfibB fr_RG)
      ltac:(vm_compute; reflexivity) a Hg Ha).
  - (* HLRW *) intros a Ha Hr.
    exact (c_rom_apart TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a Hr (c_HGlock TfibB a Ha)).
  - (* HAOD *) intros a Ha. cbn [fr_RG fr_globals_b rg_lock rg_send_max rg_client rg_send_dead] in *. lia.
  - (* HAO3 *) cbn [fr_RG fr_globals_b rg_send_max rg_client rg_send_dead]. lia.
  - (* HLPST: PST = [] *) intros a _ H. inversion H.
Qed.
End topR.
Theorem pb_relay_event_x_top : re_spec_x (PI := PB_fr) TfibB [] ARX MT RP CfParamsReply.fr_MMAX
  (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG (BASE + AF_fr_relay_event).
Proof.
  exact (pb_relay_event_x_topR (@wle segs) (@wle_refl segs) (@wle_trans segs) (fun _ _ H => H) SL_x).
Qed.
End top.
Print Assumptions pb_relay_event_x_top.
