(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 440 of its 488 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_ctrl_build_asG.v, with its module paths and module names changed; 28 of its 44 lines of code are new or changed and 472 lines of the source are left out. *)
(* lib/A/Prog/reac_ctrl_build_asTop.v -- a Theorem Labs lane, 2026-10-29.
   proves no function (kind: composition). The build_as glue pb_reac_ctrl_build_as_on with its seven image binders
   discharged by lib/A/Prog/BuildAsImg.v at a Theorem Labs lane's list GLOBS := A.ACtlGlobs.ctrl_globs_A: the fit check of the
   image facts against the glue, and the form the image-A top cites for TBUILD (GLOBS_A := ctrl_globs_A). HGM is
   a Theorem Labs lane's ACtlGlobs.ctrl_globs_A_marked_B B TSYMS (a Theorem Labs lane N1, 18:22Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m ACtlGlobs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlImg CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block C_ctrl_lay_block C_ctrl_emit_as C_reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require BuildAsImg reac_ctrl_build_asG.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).

Corollary pb_reac_ctrl_build_as_top (B : asyms) (TSYMS : AF0m.CtrlTSyms B) (RLO RHI : Z)
  (TL : PALib (PI := PI_ctrl) B) (LAWS : AR_laws SEGS B) (ML : model_laws (as_universe B))
  (RELRO_IMG : forall x, RLO <= x < RHI -> in_img SEGS x)
  (TEMIT : tctrl_emit_as_spec (SK := SK) B ACtlGlobs.ctrl_globs_A (BASE + AF_ctrl_emit_as) RLO RHI)
  (HIMGSH : img_shadow_vis SEGS B) :
  treac_ctrl_build_as_spec (SK := SK) B ACtlGlobs.ctrl_globs_A (BASE + AF_reac_ctrl_build_as) RLO RHI.
Proof.
  pose proof (reac_ctrl_build_asG.pb_reac_ctrl_build_as_on B TSYMS ACtlGlobs.ctrl_globs_A RLO RHI) as P.
  unfold pb_reac_ctrl_build_as_stmt in P.
  exact (P TL LAWS ML RELRO_IMG TEMIT HIMGSH (ACtlGlobs.ctrl_globs_A_marked_B B TSYMS) BuildAsImg.ba_img_sw_glob BuildAsImg.ba_img_sw_al
           (BuildAsImg.ba_img_sw_e B TSYMS RLO RHI) BuildAsImg.ba_img_cat_glob BuildAsImg.ba_img_cat_al
           BuildAsImg.ba_img_sw_rng BuildAsImg.ba_img_cat_rng).
Qed.
End b.
