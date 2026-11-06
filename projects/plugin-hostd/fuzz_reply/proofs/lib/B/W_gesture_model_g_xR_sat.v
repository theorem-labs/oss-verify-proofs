(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: the ROOM round (an internal work row), A's re-fit git diff f6bfd4d6ab5 f6038f3d481
   of lib/A/W_gesture_model_g.v applied by three-way merge onto lane W4's ARx text (a working branch
   0d0105eaf4d) at B's names: pb_gesture_model_g_x at RP, and Section cf: pb_gesture_model_g_cf at the B top's ARX
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v Definition ARX, word for word), its literal shadow facts by
   lib/B/TopxImageB.v tfib_shp_x. The AR statements (Section r) are W4's, unchanged. *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (asan-ubsan, entry 0x86048) twin of lib/A/W_gesture_model_g.v.
   gesture_model at its caller's choice of globals (W_contract.v gm_spec_g), the
   composition of lane W4's three cuts with the callees' G-generic contracts:
     pb_gesture_model (W_gesture_model.v, entry to the scan loop, GMSCAN open)
     pb_gm_scan       (W_gm_scan.v, the scan loop 0x860d8, GMFOUND open)
     pb_gm_found      (W_gm_found.v, the found point 0x8611c to the return / tail calls)
   and, at the caller's G: list_find by lfind_spec_g (lane W1), list_push by lp_spec_g (lane W2), list_drop by
   W1's pb_list_drop_ro statement (W_list_drop_top.v: any G with gx_ok, gx_rt and rom_out).
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record); the template is lib/A/W_gesture_model_g.v on
   a working branch): Section c proves pb_gesture_model_g_x : gm_spec_g_x over a generic allocator relation ARx
   from the three cuts' _x theorems (pb_gesture_model_x, pb_gm_scan_x, pb_gm_found_x) and the callees' _g_x twins;
   Section r re-derives pb_gesture_model_g, statement unchanged, at ARx := W_journal_x.ARi0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_gesture_model_g.v; 15 of its 71 lines of code are new or changed and 134 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR_g6.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_gesture_model_g.v), so each hypothesis reads as there. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_gm_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_gesture_model W_gm_scan W_gm_found.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_gesture_model_g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_gesture_model_g_xR_sat: gm_spec_g_xR at R := wle' SEGS RZ_cf, from W_gesture_model_g.pb_gesture_model_g_x by gm_spec_g_xR_of_x and YA0nH.wle_wle'. The
   Section hypotheses are pb_gesture_model_g_x's own (W_gesture_model_g.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat_pb_gesture_model_g_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
Hypothesis LFIND_G : lfind_spec_g_x B PST ARx (BASE + AF_fr_list_find).
Hypothesis LPUSH_G : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
Theorem pb_gesture_model_g_xR_sat :
  gm_spec_g_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX (BASE + AF_fr_gesture_model).
Proof.
apply gm_spec_g_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_gesture_model_g.pb_gesture_model_g_x; eassumption.
Qed.
End sat_pb_gesture_model_g_x.
