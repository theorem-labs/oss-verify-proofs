(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's check_no_loss,
   a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), after
   lib/A/W_check_no_loss.v (sha256 8817affe2a55; internal record) and lib/B/W_check_bounded.v (at
   7e062bb9b9c), with the image-B facts (frame, registers, trap sites) of the old-frame walk lib/B/Prog/check_no_loss.v
   (a working branch 0fafbcda68f). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_check_no_loss.v; 15 of its 80 lines of code are new or changed and 4909 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR_g6.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_check_no_loss.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_tbl W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_img W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_cnl_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_check_no_loss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_check_no_loss_xR_sat: cnl_spec_xR at R := wle' SEGS RZ_cf, from W_check_no_loss.pb_check_no_loss_x by cnl_spec_xR_of_x and YA0nH.wle_wle'. The
   Section hypotheses are pb_check_no_loss_x's own (W_check_no_loss.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat_pb_check_no_loss_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Variable MMAX : Z.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LDROP : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_x B PST ARx MT RP G0 (BASE + AF_fr_list_drop).
Hypothesis HRO : rom_out SEGS B [(VAL A_g_s, 384)].
Theorem pb_check_no_loss_xR_sat :
  cnl_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G MMAX (BASE + AF_fr_check_no_loss).
Proof.
apply cnl_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_check_no_loss.pb_check_no_loss_x; eassumption.
Qed.
End sat_pb_check_no_loss_x.
