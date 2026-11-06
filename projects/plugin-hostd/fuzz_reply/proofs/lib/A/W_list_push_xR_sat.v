(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v; 37 of its 103 lines of code are new or changed and 1525 lines of the source are left out. *)
(* Satisfiability at the real image A of the R contract texts (W_contract_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_list_push.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State
Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15
YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06
YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep
W_contract W_frame W_list_push_tail W_lp_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

(* pb_list_push_xR_sat: lp_spec_xR at R := wle' SEGS RZ_cf, from W_list_push.pb_list_push_x by lp_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_list_push_x's own (W_list_push.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat1.
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
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX.
Hypothesis TAIL : lp_tail_stmt_x B PST ARx MT RP G.
Theorem pb_list_push_xR_sat :
  lp_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G MMAX W_list_push.A_list_pushP.
Proof.
apply lp_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_list_push.pb_list_push_x; eassumption.
Qed.
End sat1.

(* pb_list_push_g_xR_sat: lp_spec_g_xR at R := wle' SEGS RZ_cf, from W_list_push.pb_list_push_g_x by lp_spec_g_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_list_push_g_x's own (W_list_push.v, Sections a / b / g), unchanged; their comments are left out. *)
Section sat2.
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
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xd0] CTX_M.
Theorem pb_list_push_g_xR_sat :
  lp_spec_g_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_g_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_list_push.pb_list_push_g_x; eassumption.
Qed.
End sat2.
