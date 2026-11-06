(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: gestures_end CLOSED on image A (lane W4): pb_gestures_end (W_gestures_end.v,
   the entry to the two frozen cut points of W_gse_cut.v) with its two cut hypotheses discharged by a Theorem Labs lane's
   pb_gse_loop (W_gse_loop.v, the loop head 0x825c0) and pb_gse_tail (W_gse_tail.v, 0x82638 -> ret).  What is left
   is the callee contract GE (pb_gesture_end, W_gesture_end.v), the allocator's free rules, the instance laws and
   the image facts on G_SL and the " end\0" literal.  The composition is made over any allocator relation ARx
   (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)) from the three pieces' generic forms, pb_gestures_end_closed_x;
   pb_gestures_end_closed, the AR statement, is re-derived from it at ARi0 (Section cAR). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_gestures_end_top.v; 24 of its 72 lines of code are new or changed and 91 lines of the source are left out. *)
(* Satisfiability at the real image A of the R contract texts (W_contract_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_gestures_end_top.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State
Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15
YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06
YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq
YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract W_rep
W_journal W_gse_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gestures_end W_gse_loop W_gse_tail.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gestures_end_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

(* pb_gestures_end_closed_xR_sat: gse_spec_xR at R := wle' SEGS RZ_cf, from W_gestures_end_top.pb_gestures_end_closed_x by gse_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_gestures_end_closed_x's own (W_gestures_end_top.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0xbc] CTX_AFREE.
Hypothesis HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0xfc] CTX_AFREE.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) PST.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Theorem pb_gestures_end_closed_xR_sat :
  gse_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX RG W_gestures_end.A_gestures_endP.
Proof.
apply gse_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_gestures_end_top.pb_gestures_end_closed_x; eassumption.
Qed.
End sat.
