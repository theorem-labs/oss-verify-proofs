(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's op_add, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_op_add.v; 13 of its 101 lines of code are new or changed and 2660 lines of the source are left out. *)
(* AR-side helper lemmas of op_add's call (oa_call_keep / _blk / _hi, oa_writable_img), as they stood in W2's
   lib/A/W_op_add.v at a working branch 9941927fa02 (W2's text, AR form, lines 223-271 and 580-593): W2 has since
   kept only the ARx forms in W_op_add.v; the AR ARM_add walk (W_LLVMFuzzerTestOneInput_add.v) still needs these, so
   they are carried here VERBATIM (same names, same proofs) in their own module, Required without Import so the names
   do not clash with W2's.  Delete this file when ARM_add's AR proof is retired in favour of lf_arm_add_x. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract
W_frame W_op_add_src.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma oa_call_keep : forall G' STK sp0 FP ly0 S0 (W0 : world SEGS) m0 md0 ly1 S1 (W1 : world SEGS) m1 md1 k,
ajournal_gx SEGS B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
forall a, in_img SEGS a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Him Hno He ltac:(apply fp_spares_closed; exact Hsk)).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* the bytes of a block live before and after the call, outside the callee's FP *)
Lemma oa_call_keep_blk : forall G' STK sp0 FP ly0 S0 (W0 : world SEGS) m0 md0 ly1 S1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx SEGS B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
~ inFP FP (p + j) -> aview SEGS (w_H W1) m1 (p + j) = aview SEGS (w_H W0) m0 (p + j).
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n j H0 H1 Hj Hfp).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
apply (aview_gagree SEGS G' (w_H W0) m0 memS (p + j) HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
(* and what it keeps above alloc_ceiling: every byte outside its own window (the caller's frame is there,
   so the caller's stack region survives the call) *)
Lemma oa_call_keep_hi : forall G' STK sp0 FP ly0 S0 (W0 : world SEGS) m0 md0 ly1 S1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx SEGS B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
Lemma oa_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
End c.
End b.
End a.
