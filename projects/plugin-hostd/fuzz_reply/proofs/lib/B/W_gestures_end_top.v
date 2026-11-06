(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: gestures_end CLOSED on image B (asan-ubsan, entry 0x82618; lane W4), the twin of
   lib/A/W_gestures_end_top.v: pb_gestures_end (W_gestures_end.v,
   the entry to the two frozen cut points of W_gse_cut.v) with its two cut hypotheses discharged by
   pb_gse_loop (W_gse_loop.v, the loop head 0x82694) and pb_gse_tail (W_gse_tail.v, 0x82754 -> ret).  What is left
   is the callee contract GE (pb_gesture_end, W_gesture_end.v), the allocator's free rules, the instance laws and
   the image facts on G_SL and the " end\0" literal.  The composition is made over any allocator relation ARx
   (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)) from the three pieces' generic forms, pb_gestures_end_closed_x;
   pb_gestures_end_closed, the AR statement, is re-derived from it at ARi0 (Section cAR). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_gse_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_gestures_end W_gse_loop W_gse_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- THE GENERIC COMPOSITION: the Section hypotheses beyond the AR one's are PST / ARx / hl / LAWS (the generic
   relation), HP0, IMGC / BLKN (W_kit_x.v Section g), and the two facts on the program statics PST the loop needs
   (PSTR, HEND5P: W_gse_loop.v); GE is its generic form; the free rules are their generic caller-context forms over
   one context list CTX_AFREE, with gestures_end's two free sites HCTX_gse_loop / HCTX_gse_tail. ---- *)
Section c.
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
(* the free rules in their caller-context form (a Theorem Labs lane's 21:20Z ruling), one context list per allocator entry;
   gestures_end's two free sites as closed singletons of their return addresses (ATopKeeper's K0 table CTX_AFREE,
   lib/B/YCk0.v): the loop's free at 0x82728 (ra 0x8272c = gestures_end + 0x114) and the tail's free at 0x82764
   (ra 0x82768 = gestures_end + 0x150) *)
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0x114] CTX_AFREE.
Hypothesis HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0x150] CTX_AFREE.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* " end\0" lies in the image (true at every placement: it is .rodata).  The zero-shadow claim that stood here before
   is FALSE at the instance (partial granule: shadow byte 5 at 0x7fffc1e0, W3's measurement) and was never needed. *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* the program statics PST hold no ROM byte and no byte of " end\0" (both .rodata; at PST := [] trivially) *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) PST.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the composition at a world relation R, from the three pieces' R twins
   (W_gse_tail.pb_gse_tail_xR, W_gse_loop.pb_gse_loop_xR, W_gestures_end.pb_gestures_end_xR).  gse_spec_x ->
   W_contract_xR.gse_spec_xR (R right after ARx); GE -> GE_R : ge_spec_xR (a Theorem Labs lane's B lane 1 proves it in
   W_gesture_end.v); the free rules -> their R forms (afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX_AFREE R)
   with RO_ARx for their call-boundary premise RO.  The strict pb_gestures_end_closed_x after End wR is this at
   R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GE_R : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :92 pb_gestures_end_closed_x *)
Theorem pb_gestures_end_closed_xR : gse_spec_xR B PST ARx R MT RP MMAX RG W_gestures_end.A_gestures_endP.
Proof.
assert (TAIL : gse_tail_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_tail))
  by (eapply W_gse_tail.pb_gse_tail_xR with (CTX_AFREE := CTX_AFREE) (RO := RO); eassumption).
assert (LOOP : gse_loop_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_loop))
  by (eapply W_gse_loop.pb_gse_loop_xR with (CTX_AFREE := CTX_AFREE) (RO := RO); eassumption).
eapply W_gestures_end.pb_gestures_end_xR; eassumption.
Qed.
End wR.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): each R premise at wle is the
   strict hypothesis of the same name (the free / realloc rules by W_journal_x.v's *_xR_of_x, RO / HA := True), and
   the three laws hold for wle *)
#[local] Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Theorem pb_gestures_end_closed_x : gse_spec_x B PST ARx MT RP MMAX RG W_gestures_end.A_gestures_endP.
Proof using fx rc SK PI B PST ARx hl MT RP MMAX RG LAWS HP0 TL HG MTL GE CTX_AFREE AFREE AFREEN HCTX_gse_loop HCTX_gse_tail HROMO HOUTG HEND5I HEND5G PSTR HEND5P IMGC BLKN.
eapply (pb_gestures_end_closed_xR (@wle SEGS)) with (RO := fun _ => True);
  first [ wle_inst | (intros; exact I) | (apply afree_cf_rule_c_xR_of_x; exact AFREE) | (apply afree_null_cf_rule_c_xR_of_x; exact AFREEN) ].
Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_gestures_end_closed's statement is the
   AR composition's, byte-identical, now a corollary of pb_gestures_end_closed_x at ARx := ARi0 (cgif's AR with the
   head set empty), PST := [].  Its Section takes LX0 (the laws at ARi0) in place of LAWS: the instance builds it once,
   W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridges: W_contract_x.gse_spec_x_AR0 (conclusion),
   ge_spec_x_of_AR0 (GE).  The free rules stay AR rules here; their caller-context forms at
   CTX := [[gestures_end + 0x114]; [gestures_end + 0x150]] (the two free sites of gestures_end) come from
   W_journal.afree_cf_rule_c_weak / afree_null_cf_rule_c_weak and go to ARi0 through
   W_journal_x.afree_cf_rule_c_x_of_AR0 / afree_null_cf_rule_c_x_of_AR0.  HP0 at ARi0 is ARi0_hp0; IMGC / BLKN are
   W_kit_x.AR_imgc / AR_blkn; PSTR and HEND5P hold at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis GE : ge_spec B MT MMAX RG (BASE + AF_fr_gesture_end).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AFREEN : afree_null_cf_rule SEGS B MT.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* " end\0" lies in the image (true at every placement: it is .rodata).  The zero-shadow claim that stood here before
   is FALSE at the instance (partial granule: shadow byte 5 at 0x7fffc1e0, W3's measurement) and was never needed. *)
Hypothesis HEND5I : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img SEGS a.
(* HEND5G holds for EXACTLY [VAL A_lit_end5, VAL A_lit_end5 + 5) = [0x20f00, 0x20f05) on both images and MUST NOT BE
   WIDENED: its `~ owned_static` clause is TRUE (StartupTrace's tfib_lit_end5_not_owned_static, a working branch
   5fab70f4113; ZeroGlobals and W1Verify measured the same rows) only because owned_static's rows (0x20ee1, 0x1f) and
   (0x20f05, 0x1b) - the literal's two redzones - end and start exactly at its edges.  One byte more on either side,
   or rounding the range to 8 bytes or an aligned word, makes that clause FALSE. *)
Hypothesis HEND5G : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
  ~ inG (G_SL B RG) a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem pb_gestures_end_closed : gse_spec B MT MMAX RG W_gestures_end.A_gestures_endP.
Proof.
apply gse_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
assert (HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) (@nil (Z * Z)))
  by (intros a _ H; inversion H).
pose proof (ge_spec_x_of_AR0 B MT MMAX RG _ GE) as GE_X.
pose (CTXL := [[BASE + AF_fr_gestures_end + 0x114]; [BASE + AF_fr_gestures_end + 0x150]]).
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_cf_rule_c_weak SEGS B MT CTXL AFREE)) as AFREE_X.
pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_null_cf_rule_c_weak SEGS B MT CTXL AFREEN)) as AFREEN_X.
assert (HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0x114] CTXL) by (unfold CTXL; cbn [In]; left; reflexivity).
assert (HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0x150] CTXL) by (unfold CTXL; cbn [In]; right; left; reflexivity).
eapply (pb_gestures_end_closed_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG) with (CTX_AFREE := CTXL); eassumption.
Qed.
End cAR.
End b.
End a.
