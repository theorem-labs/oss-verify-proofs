(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths and module names changed; 694 of its 806 lines of code are new or changed and 977 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c.v at cb9cdc023f20; for the same unit's
   image B (fuzz_rate.asan-ubsan): RtPgSegB's cuts D and J, image B's registers (cursor s2, left s6, kind byte's address
   s10, t1, a6) and real-frame cells (R+0x150, R+0x130, R+0x0, and R+0x158 = &pp->len, which the tails read back into
   s2), the pod e62 at F + 0x210, the class-4 frame for locals (1024 bytes, 128 shadow bytes, 88-byte pattern), the
   real frame 0x220, image B's first write ranges hi_w1; the heads and tails are lib/AU/RtPgW6cBaseB.v's statements,
   Section hypotheses until the end, where lib/AU/RtPgW6c6B.v, RtPgW6c7B.v, RtPgW6c8B.v and RtPgW6cTailB.v discharge
   them; A's unused helpers w6c_getrZ, w6c_fsub and w6c_present_hdr are dropped and RtPgW6cTail's w6c_val_kept is
   restated here. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cB.v, with its module paths and module names changed; 213 of its 427 lines of code are new or changed and 592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c.v at cb9cdc023f20; for the same unit's
   image B (fuzz_rate.asan-ubsan): RtPgSegB's cuts D and J, image B's registers (cursor s2, left s6, kind byte's address
   s10, t1, a6) and real-frame cells (R+0x150, R+0x130, R+0x0, and R+0x158 = &pp->len, which the tails read back into
   s2), the pod e62 at F + 0x210, the class-4 frame for locals (1024 bytes, 128 shadow bytes, 88-byte pattern), the
   real frame 0x220, image B's first write ranges hi_w1; the heads and tails are lib/AU/RtPgW6cBaseB.v's statements,
   Section hypotheses until the end, where lib/AU/RtPgW6c6B.v, RtPgW6c7B.v, RtPgW6c8B.v and RtPgW6cTailB.v discharge
   them; A's unused helpers w6c_getrZ, w6c_fsub and w6c_present_hdr are dropped and RtPgW6cTail's w6c_val_kept is
   restated here. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cB.v at 05426fac6916 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed; the cuts are lib/AU/RPgSeg.v's rs_cut_D
   and rs_cut_J; the case entry's facts come from lib/AU/RPgEntBCut.v's ebb_D_facts and ebb_D_input (with the
   input's distance from role B's two other first write ranges, R + 0x10 .. 0x40 and R + 0x178 .. 0x198, from the
   segment start's rs_in) and lib/AU/RPgW6aKit.v's w6k_pre_geom, the tables' shadow from rl_seg_pre's registered
   globals (role_B_globs) by ebb_ra_kept; the join is ebb_J_of (registers outside lib/AU/RPgW6bBase.v's w6bb_clob,
   bytes outside its w6bb_wr, w6bb_J_R); role B's cells are R+0x158, R+0x110, R+0x10, R+0x130 and R+0x140 (the tails
   read pp and &pp->len from the last two) and the real frame is 0x200 bytes; the cut-free helpers move to
   lib/AU/RPgW6cKit.v and the closing theorem to lib/AU/RPgW6c.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x80020), lib/AU/RPgSeg.v's rs_piece_W6c_stmt: from the cut D at the switch entry of
   kind % 10 = 6 (0x811d8), 7 (0x81050) or 8 (0x8122c) to the cut J 0x818d8 (pod.h:340-366), with the heads and the
   tails of lib/AU/RPgW6cBase.v as Section hypotheses. Proves no function (kind: segment lemma).

   THE CHAIN. At D (rs_cut_D) w6cb_prep reads the block statements' premises: the context (the journal, the frame
   geometry, rom_view), the registers and cells of rs_L_D, the input at the cursor, e62's 104 zeros, the two tables'
   shadow (0x21120 and 0x21140, registered globals of 16 bytes) and the cells R+0x130 = &pp->len and R+0x140 = pp.
   The case's head runs to the intrinsic's entry; w6cb_src_ok, w6cb_hdr_bytes, w6cb_fsh_T and w6cb_cell_T give its
   tail's premises; the tail ends at J in w6cb_jpost; w6cb_to_J turns that into rs_cut_J through ebb_J_of (the
   journal, the registers kept, the bytes kept, a3 = the cursor, t1 = what is left, s6 = &pp->len, a5 = pp, e62 =
   ent_mem of Model.ent_build's pod of the turn's input) and applies the continuation rs_from_J. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW6bBase RPgEntBCut RPgW6aKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW6cBase RPgW6cKit.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/AU/RPgSeg.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* a location of rs_L_D: unfold the list and find the entry *)
Ltac w6cb_inL := cbn [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app]; repeat (first [left; reflexivity | right]).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== a cut's geometry ======================================== *)
(* R's frame above the ceiling with the callees' stack below it, the frame for locals F (class 4: 1024 bytes, 128
   shadow bytes) and its shadow, and the block pp below the ceiling *)
Definition w6cb_sep (R F pp : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x200 <= 2 ^ 47 /\
4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling.

(* the frame's shadow at the head's end *)
Lemma w6cb_fsh_T : forall (W : world rsegs) memD memT R F pp,
w6cb_sep R F pp -> rl_fsh rsegs (w_H W) memD F rs_PJ ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
rl_fsh rsegs (w_H W) memT F rs_PJ.
Proof.
intros W memD memT R F pp HG HF HmT. pose proof alloc_ceiling_lt as Hc.
destruct HG as (_ & _ & G3 & G4 & G5 & G6 & G7 & _).
apply (rm_fsh_kept rsegs (w_H W) memD (w_H W) memT _ _ HF).
intros ii Hii. rewrite ebb_PJ_len in Hii.
apply HmT; [lia | unfold w6cb_hdr_wr; lia].
Qed.
(* a real-frame cell at the head's end, the value a tail reads *)
Lemma w6cb_cell_T : forall (W : world rsegs) memD memT R F pp o v,
w6cb_sep R F pp -> 0 <= o -> o + 8 <= 0x200 -> val_mem rsegs (mrestrict (w_H W) memD) (R + o) 8 v ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
val_mem rsegs (mrestrict (w_H W) memT) (R + o) 8 v.
Proof.
intros W memD memT R F pp o v HG Ho0 Ho V HmT. pose proof alloc_ceiling_lt as Hc.
destruct HG as (G1 & G2 & G3 & G4 & _).
apply (w6cb_val_kept (w_H W) memD (w_H W) memT _ 8 _ V).
intros ii Hii. change (Z.of_nat 8) with 8 in Hii.
apply HmT; [unfold T_SEG_STK, ASTACK in *; lia | unfold w6cb_hdr_wr, T_SEG_STK, ASTACK in *; lia].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== at D: the blocks' premises ======================================== *)
Lemma w6cb_prep : forall cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD,
rs_start_M01 rsegs B cx rest ->
rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd lyD SD WD regsD memD mdD ->
w6cb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  lyD SD WD memD mdD (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
w6cb_regs B regsD (e_R (x_e cx)) (rs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
w6cb_cells WD memD (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) /\
w6cb_in WD memD (e_R (x_e cx)) (e_F (x_e cx)) (rs_cur rsegs cx rest r) r /\
rm_bytes rsegs (w_H WD) memD (e_F (x_e cx) + 0x210) (zeros 104) /\
range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF W6CB_T6 16 /\
range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF W6CB_T8 16 /\
val_mem rsegs (mrestrict (w_H WD) memD) (e_R (x_e cx) + 0x140) 8 (e_pp (x_e cx)) /\
w6cb_sep (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)).
Proof.
intros cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD HST HD.
pose proof asan_consts as (Hceil & _).
pose proof (ebb_D_facts B MT cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD HST HD) as
  (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
   & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
pose proof (ebb_D_input B MT cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD HST HD) as (_ & Hc1 & Hwin).
pose proof HST as (HP & _ & _ & _ & HIN).
destruct (w6k_pre_geom rsegs B cx HP) as (_ & HRk & _).
pose proof HP as HP'. unfold rs_pre, rl_seg_pre in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hglobs & _).
cbn [hi_globs role_himg_B] in Hglobs. rewrite Forall_forall in Hglobs.
destruct HD as (HPB & HAT & _ & _ & HE0 & _ & _ & _ & _).
destruct HPB as (_ & _ & Hsr & _).
assert (AT : forall l v, In (l, v) (rs_L_D rsegs cx sh np ps cnt es rest r kd) ->
  rl_at rsegs (w_H WD) memD regsD (x_e cx) l v)
  by (intros l v Hin; exact (proj1 (Forall_forall _ _) HAT (l, v) Hin)).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (rl_fbounds (e_F (x_e cx)) HF32 HFapp) as (FB1 & FB2 & FB3 & FB4 & FB5 & _).
split.
{ (* the context *)
  split; [exact HJ|]. split; [|exact HromD].
  unfold w6cb_geo. split; [exact BR4|]. split; [exact BR5|]. split; [exact BR2|]. split; [exact HRk|].
  split; [exact Hown|]. split; [exact EF2|]. split; [exact HFapp | exact HF32]. }
split.
{ (* the registers *)
  unfold w6cb_regs.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact (AT (LReg 9) _ ltac:(w6cb_inL))|].
  split; [exact (AT (LReg 27) _ ltac:(w6cb_inL))|].
  split; [exact (AT (LReg 18) _ ltac:(w6cb_inL))|].
  split; [exact (AT (LReg 22) _ ltac:(w6cb_inL))|].
  split; [exact (AT (LReg 16) _ ltac:(w6cb_inL))|].
  split; [exact (AT (LReg 6) _ ltac:(w6cb_inL))|].
  exact (AT (LReg 20) _ ltac:(w6cb_inL)). }
split.
{ (* the cells *)
  unfold w6cb_cells.
  split; [apply (proj1 (w6cb_val_mod _ _ _)); exact (AT (LCell XR 0x158) _ ltac:(w6cb_inL))|].
  split; [apply (proj1 (w6cb_val_mod _ _ _)); exact (AT (LCell XR 0x110) _ ltac:(w6cb_inL))|].
  split; [apply (proj1 (w6cb_val_mod _ _ _)); exact (AT (LCell XR 0x10) _ ltac:(w6cb_inL))|].
  split; [apply (proj1 (w6cb_val_mod _ _ _)); exact (AT (LCell XR 0x130) _ ltac:(w6cb_inL))|].
  lia. }
split.
{ (* the input at the cursor *)
  destruct Hwin as (Hg & Hra & _ & Hc63 & Ham & Hhull & Hdis).
  destruct HIN as (Hel & _ & _ & _ & _ & _ & _ & Hdis0).
  destruct Hsr as (j & Hj & Er).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : rs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Hlr; lia).
  unfold w6cb_in.
  split; [exact Hg|]. split; [exact Hra|]. split; [exact Hhull|]. split; [exact Hc1|]. split; [exact Hc63|].
  split; [exact Ham|].
  intros a Ha. destruct (Hdis a Ha) as (D1 & D2 & D3).
  assert (Ha0 : e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx)) by (rewrite Hcur in Ha; rewrite Hel; lia).
  destruct (Hdis0 a Ha0) as (_ & D4 & _).
  pose proof (fun X => D4 (proj2 (ebb_inw (x_e cx) a) X)) as D4'.
  split; [exact D1|]. split; [intros X; apply D4'; tauto|]. split; [exact D2|].
  split; [intros X; apply D4'; tauto | exact D3]. }
split; [exact HE0|].
(* the two tables' shadow *)
assert (HT : forall t, In (t, 16) role_B_globs -> 0 <= t -> t + 16 <= kHighMemEnd ->
  range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF t 16).
{ intros t Ht Ht0 Ht1. pose proof (Hglobs (t, 16) Ht) as HG. cbn [fst snd] in HG.
  eapply ebb_ra_kept; [exact HG | exact Hfsh0 | exact Ht0 | exact Ht1 | exact KB]. }
split; [apply HT; [unfold role_B_globs; repeat (first [left; reflexivity | right]) | unfold W6CB_T6; lia
  | unfold W6CB_T6, kHighMemEnd; lia]|].
split; [apply HT; [unfold role_B_globs; repeat (first [left; reflexivity | right]) | unfold W6CB_T8; lia
  | unfold W6CB_T8, kHighMemEnd; lia]|].
split; [apply (proj1 (w6cb_val_mod _ _ _)); exact (AT (LCell XR 0x140) _ ltac:(w6cb_inL))|].
unfold w6cb_sep. lia.
Qed.

(* ======================================== at J: the cut ======================================== *)
Lemma w6cb_to_J : forall cx POST rest i k sh np ps cnt es rr r kd lyD SD WD regsD memD mdD regsJ memJ mdJ ed r',
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd lyD SD WD regsD memD mdD ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  lyD SD WD memJ mdJ (x_k cx) ->
same_io mdD mdJ ->
(forall q, In q w6cb_keep -> getr regsJ q = getr regsD q) ->
getr regsJ 22 = w64 (e_pp (x_e cx) + 0x4000) -> getr regsJ 15 = w64 (e_pp (x_e cx)) ->
getr regsJ 13 = w64 (rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length r')) ->
getr regsJ 6 = w64 (Z.of_nat (length r')) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 ~ (e_F (x_e cx) + 0x210 <= a < e_F (x_e cx) + 0x278) ->
 aview rsegs (w_H WD) memJ a = aview rsegs (w_H WD) memD a) ->
rm_bytes rsegs (w_H WD) memJ (e_F (x_e cx) + 0x210) (ent_mem ed) ->
(ed, r') = ent_build rr ->
SRr rsegs WD (cfg_at rsegs W6CB_J regsJ memJ mdJ) POST.
Proof using MTL.
intros cx POST rest i k sh np ps cnt es rr r kd lyD SD WD regsD memD mdD regsJ memJ mdJ ed r'
  Hst HJ Hlp Hle HD HJJ HioJ HKR J22 J15 J13 J6 HMJ HEJ Hed.
apply (HJ lyD SD WD regsJ memJ mdJ sh np ps cnt es rr (snd (ent_build rr)) (fst (ent_build rr)) Hlp Hle).
apply (ebb_J_of B MT MTL cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD lyD SD WD regsJ memJ mdJ Hst HD HJJ).
- intros rg H0 Hn. apply HKR. exact (w6cb_keep_of_clob rg H0 Hn).
- reflexivity.
- apply Permutation_refl.
- exact HioJ.
- exact (mle_start MT SD MTL).
- intros a Ha Hn. apply HMJ; [exact Ha | |]; intros X; apply Hn; unfold w6bb_wr.
  + left. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  + right; right; right. exact X.
- unfold w6bb_J_R. rewrite <- Hed. cbn [fst snd].
  split; [exact J22|]. split; [exact J15|]. split; [exact J13|]. split; [exact J6 | exact HEJ].
Qed.

(* ======================================== the three cases ======================================== *)
Section h.
Hypothesis H6 : w6cb_h6_stmt B.
Hypothesis H7 : w6cb_h7_stmt B.
Hypothesis H8 : w6cb_h8_stmt B.
Hypothesis HCPY : w6cb_tail_cpy_stmt B.
Hypothesis HSET : w6cb_tail_set_stmt B.

Lemma w6cb_case6 : forall cx POST rest i k kd, kd mod 10 = 6 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using MTL H6 HCPY.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6cb_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & HT6 & _ & HPP & HG).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HCTX as (HJD & HGEO & _).
pose proof HGEO as (_ & _ & _ & _ & _ & _ & HFapp & _).
pose proof HCELLS as (_ & _ & _ & _ & HPP0 & HPP1).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6CB_D6 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D27 & D18 & D22 & D16 & D6 & D20).
eapply SRr_bind; [exact (H6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ HT6)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T22 & T24 & T20 & Vty & Vsz).
pose proof (w6cb_cell_T WD memD memT _ _ _ 0x140 _ HG ltac:(lia) ltac:(lia) HPP HmT) as HPPT.
pose proof (w6cb_sz6_rng (w6cb_ty6 (fst (fuzz_u8 r)))) as Hsz.
set (sz := w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r)))) in *.
set (ty := w6cb_ty6 (fst (fuzz_u8 r))) in *.
assert (Er1 : snd (fuzz_u8 r) = skipn 1 r) by apply w6cb_u8_rest.
rewrite Er1 in *.
assert (Hl1 : Z.of_nat (length (skipn 1 r)) = Z.of_nat (length r) - Z.of_nat (Nat.min 1 (length r)))
  by (rewrite length_skipn; lia).
destruct (w6cb_src_ok WD memD memT _ _ (rs_cur rsegs cx rest r) r 1 (Z.to_nat sz) HIN HFapp HmT)
  as (Sb & Sra & Shl & Sam & S0 & S63 & Sdis).
set (bs := firstn (Z.to_nat sz) (skipn 1 r)) in *.
assert (Hbs : Z.of_nat (length bs) = Z.min sz (Z.of_nat (length (skipn 1 r)))) by (subst bs; rewrite length_firstn; lia).
assert (Esrc : rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length (skipn 1 r)) =
  rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r))) by lia.
rewrite Esrc in T11, T24.
eapply SRr_bind.
{ apply (HCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    (x_k cx) lyD SD WD memT mdT regsT (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r))) bs
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r)) + Z.min sz (Z.of_nat (length (skipn 1 r))))
    (Z.of_nat (length (skipn 1 r)) - Z.min sz (Z.of_nat (length (skipn 1 r))))
    (e_pp (x_e cx)) HJT HGEO T1).
  - w6cb_kept HkT. exact D2.
  - w6cb_kept HkT. exact D3.
  - w6cb_kept HkT. exact D4.
  - w6cb_kept HkT. exact D9.
  - exact T10.
  - exact T11.
  - rewrite Hbs. exact T12.
  - exact T22.
  - exact T24.
  - exact T20.
  - subst bs. rewrite length_firstn. lia.
  - lia.
  - apply (w6cb_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6cb_hdr_wr; lia].
  - exact Sb.
  - exact Sra.
  - exact Shl.
  - exact Sam.
  - exact S0.
  - exact S63.
  - exact Sdis.
  - exact (w6cb_fsh_T WD memD memT _ _ _ HG HFSH HmT).
  - exact HPPT.
  - exact HPP0.
  - exact HPP1. }
intros WJ cJ _ HPJ.
destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J6 & J13 & J22 & J15 & HmJ & HEJ).
subst WJ.
eapply (w6cb_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ (skipn (Z.to_nat sz) (skipn 1 r)) Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6cb_keep_clob q Hq) as (Hq0 & Hq1 & _). exact (HkT q Hq0 Hq1).
- exact J22.
- exact J15.
- rewrite J13. f_equal. rewrite !length_skipn. lia.
- rewrite J6. f_equal. rewrite !length_skipn. lia.
- exact (w6cb_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6cb_ent6 b r Hkd). rewrite Er1. reflexivity.
Qed.

Lemma w6cb_case7 : forall cx POST rest i k kd, kd mod 10 = 7 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using MTL H7 HCPY.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6cb_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & _ & _ & HPP & HG).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HCTX as (HJD & HGEO & _).
pose proof HGEO as (_ & _ & _ & _ & _ & _ & HFapp & _).
pose proof HCELLS as (_ & _ & _ & _ & HPP0 & HPP1).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6CB_D7 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D27 & D18 & D22 & D16 & D6 & D20).
eapply SRr_bind; [exact (H7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T22 & T24 & T20 & Vty & Vsz).
pose proof (w6cb_cell_T WD memD memT _ _ _ 0x140 _ HG ltac:(lia) ltac:(lia) HPP HmT) as HPPT.
assert (Er2 : snd (fuzz_u8 (snd (fuzz_u8 r))) = skipn 2 r)
  by (rewrite !w6cb_u8_rest, skipn_skipn; reflexivity).
assert (Hsz : 0 <= fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12 < 12) by (apply Z.mod_pos_bound; lia).
set (sz := fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12) in *.
set (ty := fst (fuzz_u8 r) mod 21) in *.
rewrite Er2 in *.
destruct (w6cb_src_ok WD memD memT _ _ (rs_cur rsegs cx rest r) r 2 (Z.to_nat sz) HIN HFapp HmT)
  as (Sb & Sra & Shl & Sam & S0 & S63 & Sdis).
set (bs := firstn (Z.to_nat sz) (skipn 2 r)) in *.
assert (Hbs : Z.of_nat (length bs) = Z.min sz (Z.of_nat (length (skipn 2 r)))) by (subst bs; rewrite length_firstn; lia).
assert (Esrc : rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length (skipn 2 r)) =
  rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r))) by (rewrite length_skipn; lia).
rewrite Esrc in T11, T24.
eapply SRr_bind.
{ apply (HCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    (x_k cx) lyD SD WD memT mdT regsT (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r))) bs
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r)) + Z.min sz (Z.of_nat (length (skipn 2 r))))
    (Z.of_nat (length (skipn 2 r)) - Z.min sz (Z.of_nat (length (skipn 2 r))))
    (e_pp (x_e cx)) HJT HGEO T1).
  - w6cb_kept HkT. exact D2.
  - w6cb_kept HkT. exact D3.
  - w6cb_kept HkT. exact D4.
  - w6cb_kept HkT. exact D9.
  - exact T10.
  - exact T11.
  - rewrite Hbs. exact T12.
  - exact T22.
  - exact T24.
  - exact T20.
  - subst bs. rewrite length_firstn. lia.
  - lia.
  - apply (w6cb_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6cb_hdr_wr; lia].
  - exact Sb.
  - exact Sra.
  - exact Shl.
  - exact Sam.
  - exact S0.
  - exact S63.
  - exact Sdis.
  - exact (w6cb_fsh_T WD memD memT _ _ _ HG HFSH HmT).
  - exact HPPT.
  - exact HPP0.
  - exact HPP1. }
intros WJ cJ _ HPJ.
destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J6 & J13 & J22 & J15 & HmJ & HEJ).
subst WJ.
eapply (w6cb_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ (skipn (Z.to_nat sz) (skipn 2 r)) Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6cb_keep_clob q Hq) as (Hq0 & Hq1 & _). exact (HkT q Hq0 Hq1).
- exact J22.
- exact J15.
- rewrite J13. f_equal. rewrite !length_skipn. lia.
- rewrite J6. f_equal. rewrite !length_skipn. lia.
- exact (w6cb_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6cb_ent7 b r Hkd). rewrite Er2. reflexivity.
Qed.

Lemma w6cb_case8 : forall cx POST rest i k kd, kd mod 10 = 8 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using MTL H8 HSET.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6cb_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & _ & HT8 & HPP & HG).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HCTX as (HJD & HGEO & _).
pose proof HCELLS as (_ & _ & _ & HPPL & HPP0 & HPP1).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6CB_D8 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D27 & D18 & D22 & D16 & D6 & D20).
eapply SRr_bind; [exact (H8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ HT8)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T18 & T22 & Vty & Vsz).
pose proof (w6cb_cell_T WD memD memT _ _ _ 0x140 _ HG ltac:(lia) ltac:(lia) HPP HmT) as HPPT.
pose proof (w6cb_cell_T WD memD memT _ _ _ 0x130 _ HG ltac:(lia) ltac:(lia) HPPL HmT) as HPPLT.
pose proof (w6cb_sz8_rng (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r))) as Hsz.
set (r' := snd (w6cb_sz8 (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))) in *.
set (sz := fst (w6cb_sz8 (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))) in *.
set (ty := w6cb_ty8 (fst (fuzz_u8 r))) in *.
eapply SRr_bind.
{ apply (HSET (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    (x_k cx) lyD SD WD memT mdT regsT (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length r')) (Z.of_nat (length r'))
    (e_pp (x_e cx)) HJT HGEO T1).
  - w6cb_kept HkT. exact D2.
  - w6cb_kept HkT. exact D3.
  - w6cb_kept HkT. exact D4.
  - w6cb_kept HkT. exact D9.
  - exact T10.
  - exact T11.
  - exact T12.
  - exact T18.
  - exact T22.
  - lia.
  - apply (w6cb_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6cb_hdr_wr; lia].
  - exact (w6cb_fsh_T WD memD memT _ _ _ HG HFSH HmT).
  - exact HPPLT.
  - exact HPPT.
  - exact HPP0.
  - exact HPP1. }
intros WJ cJ _ HPJ.
destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J6 & J13 & J22 & J15 & HmJ & HEJ).
subst WJ.
eapply (w6cb_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ r' Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6cb_keep_clob q Hq) as (Hq0 & _ & Hq2). exact (HkT q Hq0 Hq2).
- exact J22.
- exact J15.
- exact J13.
- exact J6.
- exact (w6cb_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6cb_ent8 b r Hkd). reflexivity.
Qed.

Theorem w6cb_piece_of : rs_piece_W6c_stmt rsegs B MT.
Proof using MTL H6 H7 H8 HCPY HSET.
intros cx POST rest i k kd Hst Hin HJ.
cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]].
- exact (w6cb_case6 cx POST rest i k kd (eq_sym E) Hst HJ).
- exact (w6cb_case7 cx POST rest i k kd (eq_sym E) Hst HJ).
- exact (w6cb_case8 cx POST rest i k kd (eq_sym E) Hst HJ).
Qed.
End h.
End d.
End b.
