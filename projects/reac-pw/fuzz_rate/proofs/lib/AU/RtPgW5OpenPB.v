(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v at 533bf30ff015 for image B (fuzz_rate.asan-ubsan): image B's block SEL7 0x80ff4 -> LATCH7 0x8257c (e into scope, memset(e.body, 0, 96) through lib/AU/RtPgStepsB.v rtsb_intrin_at at 0x51d54, e.size = e.type = 4, the call pod_write_ent(pp, e) 0x81054 through rtsb_pwe_at with lib/AU/PweSpec.v's contract at 0x83cc4 as a Section hypothesis, e out of scope) in three engine runs over the kit lib/AU/RtPgPropBKit.v, with the frame shadow, frame-object and record facts of lib/AU/RtPgMemB.v; the piece is lib/AU/RtPgSegB.v's rsb_piece_W4_int7_stmt with image B's cut lists. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBInt7.v, with its module names changed; 314 of its 368 lines of code are new or changed and 685 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5OpenP.v at a906250c10ef for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (SELS 0x81150 -> C 0x8127c / CL 0x82484), cut lists (lib/A/RtPgSeg.v:
   the cursor in R+0x100 and in.n in s8 at SELS, both in s9 / s8 at C and CL, the count in R+0xf0, the six header
   cells rs_Hc, the frame's 56 shadow bytes) and segment start (rs_start_M01 with its own rt_fsh conjunct); the input
   byte and its shadow at the cut come from lib/A/RtPgPropLib.v pa_input_now, the read-only image from
   lib/A/RtPgW5Seg.v w5_rom_now; the three core walks are the lemmas of lib/A/RtPgW5Open.v, not Section
   hypotheses; rm_ / rl_ become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5OpenP.v at a66696a9b1d1 for the same unit's
   image B (fuzz_rate.asan-ubsan): image B's pcs (SELS 0x81210 -> C 0x813a0 / CL 0x824c0) and cut lists
   (lib/AU/RtPgSegB.v: the cursor in s10 and in.n in t4 at all three cuts, &pp->len in s2, pp and ~pp and &e62 in the
   cells R+0x168 / R+0x108 / R+0x150, the count in R+0x140 and the four cells R+0x98 .. R+0xb0 the piece writes, the
   frame's 88 shadow bytes, the real-frame ranges of hi_w1); the helpers of lib/A/RtPgPropLib.v and
   lib/A/RtPgW5CloseP.v this file used are lib/AU/RtPgW5SegB.v's (w5b_); the three core walks are the lemmas of
   lib/AU/RtPgW5OpenB.v; rtm_ / pa_ / w5_ become rtmb_ / w5b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the piece lemma of the params Struct's
   header and its pod count in LLVMFuzzerTestOneInput (0x8076c), SELS 0x81210 -> C 0x813a0 / CL 0x824c0, as
   lib/AU/RtPgSegB.v states it (rsb_piece_W5_open_stmt). Proves no function (kind: segment lemma).

   HOW. The cut SELS gives the code's facts (registers, real-frame cells, pp->len from the first block's image,
   rom_view and the input byte at the cursor with its shadow, carried to the cut by RtPgW5SegB.w5b_rom_now and
   w5b_input_now); one of the three core walks runs from them (no input left: count 0 -> CL; a count byte c with
   c mod 33 = 0 -> CL; c mod 33 <> 0 -> C with the pod index 0); the end cut is rebuilt from its post: the journal
   and frame part (RtPgW5SegB.w5b_core_post), the (location, value) facts, the frame's shadow (kept), the first
   block's image (Model.pc_buf_open: the Struct's size word 0 and its type appended) and the tie of the count to the
   input (Model.prop_step's Struct arm, fuzz_u8). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW5KitB RtPgW5SegB RtPgW5OpenB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the model at the Struct's header ---- *)
(* the Struct's size word (0 until the close) and its type *)
Definition w5b_shdr : list byte := le32 0 ++ le32 POD_STRUCT.
Lemma w5b_img_open_eq : forall sh ps,
pc_image (PbCut sh ps (Some [])) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ w5b_shdr)
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_open. unfold w5b_shdr. rewrite <- !app_assoc.
unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[]|]; reflexivity.
Qed.
Lemma w5b_tie_open : forall sh ps sel rest r c r', (sel, r) = fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))) ->
sel mod 4 <> 0 -> Z.testbit sel 4 = false -> (c, r') = fuzz_u8 r -> rsb_pod_tie sh ps (c mod 33) [] rest r'.
Proof.
intros sh ps sel rest r c r' H1 H2 H3 H4. exists sel, c, r, r'.
split; [exact H1|]. split; [exact H4|]. split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the end of the three runs, shared: the frame's shadow (kept) and the image with the Struct's header *)
Lemma w5b_open_after : forall cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 (Ep : Z -> Prop) W3 mem3,
  rsb_pre rsegs B cx -> rsb_cut_SELS rsegs B MT cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) -> ~ Ep a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, Ep a -> (q_pp (x_e cx) + rsb_at_of sh ps <= a < q_pp (x_e cx) + rsb_at_of sh ps + 8) \/
     (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) \/
     (q_R (x_e cx) + 0x98 <= a < q_R (x_e cx) + 0xb8) \/ (q_R (x_e cx) + 0x140 <= a < q_R (x_e cx) + 0x148)) ->
  rtmb_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx) + rsb_at_of sh ps) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (q_pp (x_e cx) + 0x4000) 8 (rsb_at_of sh ps + 8) ->
  rsb_fsh_at rsegs cx W3 mem3 rsb_P0 /\ rsb_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps (Some []))).
Proof using LAWS.
intros cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 Ep W3 mem3 Hpre Hcut Hmem HEp Rb Rl.
pose proof (w5b_pre_facts B LAWS cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
destruct Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
assert (Hps2 : (length ps <= 2)%nat) by lia.
destruct (w5b_img_bounds sh ps Hwf Hps2) as (IB1 & IB2 & EB1 & EB2).
assert (Hat8 : 16 <= rsb_at_of sh ps /\ rsb_at_of sh ps + 8 <= 5440)
  by (pose proof (w5b_plen_lo sh ps Hsh7); unfold rsb_at_of, rsb_plen in *; lia).
(* every byte the run did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) ->
  ~ (q_pp (x_e cx) + rsb_at_of sh ps <= a < q_pp (x_e cx) + rsb_at_of sh ps + 8) ->
  ~ (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) ->
  ~ (q_R (x_e cx) + 0x98 <= a < q_R (x_e cx) + 0xb8) ->
  ~ (q_R (x_e cx) + 0x140 <= a < q_R (x_e cx) + 0x148) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4 H5. apply Hmem; [exact Ha | exact H1 |].
  intros X. destruct (HEp a X) as [Y|[Y|[Y|Y]]]; auto. }
split.
- unfold rsb_fsh_at in *. eapply rtmb_fsh_kept; [exact Hfsh|]. intros j Hj.
  change (length rsb_P0) with 88%nat in Hj.
  pose proof (Z.mul_div_le (q_F (x_e cx)) 8 ltac:(lia)) as D1.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
  unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
  apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; lia.
- assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = rsb_at_of sh ps).
  { rewrite !length_app, !length_le32. unfold rsb_at_of, rsb_plen. lia. }
  assert (Old : rtmb_bytes rsegs (w_H W2) mem2 (q_pp (x_e cx))
    (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
    by exact Hpp.
  unfold rsb_pp_at.
  change (rtmb_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx)) (pc_image (PbCut sh ps (Some [])))).
  rewrite (w5b_img_open_eq sh ps).
  set (LA := length_app (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) w5b_shdr).
  assert (LS : length w5b_shdr = 8%nat) by reflexivity.
  assert (Nb : rtmb_bytes rsegs (w_H W3) mem3 (q_pp (x_e cx))
      ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ w5b_shdr)).
  { apply rtmb_bytes_app. split.
    - eapply rtmb_bytes_kept; [exact (w5b_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy. rewrite Hb0 in Hy.
      apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; lia.
    - rewrite Hb0. exact Rb. }
  apply (w5b_img_gen (w_H W2) mem2 (w_H W3) mem3 (q_pp (x_e cx))
    (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) _ _
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
  + rewrite LA. lia.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. unfold POD_BUF_MAX. lia.
  + exact EB1.
  + exact EB2.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. exact Rl.
  + refine (proj1 (w5b_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; lia.
  + refine (proj2 (w5b_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; lia.
  + intros y Hy. rewrite LA, Nat2Z.inj_add, Hb0, LS in Hy.
    unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
    apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; lia.
Qed.

(* the input byte at the cursor, when one is left: it lies outside the two real-frame ranges of the segment's write
   set and outside the first block *)
Lemma w5b_rt_in : forall cx rest, rsb_in rsegs cx rest ->
  forall a, q_src (x_e cx) <= a < q_src (x_e cx) + q_left (x_e cx) ->
  ~ (q_R (x_e cx) + 0x58 <= a < q_R (x_e cx) + 0x148) /\ ~ (q_R (x_e cx) + 0x150 <= a < q_R (x_e cx) + 0x180) /\
  ~ (q_pp (x_e cx) <= a < q_pp (x_e cx) + PP_SIZE).
Proof.
intros cx rest Hin a Ha. destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hdisj).
destruct (Hdisj a Ha) as (D1 & D2 & D3). split; [|split; [|exact D3]]; intros X; apply D2.
- unfold rt_inw. cbn [hi_w1 rate_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- unfold rt_inw. cbn [hi_w1 rate_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
  cbn [fst snd rt_xv]. lia.
Qed.

Lemma w5b_piece_open : rsb_piece_W5_open_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rsb_piece_W5_open_stmt. intros cx POST rest i Hst HC HCL.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (w5b_pre_facts B LAWS cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold rsb_from_SELS. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
pose proof Hcut as Hcut0.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
unfold rsb_at_cx in Hat. unfold rsb_L_KEY in Hat.
assert (E4 : (sel mod 4 =? 0) = false) by (apply Z.eqb_neq; exact Hsel4).
rewrite E4 in Hat. cbv beta iota in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walks take ---- *)
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))).
{ rewrite <- (w5b_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5b_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (w5b_at_reg _ _ _ _ _ 5 (Z.of_nat (length ps)) Hat ltac:(w5b_in)) as A5.
pose proof (w5b_at_reg _ _ _ _ _ 6 (-0x4001) Hat ltac:(w5b_in)) as A6.
pose proof (w5b_at_reg _ _ _ _ _ 9 (q_R (x_e cx)) Hat ltac:(w5b_in)) as A9.
pose proof (w5b_at_reg _ _ _ _ _ 14 1 Hat ltac:(w5b_in)) as A14.
pose proof (w5b_at_reg _ _ _ _ _ 18 (q_pp (x_e cx) + 0x4000) Hat ltac:(w5b_in)) as A18.
pose proof (w5b_at_reg _ _ _ _ _ 20 SHADOW_OFF Hat ltac:(w5b_in)) as A20.
pose proof (w5b_at_reg _ _ _ _ _ 25 1 Hat ltac:(w5b_in)) as A25.
pose proof (w5b_at_reg _ _ _ _ _ 26 (rsb_cur rsegs cx rest r) Hat ltac:(w5b_in)) as A26.
pose proof (w5b_at_reg _ _ _ _ _ 27 (q_F (x_e cx) + 0x20) Hat ltac:(w5b_in)) as A27.
pose proof (w5b_at_reg _ _ _ _ _ 29 (Z.of_nat (length r)) Hat ltac:(w5b_in)) as A29.
pose proof (w5b_at_cell _ _ _ _ _ 0x108 (Z.lnot (q_pp (x_e cx))) Hat ltac:(w5b_in)) as V108.
pose proof (w5b_at_cell _ _ _ _ _ 0x120 (-0x3ffd) Hat ltac:(w5b_in)) as V120.
pose proof (w5b_at_cell _ _ _ _ _ 0x150 (q_F (x_e cx) + 0x210) Hat ltac:(w5b_in)) as V150.
pose proof (w5b_at_cell _ _ _ _ _ 0x168 (q_pp (x_e cx)) Hat ltac:(w5b_in)) as V168.
pose proof (w5b_at_cell _ _ _ _ _ 0x170 (shadow_addr (q_pp (x_e cx) + 0x4000)) Hat ltac:(w5b_in)) as V170.
assert (Hshb : 0 <= shadow_addr (q_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (q_pp (x_e cx) + 0x4000) / 8 < 2 ^ 44) by
    (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
rewrite Z.mod_small in V150 by lia.
rewrite Z.mod_small in V168 by lia.
rewrite Z.mod_small in V170 by lia.
assert (Hps2 : (length ps <= 2)%nat) by lia.
destruct (w5b_img_bounds sh ps Hwf Hps2) as (IB1 & IB2 & EB1 & EB2).
pose proof (w5b_plen_lo sh ps Hsh7) as Hplen.
assert (Hat16 : 16 <= rsb_at_of sh ps) by (unfold rsb_at_of, rsb_plen in *; lia).
assert (H5440 : rsb_at_of sh ps + 8 <= 5440) by (unfold rsb_at_of, rsb_plen in *; lia).
(* the input: what is left of it, the cursor *)
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
destruct Hsuf as (j & Hj & Hr).
assert (Hcurv : rsb_cur rsegs cx rest r = q_src (x_e cx) + Z.of_nat j)
  by (unfold rsb_cur; rewrite Hr, length_skipn; lia).
assert (Hnl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hr, length_skipn; lia).
assert (Hamr' : q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 47)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hcur : 0 <= rsb_cur rsegs cx rest r < 2 ^ 64) by lia.
assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = rsb_at_of sh ps).
{ rewrite !length_app, !length_le32. unfold rsb_at_of, rsb_plen. lia. }
assert (Old : rtmb_bytes rsegs (w_H W2) mem2 (q_pp (x_e cx))
  (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
  by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rsb_at_of sh ps)).
{ rewrite <- Hb0. refine (rtmb_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (q_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
assert (Hsp : spZ regs2 = q_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
pose proof (w5b_rom_now B MT LAWS cx ly2 S2 W2 regs2 mem2 md2 Hpre Hcore) as Hrom.
(* the registers every exit keeps *)
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) ->
  ~ In (Z_to_bv 5 r0) [10; 11; 12; 13; 15; 16; 22; 25; 26]%bv).
{ intros r0 [-> | [-> | ->]]; w5b_notin. }
destruct r as [|x t].
- (* no input left: the count is 0, CL *)
  assert (Hclob0 : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) ->
    ~ In (Z_to_bv 5 r0) [10; 11; 12; 13; 15; 16; 22; 25]%bv).
  { intros r0 [-> | [-> | ->]]; w5b_notin. }
  eapply SRr_bind.
  { change (cfg_at rsegs RSB_SELS regs2 mem2 md2) with (cfg_at rsegs 0x81210 regs2 mem2 md2).
    refine (w5b_open_core_nil B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
      (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_F (x_e cx)) (q_pp (x_e cx))
      (rsb_at_of sh ps) (Z.of_nat (length ps)) (rsb_cur rsegs cx rest []) 0
      HJ Ppin2 Ppout A2 A5 A6 A9 A14 A18 A20 A25 A26 A27 A29 V108 V120 V150 V168 V170 Vlen
      RB3 RB1 RB2 ltac:(lia) ltac:(lia) Hat16 H5440 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). }
  intros W3 c3 Hle Hpost.
  assert (HEp : forall a, (q_pp (x_e cx) + rsb_at_of sh ps <= a < q_pp (x_e cx) + rsb_at_of sh ps + 8) \/
    (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) \/
    (q_R (x_e cx) + 0x98 <= a < q_R (x_e cx) + 0xb8) -> rsb_E1 rsegs cx a).
  { intros a [Ha|[Ha|Ha]];
    [ apply w5b_E1_pp; unfold PP_SIZE; lia | apply w5b_E1_pp; unfold PP_SIZE; lia | apply w5b_E1_R; lia ]. }
  destruct (w5b_core_post B MT MTL cx (rsb_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x824c0 _ _ W3 c3
    Hcore HEp Hclob0 Hpost)
    as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rb & Rl & R98 & Ra0 & Ra8 & Rb0 & R25)).
  rewrite Hsp in Hmem.
  destruct (w5b_open_after cx rest sh np sel ps [] ly2 S2 W2 regs2 mem2 md2 _ W3 mem3
    Hpre Hcut0 Hmem ltac:(intros a [X|[X|X]]; auto) Rb Rl) as (Hfsh3 & Hpp3).
  assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x98 \/
      q_R (x_e cx) + 0xb8 <= a < q_R (x_e cx) + 0x140 \/ q_R (x_e cx) + 0x148 <= a < q_R (x_e cx) + 0x180 ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply Hmem; unfold T_SEG_STK, ASTACK, PP_SIZE in *; [lia | lia | intros [X|[X|X]]; lia]. }
  change (cfg_at rsegs 0x824c0 regs3 mem3 md3) with (cfg_at rsegs RSB_CL regs3 mem3 md3).
  apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] [] Hlen).
  split; [exact Hcore3|]. split.
  { unfold rsb_at_cx, rsb_at. cbn [rsb_Rc rsb_Rc0 rsb_Kc rsb_Hc app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first [ w5b_kept Hat Hkeep Kc
               | (cbn [rt_at rt_xv]; exact R25)
               | (cbn [rt_at rt_xv]; rewrite Z.mod_small by lia;
                  first [exact R98 | exact Ra0 | exact Ra8 | exact Rb0]) ]. }
  split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exists j; split; [exact Hj | exact Hr]|].
  split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
  split; [exact (w5b_tie_open sh ps sel rest [] 0 [] Hselr Hsel4 Hselb eq_refl)|].
  split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
  split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
- (* a count byte b at the cursor *)
  destruct (w5b_nth_skipn rest j x t (eq_sym Hr)) as (Hjl & Hnth).
  assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length rest)) by lia.
  destruct (w5b_input_now B MT LAWS cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) Hpre Hfsh0 Hin Hcore Hfsh Hj')
    as (Vb & Rab).
  unfold rsb_u8s in Vb. rewrite Nat2Z.id, rtmb_nth_map, Hnth, <- Hcurv in Vb. rewrite <- Hcurv in Rab.
  assert (Vbr : 0 <= bv_unsigned x < 256) by exact (rtmb_byte_range x).
  assert (Hcin : q_src (x_e cx) <= rsb_cur rsegs cx rest (x :: t) < q_src (x_e cx) + q_left (x_e cx)) by lia.
  destruct (w5b_rt_in cx rest Hin _ Hcin) as (Dc1 & Dc2 & Dc3).
  assert (Hamc : amem_range (rsb_cur rsegs cx rest (x :: t)) 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Ht' : rsb_suffix rest t).
  { exists (S j). split; [lia|]. replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, <- Hr. reflexivity. }
  assert (Hcur1 : rsb_cur rsegs cx rest t = rsb_cur rsegs cx rest (x :: t) + 1)
    by (unfold rsb_cur; cbn [length]; lia).
  assert (Hnl1 : Z.of_nat (length t) = Z.of_nat (length (x :: t)) - 1) by (cbn [length]; lia).
  assert (HEp : forall a, (q_pp (x_e cx) + rsb_at_of sh ps <= a < q_pp (x_e cx) + rsb_at_of sh ps + 8) \/
    (q_pp (x_e cx) + 0x4000 <= a < q_pp (x_e cx) + 0x4008) \/
    (q_R (x_e cx) + 0x98 <= a < q_R (x_e cx) + 0xb8) \/ (q_R (x_e cx) + 0x140 <= a < q_R (x_e cx) + 0x148) ->
    rsb_E1 rsegs cx a).
  { intros a [Ha|[Ha|[Ha|Ha]]];
    [ apply w5b_E1_pp; unfold PP_SIZE; lia | apply w5b_E1_pp; unfold PP_SIZE; lia
    | apply w5b_E1_R; lia | apply w5b_E1_R; lia ]. }
  destruct (Z.eqb_spec (bv_unsigned x mod 33) 0) as [Ez|Ez].
  + (* the count is 0: CL *)
    eapply SRr_bind.
    { change (cfg_at rsegs RSB_SELS regs2 mem2 md2) with (cfg_at rsegs 0x81210 regs2 mem2 md2).
      refine (w5b_open_core_zero B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
        (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_F (x_e cx))
        (q_pp (x_e cx)) (rsb_at_of sh ps) (Z.of_nat (length ps)) (rsb_cur rsegs cx rest (x :: t))
        (Z.of_nat (length (x :: t)))
        HJ Ppin2 Ppout A2 A5 A6 A9 A14 A18 A20 A25 A26 A27 A29 V108 V120 V150 V168 V170 Vlen
        RB3 RB1 RB2 ltac:(lia) ltac:(lia) Hat16 H5440 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        Hrom Hamc Dc3 Dc1 Dc2 (bv_unsigned x) ltac:(cbn [length]; lia) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    destruct (w5b_core_post B MT MTL cx (rsb_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x824c0 _ _ W3 c3
      Hcore HEp Hclob Hpost)
      as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rb & Rl & R98 & Ra0 & Ra8 & Rb0 & R25 & R26)).
    rewrite Hsp in Hmem.
    destruct (w5b_open_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 _ W3 mem3
      Hpre Hcut0 Hmem ltac:(intros a X; exact X) Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x98 \/
        q_R (x_e cx) + 0xb8 <= a < q_R (x_e cx) + 0x140 \/ q_R (x_e cx) + 0x148 <= a < q_R (x_e cx) + 0x180 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; unfold T_SEG_STK, ASTACK, PP_SIZE in *; [lia | lia | intros [X|[X|[X|X]]]; lia]. }
    change (cfg_at rsegs 0x824c0 regs3 mem3 md3) with (cfg_at rsegs RSB_CL regs3 mem3 md3).
    apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] t Hlen).
    split; [exact Hcore3|]. split.
    { unfold rsb_at_cx, rsb_at. cbn [rsb_Rc rsb_Rc0 rsb_Kc rsb_Hc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ w5b_kept Hat Hkeep Kc
                 | (cbn [rt_at rt_xv]; rewrite Hcur1; exact R26)
                 | (cbn [rt_at rt_xv]; rewrite Hnl1; exact R25)
                 | (cbn [rt_at rt_xv]; rewrite Z.mod_small by lia;
                    first [exact R98 | exact Ra0 | exact Ra8 | exact Rb0]) ]. }
    split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Ht'|].
    split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
    split; [rewrite <- Ez; exact (w5b_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
    split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
  + (* a count in 1 .. 32: the pod loop's head C, pod index 0 *)
    eapply SRr_bind.
    { change (cfg_at rsegs RSB_SELS regs2 mem2 md2) with (cfg_at rsegs 0x81210 regs2 mem2 md2).
      refine (w5b_open_core_pos B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
        (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_F (x_e cx))
        (q_pp (x_e cx)) (rsb_at_of sh ps) (Z.of_nat (length ps)) (rsb_cur rsegs cx rest (x :: t))
        (Z.of_nat (length (x :: t)))
        HJ Ppin2 Ppout A2 A5 A6 A9 A14 A18 A20 A25 A26 A27 A29 V108 V120 V150 V168 V170 Vlen
        RB3 RB1 RB2 ltac:(lia) ltac:(lia) Hat16 H5440 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        Hrom Hamc Dc3 Dc1 Dc2 (bv_unsigned x) ltac:(cbn [length]; lia) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    destruct (w5b_core_post B MT MTL cx (rsb_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x813a0 _ _ W3 c3
      Hcore HEp Hclob Hpost)
      as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
          (Rb & Rl & R98 & Ra0 & Ra8 & Rb0 & Rf0 & R25 & R26 & R22 & R11)).
    rewrite Hsp in Hmem.
    destruct (w5b_open_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 _ W3 mem3
      Hpre Hcut0 Hmem ltac:(intros a X; exact X) Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x98 \/
        q_R (x_e cx) + 0xb8 <= a < q_R (x_e cx) + 0x140 \/ q_R (x_e cx) + 0x148 <= a < q_R (x_e cx) + 0x180 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; unfold T_SEG_STK, ASTACK, PP_SIZE in *; [lia | lia | intros [X|[X|[X|X]]]; lia]. }
    assert (Hcnt : 0 < bv_unsigned x mod 33 <= 32) by (pose proof (Z.mod_pos_bound (bv_unsigned x) 33 ltac:(lia)); lia).
    change (cfg_at rsegs 0x813a0 regs3 mem3 md3) with (cfg_at rsegs RSB_C regs3 mem3 md3).
    apply (HC ly3 S3 W3 regs3 mem3 md3 sh np ps (bv_unsigned x mod 33) [] t Hlen eq_refl).
    split.
    { split; [exact Hcore3|]. split; [exact Hin|]. split; [exact Ht'|]. split; [exact Ht'|].
      split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
      split; [exact (w5b_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
      split; [exact Hps2|]. split; [lia|]. split; [constructor|]. split; [cbn; lia | cbn [length Z.of_nat]; lia]. }
    split.
    { unfold rsb_at_cx, rsb_at, rsb_L_pod. cbn [rsb_Rc rsb_Rc0 rsb_Kc rsb_Hc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ w5b_kept Hat Hkeep Kc
                 | (cbn [rt_at rt_xv]; rewrite Hcur1; exact R26)
                 | (cbn [rt_at rt_xv]; rewrite Hnl1; exact R25)
                 | (cbn [rt_at rt_xv]; exact R22)
                 | (cbn [rt_at rt_xv length Z.of_nat]; exact R11)
                 | (cbn [rt_at rt_xv]; rewrite Z.mod_small by lia;
                    first [exact R98 | exact Ra0 | exact Ra8 | exact Rb0 | exact Rf0]) ]. }
    split; [exact Hfsh3 | exact Hpp3].
Qed.
End p.

Print Assumptions w5b_piece_open.
