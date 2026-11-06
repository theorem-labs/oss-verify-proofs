(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v, with its module paths and module names changed; 291 of its 338 lines of code are new or changed and 364 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5OpenP.v at 164759458cd; module paths changed, rs_ -> hs_, rm_ -> hm_, rl_ -> hd_, role_himg_A -> headamp_himg_A, every pc moved to image A of fuzz_headamp (SELS 0x8165c, C 0x817a0, CL 0x82a14), the cut facts read from headamp's registers and cells (the cursor in s11 at SELS and in s9 at C / CL, pp in R+0xf0 and in s11 at C / CL; at R+0xc0, the count R+0xc8, the bounds R+0x100 / R+0x108, in.n R+0x118, hi_w1's cells [R, R+0x160)), the frame's shadow pattern of 80 bytes, the start facts from lib/A/HPgW6cKit.v (hs_in_now, hs_rom_now) and lib/A/HPgW5Seg.v (w5_pre_facts at hs_pre ... (hi_shA headamp_himg_A)), the AR_laws Section hypothesis removed. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the piece lemma of the
   params Struct's header and its pod count in LLVMFuzzerTestOneInput (0x80bc0), SELS 0x8165c -> C 0x817a0 /
   CL 0x82a14, as lib/A/HPgSeg.v states it (hs_piece_W5_open_stmt). Proves no function (kind: segment lemma).

   HOW. The cut SELS gives the code's facts (registers, real-frame cells, pp->len, rom_view and the input byte at
   the cursor with its shadow, carried to the cut by lib/A/HPgW6cKit.v hs_rom_now / hs_in_now); one of the three
   core walks of lib/A/HPgW5Open.v runs from them (no input left: count 0 -> CL; a count byte c with c mod 33 = 0 ->
   CL; c mod 33 <> 0 -> C with the pod index 0); the end cut is rebuilt from its post: the journal and frame part,
   the (location, value) facts (the cursor now in s9, pp in s11), the frame's shadow (kept), the first block's
   image (Model.pc_buf_open: the Struct's size word 0 and its type appended) and the tie of the count to the input
   (Model.prop_step's Struct arm, fuzz_u8). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6cKit HPgW5Kit HPgW5Seg HPgW5Open.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the model at the Struct's header ---- *)
(* the Struct's size word (0 until the close) and its type *)
Definition w5_shdr : list byte := le32 0 ++ le32 POD_STRUCT.
Lemma w5_img_open_eq : forall sh ps,
pc_image (PbCut sh ps (Some [])) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ w5_shdr)
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_open. unfold w5_shdr. rewrite <- !app_assoc.
unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[]|]; reflexivity.
Qed.
Lemma w5_skipn_cons : forall (l : list byte) j x t, skipn j l = x :: t ->
(j < length l)%nat /\ nth j l (Z_to_bv 8 0) = x /\ skipn (S j) l = t.
Proof.
intros l j. revert l. induction j as [|j IH]; intros [|y l] x t H; cbn in H; try discriminate.
- injection H as -> ->. cbn. split; [lia | split; reflexivity].
- destruct (IH l x t H) as (H1 & H2 & H3). cbn. split; [lia | split; assumption].
Qed.
Lemma w5_tie_open : forall sh ps sel rest r c r', (sel, r) = fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))) ->
sel mod 4 <> 0 -> Z.testbit sel 4 = false -> (c, r') = fuzz_u8 r -> hs_pod_tie sh ps (c mod 33) [] rest r'.
Proof.
intros sh ps sel rest r c r' H1 H2 H3 H4. exists sel, c, r, r'.
split; [exact H1|]. split; [exact H4|]. split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the end of the three runs, shared: the cut's frame, the facts kept, the image with the Struct's header *)
Lemma w5_open_after : forall cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 (Ep : Z -> Prop) W3 ly3 S3 regs3 mem3 md3,
  hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_cut_SELS rsegs B MT cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hs_core rsegs B MT cx (hs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) -> ~ Ep a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, Ep a -> (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 8) \/
     (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) \/ (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) \/
     (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120)) ->
  hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx) + hs_at_of sh ps) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (e_pp (x_e cx) + 0x4000) 8 (hs_at_of sh ps + 8) ->
  hs_fsh_at rsegs cx W3 mem3 hs_P0 /\ hs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps (Some []))).
Proof.
intros cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 Ep W3 ly3 S3 regs3 mem3 md3 Hpre Hcut Hcore3 Hmem HEp Rb Rl.
pose proof (w5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
destruct Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen _].
assert (Hat16 : 16 <= hs_at_of sh ps) by (unfold hs_at_of, hs_plen; pose proof (w5_plen_lo sh ps Hsh7); unfold hs_plen in *; lia).
assert (H5440 : hs_at_of sh ps + 16 <= 5440) by (unfold hs_at_of, hs_plen; lia).
(* every byte the run did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 8) ->
  ~ (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) ->
  ~ (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) -> ~ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4 H5. apply Hmem; [exact Ha | exact H1 |]. intros X. destruct (HEp a X) as [Y|[Y|[Y|Y]]]; auto. }
split.
- unfold hs_fsh_at in *. eapply hm_fsh_kept; [exact Hfsh|]. intros j Hj.
  change (length hs_P0) with 80%nat in Hj.
  pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)) as D1.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
  unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
  apply Kp; lia.
- pose proof (w5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
  assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = hs_at_of sh ps).
  { rewrite !length_app, !length_le32. unfold hs_at_of, hs_plen. lia. }
  assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
    (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
    by exact Hpp.
  unfold hs_pp_at.
  change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some [])))).
  rewrite (w5_img_open_eq sh ps).
  set (LA := length_app (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) w5_shdr).
  assert (LS : length w5_shdr = 8%nat) by reflexivity.
  assert (Nb : hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx))
      ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ w5_shdr)).
  { apply hm_bytes_app. split.
    - eapply hm_bytes_kept; [exact (w5_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy. rewrite Hb0 in Hy.
      apply Kp; lia.
    - rewrite Hb0. exact Rb. }
  apply (w5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx))
    (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) _ _
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
  + rewrite LA. lia.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. unfold POD_BUF_MAX. lia.
  + exact EB1.
  + exact EB2.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. exact Rl.
  + refine (proj1 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; lia.
  + refine (proj2 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; lia.
  + intros y Hy. rewrite LA, Nat2Z.inj_add, Hb0, LS in Hy.
    unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
    apply Kp; lia.
Qed.

Lemma w5_piece_open : hs_piece_W5_open_stmt rsegs B MT.
Proof using MTL.
unfold hs_piece_W5_open_stmt. intros cx POST rest i Hst HC HCL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (w5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold hs_from_SELS. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
pose proof Hcut as Hcut0.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
unfold hs_at_cx in Hat. unfold hs_L_KEY in Hat.
assert (E4 : (sel mod 4 =? 0) = false) by (apply Z.eqb_neq; exact Hsel4).
rewrite E4 in Hat. cbv beta iota in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walks take ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (w5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (w5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(w5_in)) as A9.
pose proof (w5_at_reg _ _ _ _ _ 10 (hs_at_of sh ps - 0x3ffd) Hat ltac:(w5_in)) as A10.
pose proof (w5_at_reg _ _ _ _ _ 20 (shadow_addr (e_pp (x_e cx) + 0x4000)) Hat ltac:(w5_in)) as A20.
pose proof (w5_at_reg _ _ _ _ _ 21 (e_pp (x_e cx) + 0x4000) Hat ltac:(w5_in)) as A21.
pose proof (w5_at_reg _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(w5_in)) as A23.
pose proof (w5_at_reg _ _ _ _ _ 27 (hs_cur rsegs cx rest r) Hat ltac:(w5_in)) as A27.
pose proof (w5_at_cell _ _ _ _ _ 0xc0 (hs_at_of sh ps) Hat ltac:(w5_in)) as Vc0.
pose proof (w5_at_cell _ _ _ _ _ 0xf0 (e_pp (x_e cx)) Hat ltac:(w5_in)) as Vf0.
pose proof (w5_at_cell _ _ _ _ _ 0x100 (-0x4001) Hat ltac:(w5_in)) as V100.
pose proof (w5_at_cell _ _ _ _ _ 0x108 (-0x3ffd) Hat ltac:(w5_in)) as V108.
pose proof (w5_at_cell _ _ _ _ _ 0x118 (Z.of_nat (length r)) Hat ltac:(w5_in)) as V118.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen _].
assert (Hps2 : (length ps <= 2)%nat) by lia.
assert (Hat16 : 16 <= hs_at_of sh ps) by (unfold hs_at_of, hs_plen; pose proof (w5_plen_lo sh ps Hsh7); unfold hs_plen in *; lia).
assert (H5440 : hs_at_of sh ps + 8 <= 5440) by (unfold hs_at_of, hs_plen; lia).
(* the input: what is left of it, its byte at the cursor and the shadow, at the cut *)
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hdisj).
destruct (hs_in_now rsegs B MT cx rest hs_P0 ly2 S2 W2 regs2 mem2 md2 Hpre Hin Hcore Hfsh eq_refl) as (Ibytes & Ira & _).
pose proof (hs_rom_now rsegs B MT w5_segs_low cx ly2 S2 W2 regs2 mem2 md2 Hpre Hcore) as Hrom.
destruct Hsuf as (j & Hj & Hr).
assert (Hcurv : hs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j)
  by (unfold hs_cur; rewrite Hr, length_skipn; lia).
assert (Hnl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hr, length_skipn; lia).
assert (Hcur : 0 <= hs_cur rsegs cx rest r < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
rewrite Z.mod_small in Vc0 by lia. rewrite Z.mod_small in Vf0 by lia.
rewrite Z.mod_small in V118 by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (w5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = hs_at_of sh ps).
{ rewrite !length_app, !length_le32. unfold hs_at_of, hs_plen. lia. }
assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
  (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
  by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hs_at_of sh ps)).
{ rewrite <- Hb0. refine (hm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
assert (Hamr' : hs_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hdis : forall a, hs_cur rsegs cx rest r <= a < hs_cur rsegs cx rest r + Z.of_nat (length r) ->
  ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) /\ ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx) + 0x160)).
{ intros a Ha. destruct (Hdisj a ltac:(lia)) as (D1 & D2 & D3). split; [exact D3|].
  intros X. destruct (Z.lt_ge_cases a (e_R (x_e cx))) as [Y|Y]; [exact (D1 ltac:(lia))|].
  apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* the cells and registers every exit keeps *)
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) [10; 11; 12; 25; 27]%bv).
{ intros r0 [-> | [-> | ->]]; w5_notin. }
destruct r as [|x t].
- (* no input left: the count is 0, CL *)
  eapply SRr_bind.
  { change (cfg_at rsegs HS_SELS regs2 mem2 md2) with (cfg_at rsegs 0x8165c regs2 mem2 md2).
    refine (w5_open_core_nil B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
      (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hs_at_of sh ps)
      (hs_cur rsegs cx rest []) 0 HJ Ppin2 Ppout A2 A9 A10 A20 A21 A23 A27 Vc0 Vf0 V100 V108 V118 Vlen Hrom RB3 RB1 RB2
      Hat16 H5440 ltac:(lia) ltac:(lia) Hamr' Hdis eq_refl). }
  intros W3 c3 Hle Hpost.
  assert (HEp : forall a, (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 8) \/
    (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) \/ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) ->
    hs_E1 rsegs cx a).
  { intros a [Ha|[Ha|Ha]]; [right; lia | right; lia |].
    left. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
    apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
  destruct (w5_core_post B MT MTL cx (hs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x82a14 _ _ W3 c3
    Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rb & Rl & R118 & R25 & R27)).
  rewrite Hsp in Hmem.
  destruct (w5_open_after cx rest sh np sel ps [] ly2 S2 W2 regs2 mem2 md2 _ W3 ly3 S3 regs3 mem3 md3
    Hpre Hcut0 Hcore3 Hmem ltac:(intros a [X|[X|X]]; auto) Rb Rl) as (Hfsh3 & Hpp3).
  assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x118 ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply Hmem; [lia | lia | intros [X|[X|X]]; lia]. }
  change (cfg_at rsegs 0x82a14 regs3 mem3 md3) with (cfg_at rsegs HS_CL regs3 mem3 md3).
  apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] [] Hlen).
  split; [exact Hcore3|]. split.
  { unfold hs_at_cx, hs_at. cbn [hs_Rc hs_Rc0 hs_Kc app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first [ w5_kept Hat Hkeep Kc
               | (cbn [hd_at hd_xv]; exact R25)
               | (cbn [hd_at hd_xv]; exact R27)
               | (cbn [hd_at hd_xv length Z.of_nat]; rewrite Z.mod_0_l by lia; exact R118) ]. }
  split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exists j; split; [exact Hj | exact Hr]|].
  split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
  split; [exact (w5_tie_open sh ps sel rest [] 0 [] Hselr Hsel4 Hselb eq_refl)|].
  split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
  split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
- (* a count byte b at the cursor *)
  destruct (w5_skipn_cons rest j x t (eq_sym Hr)) as (Hjl & Hnth & Ht).
  assert (Vb : val_mem rsegs (mrestrict (w_H W2) mem2) (hs_cur rsegs cx rest (x :: t)) 1 (bv_unsigned x)).
  { rewrite Hcurv, <- Hnth. exact (hm_bytes_byte rsegs (w_H W2) mem2 (e_src (x_e cx)) rest j Ibytes Hjl). }
  assert (Vbr : 0 <= bv_unsigned x < 256) by (pose proof (bv_unsigned_in_range 8 x) as X; exact X).
  assert (Rab : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hs_cur rsegs cx rest (x :: t)) 1).
  { apply (range_addressable_sub _ _ (e_src (x_e cx)) (e_left (x_e cx))); [exact Ira | lia | lia]. }
  assert (Hamc : amem_range (hs_cur rsegs cx rest (x :: t)) 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Ht' : hs_suffix rest t) by (exists (S j); split; [lia | symmetry; exact Ht]).
  assert (Hcur1 : hs_cur rsegs cx rest t = hs_cur rsegs cx rest (x :: t) + 1)
    by (unfold hs_cur; cbn [length]; lia).
  assert (Hnl1 : Z.of_nat (length t) = Z.of_nat (length (x :: t)) - 1) by (cbn [length]; lia).
  destruct (Z.eqb_spec (bv_unsigned x mod 33) 0) as [Ez|Ez].
  + (* the count is 0: CL *)
    eapply SRr_bind.
    { change (cfg_at rsegs HS_SELS regs2 mem2 md2) with (cfg_at rsegs 0x8165c regs2 mem2 md2).
      refine (w5_open_core_zero B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hs_at_of sh ps)
        (hs_cur rsegs cx rest (x :: t)) (Z.of_nat (length (x :: t))) HJ Ppin2 Ppout A2 A9 A10 A20 A21 A23 A27 Vc0 Vf0
        V100 V108 V118 Vlen Hrom RB3 RB1 RB2 Hat16 H5440 ltac:(lia) ltac:(lia) Hamr' Hdis Hamc (bv_unsigned x)
        ltac:(cbn [length]; lia) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    assert (HEp : forall a, (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 8) \/
      (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) \/ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) \/
      (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) -> hs_E1 rsegs cx a).
    { intros a [Ha|[Ha|Ha]]; [right; lia | right; lia |].
      left. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
      apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
    destruct (w5_core_post B MT MTL cx (hs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x82a14 _ _ W3 c3
      Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
      (Rb & Rl & R118 & Rc8 & R25 & R27)).
    rewrite Hsp in Hmem.
    destruct (w5_open_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 _ W3 ly3 S3
      regs3 mem3 md3 Hpre Hcut0 Hcore3 Hmem ltac:(intros a [X|[X|[X|X]]]; auto) Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0xc8 \/ e_R (x_e cx) + 0xd0 <= a < e_R (x_e cx) + 0x118 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; [lia | lia | intros [X|[X|[X|X]]]; lia]. }
    change (cfg_at rsegs 0x82a14 regs3 mem3 md3) with (cfg_at rsegs HS_CL regs3 mem3 md3).
    apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] t Hlen).
    split; [exact Hcore3|]. split.
    { unfold hs_at_cx, hs_at. cbn [hs_Rc hs_Rc0 hs_Kc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ w5_kept Hat Hkeep Kc
                 | (cbn [hd_at hd_xv]; rewrite Hcur1; exact R25)
                 | (cbn [hd_at hd_xv]; exact R27)
                 | (cbn [hd_at hd_xv]; rewrite Z.mod_small by lia; rewrite Hnl1; exact R118) ]. }
    split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Ht'|].
    split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
    split; [rewrite <- Ez; exact (w5_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
    split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
  + (* a count in 1 .. 32: the pod loop's head C, pod index 0 *)
    eapply SRr_bind.
    { change (cfg_at rsegs HS_SELS regs2 mem2 md2) with (cfg_at rsegs 0x8165c regs2 mem2 md2).
      refine (w5_open_core_pos B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hs_at_of sh ps)
        (hs_cur rsegs cx rest (x :: t)) (Z.of_nat (length (x :: t))) HJ Ppin2 Ppout A2 A9 A10 A20 A21 A23 A27 Vc0 Vf0
        V100 V108 V118 Vlen Hrom RB3 RB1 RB2 Hat16 H5440 ltac:(lia) ltac:(lia) Hamr' Hdis Hamc (bv_unsigned x)
        ltac:(cbn [length]; lia) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    assert (HEp : forall a, (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 8) \/
      (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) \/ (e_R (x_e cx) + 0x118 <= a < e_R (x_e cx) + 0x120) \/
      (e_R (x_e cx) + 0xc8 <= a < e_R (x_e cx) + 0xd0) -> hs_E1 rsegs cx a).
    { intros a [Ha|[Ha|Ha]]; [right; lia | right; lia |].
      left. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
      apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
    destruct (w5_core_post B MT MTL cx (hs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x817a0 _ _ W3 c3
      Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
      (Rb & Rl & R118 & Rc8 & R25 & R27 & R11)).
    rewrite Hsp in Hmem.
    destruct (w5_open_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 _ W3 ly3 S3
      regs3 mem3 md3 Hpre Hcut0 Hcore3 Hmem ltac:(intros a [X|[X|[X|X]]]; auto) Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0xc8 \/ e_R (x_e cx) + 0xd0 <= a < e_R (x_e cx) + 0x118 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; [lia | lia | intros [X|[X|[X|X]]]; lia]. }
    assert (Hcnt : 0 < bv_unsigned x mod 33 <= 32) by (pose proof (Z.mod_pos_bound (bv_unsigned x) 33 ltac:(lia)); lia).
    change (cfg_at rsegs 0x817a0 regs3 mem3 md3) with (cfg_at rsegs HS_C regs3 mem3 md3).
    apply (HC ly3 S3 W3 regs3 mem3 md3 sh np ps (bv_unsigned x mod 33) [] t Hlen eq_refl).
    split.
    { split; [exact Hcore3|]. split; [exact Hin|]. split; [exact Ht'|]. split; [exact Ht'|].
      split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
      split; [exact (w5_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
      split; [exact Hps2|]. split; [lia|]. split; [constructor|]. split; [cbn; lia | cbn [length Z.of_nat]; lia]. }
    split.
    { unfold hs_at_cx, hs_at. cbn [hs_L_pod hs_Rc hs_Rc0 hs_Kc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ w5_kept Hat Hkeep Kc
                 | (cbn [hd_at hd_xv]; rewrite Hcur1; exact R25)
                 | (cbn [hd_at hd_xv]; exact R27)
                 | (cbn [hd_at hd_xv length Z.of_nat]; exact R11)
                 | (cbn [hd_at hd_xv]; rewrite Z.mod_small by lia; exact Rc8)
                 | (cbn [hd_at hd_xv]; rewrite Z.mod_small by lia; rewrite Hnl1; exact R118) ]. }
    split; [exact Hfsh3 | exact Hpp3].
Qed.
End p.

Print Assumptions w5_piece_open.
