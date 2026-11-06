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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v, with its module paths and module names changed; 189 of its 236 lines of code are new or changed and 364 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5IntP.v at 164759458cd; module paths changed, rs_ -> hs_, rm_ -> hm_, RPgW5Int -> HPgW5Int, the cut pcs moved to image A of fuzz_headamp (SELI 0x82808, LATCH 0x82ac0), the start facts read from headamp's cells (at R+0xc0, first R+0xe8, pp + 0x400c R+0x78, pp R+0xf0, the capacity bounds R+0x100 / R+0x108) in place of role's s11 = pp, the frame's shadow pattern of 80 granules, the kept cells up to R+0x120 (the cursor's R+0x118 and s11 of hs_cur2 kept from SELI), w5_pre_facts taking the frame-shadow pattern, the AR_laws Section hypothesis removed (YG0q.AR_laws_ok). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the piece lemma of the Int-7 value pod of one
   property in LLVMFuzzerTestOneInput (0x80bc0), SELI 0x82808 -> LATCH 0x82ac0, as lib/A/HPgSeg.v states it
   (hs_piece_W5_int_stmt). Proves no function (kind: segment lemma).

   HOW. The cut SELI gives the code's facts (registers, real-frame cells, pp->len from the first block's image); the
   core walk (lib/A/HPgW5Int.v w5_int_core, which takes the runtime's memset contract as its Section hypothesis
   W5_AMEMSET) runs from them to 0x82ac0; the cut LATCH is rebuilt from its post: the journal and frame part, the
   (location, value) facts (all kept: the piece writes no real-frame cell and no register of the list, so s11 and
   R+0x118, the cursor of hs_cur2, are SELI's), the frame's shadow (kept), the first block's image (the property's
   value pod appended, Model.pc_buf_prop, and has_params set when this is the first params property) and
   Model.props_loop's two Int arms (the volume property, and a params property whose selector has bit 4 set). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW5Kit HPgW5Seg HPgW5Int.
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

(* ---- the model of one Int-7 property (Model.prop_step's second and third arms) ---- *)
(* the value pod: size 4, type POD_INT, the body le32 7, four pad bytes *)
Definition w5_ipod : list byte := le32 4 ++ le32 4 ++ le32 7 ++ zeros 4.
(* the first-flag the piece reads: set only on a params property while no params property was written *)
Definition w5_ifst (sel : Z) (ps : list (Z * pval)) : Z := if sel mod 4 =? 0 then 0 else hs_first ps.

Lemma w5_img_int_eq : forall sh ps sel, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(hs_key_of sel, PInt 7)]) None) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) ++ w5_ipod)
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None) || (w5_ifst sel ps =? 1))
  (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps sel Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_prop.
replace (prop_bytes sh (hs_key_of sel, PInt 7)) with (le32 (hs_key_of sel) ++ le32 0 ++ w5_ipod)
  by (unfold prop_bytes; replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh); reflexivity).
rewrite <- !app_assoc.
unfold has_params, params_struct, pc_ents, w5_ifst, hs_key_of. cbn [p_props pc_props pc_open].
rewrite first_params_app. cbn [fst snd].
destruct (Z.eqb_spec (sel mod 4) 0) as [E4|E4].
- destruct (first_params ps) as [v|]; [destruct v|]; reflexivity.
- cbv beta iota. destruct (Z.eqb_spec (hs_first ps) 1) as [E|E].
  + rewrite (w5_first1 ps E). reflexivity.
  + destruct (w5_first0 ps E) as [v Hv]. rewrite Hv. destruct v; reflexivity.
Qed.
Lemma w5_seen_int : forall ps sel,
hs_seen (ps ++ [(hs_key_of sel, PInt 7)]) = if sel mod 4 =? 0 then hs_seen ps else 1.
Proof.
intros ps sel. unfold hs_seen, hs_key_of. rewrite existsb_app. cbn [existsb fst].
destruct (Z.eqb_spec (sel mod 4) 0) as [E|E]; cbn; [rewrite orb_false_r | rewrite orb_true_r]; reflexivity.
Qed.
Lemma w5_wf_int : forall sh ps sel, hs_wf sh ps -> (length ps <= 2)%nat ->
hs_wf sh (ps ++ [(hs_key_of sel, PInt 7)]).
Proof.
intros sh ps sel (Hs & Hk & He & Hl) H2.
assert (HK : 0 <= hs_key_of sel < 2 ^ 32)
  by (unfold hs_key_of; destruct (sel mod 4 =? 0); split; try lia; apply Z.ltb_lt; reflexivity).
split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [split; [exact HK | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn [flat_map snd]; rewrite !app_nil_r; exact He|].
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma w5_loop_int : forall sh ps sel rest r, sh <> 7 ->
ps = fst (props_loop sh (length ps) (hs_r0 rest)) ->
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))) ->
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
(ps ++ [(hs_key_of sel, PInt 7)], r) = props_loop sh (length (ps ++ [(hs_key_of sel, PInt 7)])) (hs_r0 rest).
Proof.
intros sh ps sel rest r Hsh Hps Hs1 H4.
rewrite length_app. cbn [length]. rewrite Nat.add_1_r. rewrite props_loop_S_end.
remember (props_loop sh (length ps) (hs_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs1. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs1. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
unfold hs_key_of. destruct (Z.eqb_spec (sel mod 4) 0) as [E|E]; [reflexivity|].
destruct H4 as [X|X]; [exfalso; exact (E X)|]. rewrite X. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* the runtime's memset contract (__asan_memset at 0x521a8), discharged at the harness level *)
Hypothesis W5_AMEMSET : aintrin_realizes rsegs B OSet 0x521a8.

Lemma w5_piece_int : hs_piece_W5_int_stmt rsegs B MT.
Proof using MTL W5_AMEMSET.
unfold hs_piece_W5_int_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (w5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp).
pose proof Hpre as (_ & Hev & _ & H3 & H4 & _).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold hs_from_SELI. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselr).
destruct Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
unfold hs_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (w5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (w5_getr5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (w5_getr5 (x_regs cx) 3%bv 3 eq_refl). exact H3. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (w5_getr5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (w5_getr5 (x_regs cx) 4%bv 4 eq_refl). exact H4. }
pose proof (w5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(w5_in)) as A9.
pose proof (w5_at_reg _ _ _ _ _ 10 (hs_at_of sh ps - 0x3ffd) Hat ltac:(w5_in)) as A10.
pose proof (w5_at_reg _ _ _ _ _ 20 (shadow_addr (e_pp (x_e cx) + 0x4000)) Hat ltac:(w5_in)) as A20.
pose proof (w5_at_reg _ _ _ _ _ 21 (e_pp (x_e cx) + 0x4000) Hat ltac:(w5_in)) as A21.
pose proof (w5_at_reg _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(w5_in)) as A23.
pose proof (w5_at_cell _ _ _ _ _ 0xc0 (hs_at_of sh ps) Hat ltac:(w5_in)) as Va0.
pose proof (w5_at_cell _ _ _ _ _ 0xe8 (if sel mod 4 =? 0 then 0 else hs_first ps) Hat ltac:(w5_in)) as Vd0.
pose proof (w5_at_cell _ _ _ _ _ 0x78 (e_pp (x_e cx) + 0x400c) Hat ltac:(w5_in)) as V78.
pose proof (w5_at_cell _ _ _ _ _ 0xf0 (e_pp (x_e cx)) Hat ltac:(w5_in)) as Vf0.
pose proof (w5_at_cell _ _ _ _ _ 0x100 (-0x4001) Hat ltac:(w5_in)) as Ve0.
pose proof (w5_at_cell _ _ _ _ _ 0x108 (-0x3ffd) Hat ltac:(w5_in)) as Ve8.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen [c8 Hc8]].
assert (Hps2 : (length ps <= 2)%nat) by lia.
assert (Hat16 : 16 <= hs_at_of sh ps) by (unfold hs_at_of, hs_plen; pose proof (w5_plen_lo sh ps Hsh7); unfold hs_plen in *; lia).
assert (H5440 : hs_at_of sh ps + 16 <= 5440) by (unfold hs_at_of, hs_plen; lia).
assert (Hmod8 : hs_at_of sh ps mod 8 = 0).
{ replace (hs_at_of sh ps) with ((c8 + 1) * 8) by (unfold hs_at_of, hs_plen; lia). apply Z_mod_mult. }
assert (Hfsv : w5_ifst sel ps = 0 \/ w5_ifst sel ps = 1).
{ unfold w5_ifst. destruct (sel mod 4 =? 0); [left; reflexivity | apply w5_first_range]. }
change (if sel mod 4 =? 0 then 0 else hs_first ps) with (w5_ifst sel ps) in Vd0.
rewrite Z.mod_small in Va0 by lia. rewrite Z.mod_small in Vd0 by lia.
rewrite Z.mod_small in V78 by lia. rewrite Z.mod_small in Vf0 by lia.
pose proof (w5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0)) = hs_at_of sh ps).
{ rewrite !length_app, !length_le32. unfold hs_at_of, hs_plen. lia. }
assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
  (pp_image (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
  by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hs_at_of sh ps)).
{ rewrite <- Hb0. refine (hm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs HS_SELI regs2 mem2 md2) with (cfg_at rsegs 0x82808 regs2 mem2 md2).
  exact (w5_int_core B MT MTL W5_AMEMSET (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
    (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx))
    (hs_at_of sh ps) (w5_ifst sel ps) HJ Ppin2 Ppout Hev A2 A9 A3 A4 A10 A20 A21 A23 Va0 Vd0 V78 Vf0 Ve0 Ve8 Vlen
    RB3 RB1 RB2 Hat16 H5440 Hmod8 Hfsv). }
intros W3 c3 Hle Hpost.
assert (HEp : forall a, (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 16) \/
  (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) \/
  (w5_ifst sel ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4010) -> hs_E1 rsegs cx a).
{ intros a [Ha|[Ha|[_ Ha]]]; right; lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) ->
  ~ In (Z_to_bv 5 r0) [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%bv).
{ intros r0 [-> | [-> | ->]]; w5_notin. }
destruct (w5_core_post B MT MTL cx (hs_E1 rsegs cx) _ ly2 S2 W2 regs2 mem2 md2 0x82ac0 _ _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rbytes & Rlen & Rfl)).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + hs_at_of sh ps <= a < e_pp (x_e cx) + hs_at_of sh ps + 16) ->
  ~ (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) ->
  ~ (w5_ifst sel ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4010) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3' H4'. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|[X|X]]; auto. }
(* the real-frame cells of the cut lists: up to R+0x118 + 8 *)
assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x120 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x82ac0 regs3 mem3 md3) with (cfg_at rsegs HS_LATCH regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(hs_key_of sel, PInt 7)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split.
- split; [exact Hcore3|].
  split.
  { unfold hs_fsh_at in *. eapply hm_fsh_kept; [exact Hfsh|]. intros j Hj.
    change (length hs_P0) with 80%nat in Hj.
    pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)) as D1.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
    unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
    apply Kp; try lia; intros [_ X]; lia. }
  split.
  { unfold hs_pp_at.
    change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(hs_key_of sel, PInt 7)]) None))).
    rewrite (w5_img_int_eq sh ps sel Hsh7).
    assert (LI : length w5_ipod = 16%nat) by reflexivity.
    assert (Nb : hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx))
        ((pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) ++ w5_ipod)).
    { apply hm_bytes_app. split.
      - eapply hm_bytes_kept; [exact (w5_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy. rewrite Hb0 in Hy.
        apply Kp; try lia; intros [_ X]; lia.
      - rewrite Hb0. exact Rbytes. }
    apply (w5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx))
      (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) _ _
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
    - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) w5_ipod). lia.
    - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) w5_ipod), Nat2Z.inj_add, Hb0, LI. unfold POD_BUF_MAX. lia.
    - exact EB1.
    - exact EB2.
    - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) w5_ipod), Nat2Z.inj_add, Hb0, LI. exact Rlen.
    - destruct (Z.eqb_spec (w5_ifst sel ps) 1) as [E|E].
      + rewrite orb_true_r. exact (Rfl E).
      + rewrite orb_false_r. refine (proj1 (w5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
        intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; try lia; intros [X _]; exact (E X).
    - eapply hm_bytes_kept.
      + apply hm_bytes_of_val. refine (hm_pp_params_struct rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia.
      + intros y Hy. rewrite ?length_le32, ?length_Z_to_le_bytes in Hy. unfold OFF_PARAMS_STRUCT in Hy.
        apply Kp; try lia; intros [_ X]; lia.
    - intros y Hy. rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hs_key_of sel) ++ le32 0) w5_ipod), Nat2Z.inj_add, Hb0, LI in Hy.
      unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
      apply Kp; try lia; intros [_ X]; lia. }
  split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply w5_wf_int; [exact Hwf | exact Hps2]|].
  split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
  exact (w5_loop_int sh ps sel rest r Hsh7 Hps Hselr Hsel4).
- unfold hs_at_cx, hs_at.
  rewrite (w5_seen_int ps sel).
  replace (Z.of_nat (length (ps ++ [(hs_key_of sel, PInt 7)])) - 1) with (Z.of_nat (length ps))
    by (rewrite length_app; cbn [length]; lia).
  cbn [hs_Rc0 hs_Kc hs_cur2 app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: w5_kept Hat Hkeep Kc.
Qed.
End p.

Print Assumptions w5_piece_int.
