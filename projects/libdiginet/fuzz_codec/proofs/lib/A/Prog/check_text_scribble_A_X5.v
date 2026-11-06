(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v, with its module paths and module names changed; 494 of its 520 lines of code are new or changed and 31 lines of the source are left out. *)
(* The tail of check_text_scribble at image A for n = 5 text characters: the walk of
   lib/A/Prog/check_text_scribble_A_X.v run with n = 5 (one file per n, each about two minutes). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_text_scribble_A.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_text_scribble_A_X.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ABC : abcmp_realizes tfibsegs B A_BCMP.
Lemma cts_tail_5 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(q ch : Z) (tb cj : list Z) ly3 S3 W3 regs3 mem3 md3 fpos,
cts_cut_ret B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch 5 tb cj
  ly3 S3 W3 regs3 mem3 md3 fpos ->
cts_tail_goal B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch 5 tb
  W3 regs3 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch tb cj
  ly3 S3 W3 regs3 mem3 md3 fpos HC0.
pose proof HC0 as HC.
destruct HC as (HE & H10 & H11 & H12 & Hn & HOBJ & HDST & HCJ & HAGR & HLEN & HJ3 & HIN3 & HFRS3 & HP3
  & HIO3 & HM3 & HKEPT & HSP3 & HAL3 & Hgp3 & Htp3 & Hs0 & Hs1 & Ha0 & Hs2 & Hs9 & Hs3 & Hs4 & Hs5
  & Hs6 & Hs7 & Hs8 & Hs10 & Hs11 & HREC & HWANT & HFLP & HFSH & HSAV).
destruct (cts_tail_st B MT LAWS 5 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch tb cj
  ly3 S3 W3 regs3 mem3 md3 fpos HC0 ltac:(vm_compute; reflexivity)) as (HS & SHOK & HRA3).
pose proof HJ3 as HJ.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (ch <= a < ch + 24) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
set (FL := flag_addr ly3 0 fpos) in *. set (F := frame_addr ly3 0 fpos) in *.
assert (E20 : ew (cts_E regs3 regs FL) 20 = Z_to_bv 64 ch)
  by (rewrite (cts_E_reg regs3 regs FL 20 20%bv eq_refl); exact Hs4).
assert (E3 : ew (cts_E regs3 regs FL) 3 = w64 (as_gp B))
  by (rewrite (cts_E_reg regs3 regs FL 3 3%bv eq_refl); exact Hgp3).
assert (E4 : ew (cts_E regs3 regs FL) 4 = w64 (as_tp B))
  by (rewrite (cts_E_reg regs3 regs FL 4 4%bv eq_refl); exact Htp3).
assert (E2 : ew (cts_E regs3 regs FL) 2 = getr regs3 2)
  by (rewrite (cts_E_reg regs3 regs FL 2 2%bv eq_refl); reflexivity).
assert (E8e : ew (cts_E regs3 regs FL) 8 = getr regs 2)
  by (rewrite (cts_E_reg regs3 regs FL 8 8%bv eq_refl); exact Hs0).
assert (E18 : ew (cts_E regs3 regs FL) 18 = Z_to_bv 64 F)
  by (rewrite (cts_E_reg regs3 regs FL 18 18%bv eq_refl); exact Hs2).
pose proof HJ3 as (HAR3 & _).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 0 fpos HAR3 HIN3) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B ly3 S3 W3 mem3 md3 0 fpos HAR3 HIN3) as (HA64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDST as (Hch0 & Hch63 & Hchd & Hchw & Hchra & Hchh & Hcham & Hchoff).
pose proof HE as (HJ0 & HraE & Hra4E & HgpE & HtpE & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  T_check_text_scribble HE ltac:(unfold T_check_text_scribble, ESTACK; lia))
  as (Hceil0 & H47 & H46 & Hal0 & Hpres0).
assert (H46n : 2 ^ 46 + 8352 <= spZ regs).
{ eapply Z.le_trans; [|exact H46]. vm_compute. discriminate. }
pose proof Hcham as Hchamn.
unfold in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in HFapp.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hchamn.
unfold cts_tail_goal, cfg_at. change (w64 A_CTS_RET) with (Z_to_bv 64 A_CTS_RET).
aj_run_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [cts_awr_ro | idtac].
(* the wrapper's entry: hand the two ranges to the memory-comparing runtime *)
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H W3) ?msv) |- _ =>
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc] end.
rreg HS (1%bv : bv 5) Gra. rreg HS (2%bv : bv 5) Gsp. rreg HS (3%bv : bv 5) Ggp.
rreg HS (4%bv : bv 5) Gtp. rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1.
rreg HS (12%bv : bv 5) Ga2.
rewrite E20 in Ga0. rewrite E18, unsigned_lit_small in Ga1 by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & _) & _).
set (o := spZ regs3 - sp0) in *.
(* the first run wrote nothing: every byte of ms is the cut's *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. apply (cw_kept_run (fun _ => False) _ _ (w_H W3) mem3 mem3 (ms_mem ms)
    ltac:(intros; reflexivity) HFr); [|exact Ha | intros []].
  intros b Hb. unfold in_wrange in Hb. destruct Hb as (r & Hr & Hb).
  cbn [cts_ss ss_mem cts_regions In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [cts_save_region cts_rec_region YP09.r_wlo YP09.r_whi] in Hb; lia. }
(* the allocation ceiling is below the wrapper's window *)
assert (HceilN0 : alloc_ceiling + 8352 <= spZ regs).
{ eapply Z.le_trans; [|apply Z.le_sub_le_add_r; exact Hceil0]. apply Z.eq_le_incl. f_equal. }
(* the record's and want's bytes and marks at the wrapper's entry *)
assert (EFa3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p).
{ intros c p. pose proof HJ0 as (_ & Hly0 & _). pose proof HJ3 as (_ & Hly3 & _). unfold frame_addr.
  destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
assert (HKRs : forall x, 0 <= x < 2 ^ 47 -> aview tfibsegs (w_H W3) (ms_mem ms) (SHADOW_OFF + x / 8)
  = aview tfibsegs (w_H W3) mem3 (SHADOW_OFF + x / 8)).
{ intros x Hx. apply KR. pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
assert (HHU3 : shadow_hull_vis (aview tfibsegs (w_H W3) mem3) ch 5).
{ destruct HOBJ as [(bb & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
  - apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 bb m ch 5 HAR3); [|lia|lia|lia].
    eapply Permutation_in; [apply Permutation_sym; exact HP3 | exact Hin].
  - apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 W3 mem3 md3 cid pos ch 5 HAR3);
    [rewrite HFRS3; right; exact Hin | rewrite EFa3; lia | rewrite EFa3; lia | lia]. }
destruct (cts_want_ok W3 mem3 F 5 HFSH HA64 ltac:(lia) ltac:(lia)) as (HRAw3 & HHUw3).
destruct (proj1 (garr8_app tfibsegs _ ch _ _) HREC) as (HREC1 & _).
assert (HBch : forall i, 0 <= i < 5 -> aview tfibsegs (w_H W3) (ms_mem ms) (ch + i)
  = Some (nth (Z.to_nat i) (fst (DgnLib.scribble_text_spec tb 5)) 0)).
{ intros i Hi. rewrite KR by lia.
  assert (HiK : (Z.to_nat i < length (fst (DgnLib.scribble_text_spec tb 5)))%nat)
    by (rewrite HLEN; apply Z2Nat.inj_lt; lia).
  destruct (HREC1 (Z.to_nat i) HiK) as (_ & Hri).
  pose proof (garr8_mbyte tfibsegs _ _ _ (Z.to_nat i) HREC1 HiK) as Hb.
  rewrite Z2Nat.id in Hb by lia.
  unfold aview. rewrite Hb. cbn [option_map]. f_equal. apply cts_u8; exact Hri. }
assert (HBw : forall i, 0 <= i < 5 -> aview tfibsegs (w_H W3) (ms_mem ms) (F + 32 + i)
  = Some (nth (Z.to_nat i) (fst (codec_owe.owed_scribble_text_spec tb 5)) 0)).
{ intros i Hi. rewrite KR by lia.
  assert (HiK : (Z.to_nat i < length (fst (codec_owe.owed_scribble_text_spec tb 5)))%nat)
    by (rewrite HAGR, HLEN; apply Z2Nat.inj_lt; lia).
  destruct (HWANT (Z.to_nat i) HiK) as (_ & Hri).
  pose proof (garr8_mbyte tfibsegs _ _ _ (Z.to_nat i) HWANT HiK) as Hb.
  rewrite Z2Nat.id in Hb by lia.
  unfold aview. rewrite Hb. cbn [option_map]. f_equal. apply cts_u8; exact Hri. }
eapply SRr_bind.
{ eapply (cw_bcmp_at B LAWS A_BCMP ABC W3 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0
    ((0, fpos) :: own) ly3 S3 _ k ch (F + 32) 5 o (Z_to_bv 64 539084)).
  - exact HJ.
  - exact Ga0.
  - exact Ga1.
  - exact Ga2.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Gsp, E2. unfold o. fold (spZ regs3). lia.
  - unfold o. pose proof (Z.div_mod (spZ regs3) 32 ltac:(lia)) as D1.
    pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HAL3, Z.add_0_r in D1. rewrite Hsp0al, Z.add_0_r in D2.
    replace (spZ regs3 - sp0) with ((spZ regs3 / 32 * 2 - sp0 / 16) * 16) by lia. apply Z_mod_mult.
  - unfold o. lia.
  - unfold o. unfold T_check_text_scribble, ESTACK in *. lia.
  - rewrite Ggp. exact E3.
  - rewrite Gtp. exact E4.
  - exact Gra.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (ch + (a - ch)) by lia. rewrite (HBch (a - ch) ltac:(lia)). discriminate.
    + unfold spZ. rewrite Gsp, E2. fold (spZ regs3). unfold coff_win in Hchoff.
      change ESTACK with 4096. change T_check_text_scribble with 8352 in Hchoff. lia.
  - intros a Ha. split.
    + replace a with (F + 32 + (a - F - 32)) by lia. rewrite (HBw (a - F - 32) ltac:(lia)). discriminate.
    + unfold spZ. rewrite Gsp, E2. fold (spZ regs3). change ESTACK with 4096. lia.
  - intros a Ha. unfold o, coff_win in *. change (2 * ESTACK) with 8192.
    change T_check_text_scribble with 8352 in Hchoff. lia.
  - intros a Ha. unfold o. change (2 * ESTACK) with 8192. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - intros x Hx. destruct (HRA3 x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
    unfold shadow_of_addr in *. rewrite HKRs by lia. exact Hsv.
  - intros _ sa Hsa Hn0. apply (HHU3 sa Hsa). rewrite <- Hn0. symmetry. apply KR.
    unfold shadow_addr, SHADOW_OFF in Hsa.
    pose proof (Z.div_pos ch 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (ch + 5 - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (2147450880 + (ch + 5 - 1) / 8) 8
      (2147450880 + (ch + 5 - 1) / 8) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (2147450880 + ch / 8) 8 ltac:(lia) ltac:(lia)). lia.
  - intros x Hx. destruct (HRAw3 x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
    unfold shadow_of_addr in *. rewrite HKRs by lia. exact Hsv.
  - intros _ sa Hsa Hn0. apply (HHUw3 ltac:(lia) sa Hsa). rewrite <- Hn0. symmetry. apply KR.
    unfold shadow_addr, SHADOW_OFF in Hsa.
    pose proof (Z.div_pos (F + 32) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (F + 32 + 5 - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (2147450880 + (F + 32 + 5 - 1) / 8) 8
      (2147450880 + (F + 32 + 5 - 1) / 8) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (2147450880 + (F + 32) / 8) 8 ltac:(lia) ltac:(lia)). lia. }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hkept & Hpres2 & Hsame).
lazymatch type of HS with st_ok _ _ ?ssv _ =>
  let K := eval vm_compute in (run_K 0 CTS_Bx cts_SH ssv) in
  jafter_call_keep HS K regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1]%nat HS2 end.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply region_kept_aview; [ | | exact Hpres2].
    + cbn [base_val]. rewrite E8e. reflexivity.
    + intros a Ha. change (bv_unsigned (getr regs 2)) with (spZ regs) in Ha.
      apply Hkept; [unfold T_check_text_scribble, ESTACK in *; lia | unfold o, ESTACK in *; lia].
  - eapply region_kept_aview; [ | | exact Hpres2].
    + cbn [base_val]. rewrite E20. apply unsigned_lit_small. lia.
    + intros a Ha. apply Hkept; [lia |
        unfold o, coff_win, T_check_text_scribble, ESTACK in *; lia]. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (Hv0 : v = w64 0)
  by (apply Hcmp; intros i Hi; rewrite (HBch i Hi), (HBw i Hi), HAGR; reflexivity).
assert (HRA2 : range_addressable (aview tfibsegs (w_H W3) mem2) SHADOW_OFF ch 24).
{ intros x Hx. destruct (HRA3 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  assert (Hsx : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46).
  { unfold shadow_of_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
    pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  assert (Hwin : ~ (sp0 + o - 2 * ESTACK <= shadow_of_addr SHADOW_OFF x < sp0 + o)).
  { unfold o.
    change (~ (sp0 + (spZ regs3 - sp0) - 8192 <= shadow_of_addr SHADOW_OFF x < sp0 + (spZ regs3 - sp0))).
    lia. }
  rewrite (Hkept (shadow_of_addr SHADOW_OFF x) ltac:(lia) Hwin).
  rewrite (KR (shadow_of_addr SHADOW_OFF x) ltac:(lia)). exact Hsv. }
assert (SHOK2 : sh_ok tfibsegs CTS_Bx cts_SH (havoc (cts_E regs3 regs FL) 45 (map (getr regs2) CLOB))
  (mrestrict (w_H W3) mem2)).
{ unfold sh_ok, cts_SH. constructor; [|constructor].
  apply (cts_shent W3 mem2 _ ch HRA2 Hcham ltac:(lia) ltac:(lia)).
  - rewrite ew_havoc_old by lia. exact E20.
  - rewrite ew_havoc_old by lia. rewrite (cts_E_reg regs3 regs FL 23 23%bv eq_refl). exact Hs7. }
(* from the wrapper's return: the two tests and the fill loop, to the first store of the release *)
clear SHOK HS. rename HS2 into HS. rename SHOK2 into SHOK. clear HJ. rename HJ2 into HJ.
aj_run_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [cts_awr_ro | idtac].
cw_branch Hb.
{ (* the abort: a0 is the comparison's result, 0 since the texts agree *)
  exfalso. revert Hb.
  assert (Hr49 : ew (havoc (cts_E regs3 regs FL) 45 (map (getr regs2) CLOB)) 49 = getr regs2 10)
    by reflexivity.
  cbn [sv_denot]. rewrite Hr49, Hv, Hv0. vm_compute. discriminate. }
(* the texts agree: on to the fill loop and the release *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan 0x839dc; [cts_awr_ro | idtac].
cw_norm_model.
(* the release: the flag byte, the frame and its shadow come back as regions *)
pose proof HJ as (HAR1 & _).
destruct (FFL _ _ _ _ _ 0 fpos HAR1 HIN3) as (HFLp & HFLo & _ & (HFL0 & _ & HFLc)).
fold FL in HFLp, HFLo, HFL0, HFLc.
assert (HceilN : alloc_ceiling + 8352 <= spZ regs).
{ eapply Z.le_trans; [|apply Z.le_sub_le_add_r; exact Hceil0]. apply Z.eq_le_incl. f_equal. }

(* every byte outside the wrapper's stack window is the cut's at the release *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hw.
  rewrite (cw_kept_run (fun _ => False) _ _ (w_H W3) (ms_mem ms0) (ms_mem ms0) (ms_mem ms1)
    ltac:(intros; reflexivity) HFr1 ltac:(cts_wr_none) a Ha (fun x => x)).
  rewrite (cw_kept_run (fun _ => False) _ _ (w_H W3) mem2 mem2 (ms_mem ms0)
    ltac:(intros; reflexivity) HFr0 ltac:(cts_wr_none) a Ha (fun x => x)).
  rewrite (Hkept a Ha Hw). exact (KR a Ha). }
(* the frame and its shadow sit below the allocation ceiling and in the shadow band: outside the window *)
assert (KMf : forall a, (F <= a < F + 64 \/ shadow_addr F <= a < shadow_addr F + 8) ->
  aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. assert (HF8 : 0 <= F / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold shadow_addr, SHADOW_OFF in Ha.
  apply KM; [lia | unfold o; change (2 * ESTACK) with 8192; lia]. }
assert (HFLP1 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (F + 56) 8 FL).
{ apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 (ms_mem ms1) (F + 56) 8 FL); [|exact HFLP].
  intros x Hx. apply KMf. left. cbn in Hx. lia. }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  assert (E18c : ew Ev 18 = Z_to_bv 64 F) by (change (ew Ev 18) with (getr regs3 18); exact Hs2);
  assert (E32d : ew Ev 32 = Z_to_bv 64 FL) by reflexivity;
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (cw_frame_region 18 32 0) HS eq_refl
    (cw_frame_region_ok B LAWS FFL Ev 18 32 ly3 S3 W3 (ms_mem ms1) _ 0 fpos HAR1 HIN3 E18c E32d
      ltac:(change (fs_frame_bytes 0) with 64;
            replace (frame_addr ly3 0 fpos + 64 - 8) with (F + 56) by (unfold F; lia);
            apply (rdword_of_val_mem tfibsegs); [exact HFLP1 | lia]))) as HS1 end.
(* the frame is fresh: no byte of the record, not the flag byte, below the save area *)
assert (Efa : frame_addr ly3 0 fpos = frame_addr lyc 0 fpos).
{ pose proof HJ0 as (_ & Hly0 & _). pose proof HJ3 as (_ & Hly3 & _). unfold frame_addr.
  destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR1 HIN3) as (_ & _ & HFb & HFs).
change (fs_frame_bytes 0) with 64 in HFb, HFs. change (64 / 8) with 8 in HFs. fold F in HFb, HFs.
assert (HFch : F + 64 <= ch \/ ch + 24 <= F).
{ destruct (Z_lt_le_dec (Z.max F ch) (Z.min (F + 64) (ch + 24))) as [Hov|Hov]; [|lia]. exfalso.
  assert (HFz : cw_fresh B lyc Sc (Z.max F ch)).
  { eapply (cw_fresh_frame_j B LAWS FFL); [exact HJ0 | exact HJ | exact HP3 |].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Efa. fold F.
    change (fs_frame_bytes 0) with 64. lia. }
  destruct HFz as (_ & _ & HFbk & HFfr).
  destruct HOBJ as [(bb & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
  - exact (HFbk bb m (Z.max F ch - bb) Hin ltac:(lia) ltac:(lia)).
  - destruct (HFfr cid pos Hin) as (Hn1 & _). apply Hn1. unfold in_zr, frame_rng in *. cbn [fst snd] in *. lia. }
pose proof (cw_flag_apart B ly3 S3 FL F (F + 64) HFLo ltac:(intros a Ha; exact (proj2 (HFb a Ha)))) as HFLF.
lazymatch type of HS1 with ?P -> _ => assert (HD2 : P) end.
{ lazymatch goal with |- all_disjoint ?Ev _ _ =>
    assert (X8 : ew Ev 8 = getr regs3 8) by reflexivity;
    assert (X18 : ew Ev 18 = getr regs3 18) by reflexivity;
    assert (X20 : ew Ev 20 = getr regs3 20) by reflexivity;
    assert (X32 : ew Ev 32 = Z_to_bv 64 FL) by reflexivity end.
  cbn [ss_mem all_disjoint]. unfold cw_frame_region, cw_flag_region, extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
  rewrite ?X8, ?X18, ?X20, ?X32, ?Hs0, ?Hs2, ?Hs4. rewrite ?unsigned_lit_small by lia.
  change (bv_unsigned (getr regs 2)) with (spZ regs). change (fs_frame_bytes 0) with 64.
  repeat split; try exact I; lia. }
specialize (HS1 HD2). clear HD2.
(* the frame's shadow, as the frame setup left it *)
assert (HSH1 : forall j, (j < 8)%nat -> val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1))
  (shadow_addr F + Z.of_nat j) 1 (nth j cts_shm_live 0)).
{ intros j Hj. apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 (ms_mem ms1) _ 1 _);
    [| exact (proj1 (HFSH j ltac:(cbn [length cts_shm_live]; lia)))].
  intros x Hx. apply KMf. right. cbn in Hx. lia. }
lazymatch type of HS1 with st_ok _ ?Ev ?ssv ?msv =>
  assert (E24c : ew Ev 24 = Z_to_bv 64 (shadow_addr F))
    by (change (ew Ev 24) with (getr regs3 24); exact Hs8);
  assert (HRsh : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem ms1)) cts_fsh_region);
  [ unfold region_ok, cts_fsh_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    assert (HF8 : 0 <= F / 8 < 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
    rewrite E24c, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia);
    split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split;
    [ intros oo Hoo; apply (apresent_writable tfibsegs); exact (proj1 (HFs oo ltac:(lia)))
    | apply Forall_forall; intros c Hc; apply in_map_iff in Hc as (j & <- & Hj); apply in_seq in Hj;
      apply cts_chunk1; [destruct (HFSH j ltac:(cbn [length cts_shm_live]; lia)) as (_ & Hr); exact Hr
                        | exact (HSH1 j ltac:(lia))] ]
  | pose proof (ast_ok_add_region tfibsegs Ev ssv msv cts_fsh_region HS1 eq_refl HRsh) as HS2 ] end.
pose proof (cw_flag_apart B ly3 S3 FL (shadow_addr F) (shadow_addr F + 8) HFLo
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by lia;
        exact (proj2 (HFs (a - shadow_addr F) ltac:(lia))))) as HFLS.
assert (HF8t : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HF80 : 0 <= F / 8) by (apply Z.div_pos; lia).
lazymatch type of HS2 with ?P -> _ => assert (HD3 : P) end.
{ lazymatch goal with |- all_disjoint ?Ev _ _ =>
    assert (X8 : ew Ev 8 = getr regs3 8) by reflexivity;
    assert (X18 : ew Ev 18 = getr regs3 18) by reflexivity;
    assert (X20 : ew Ev 20 = getr regs3 20) by reflexivity;
    assert (X24 : ew Ev 24 = getr regs3 24) by reflexivity;
    assert (X32 : ew Ev 32 = Z_to_bv 64 FL) by reflexivity end.
  cbn [ss_mem all_disjoint]. unfold cts_fsh_region, cw_frame_region, cw_flag_region, extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
  rewrite ?X8, ?X18, ?X20, ?X24, ?X32, ?Hs0, ?Hs2, ?Hs4, ?Hs8.
  rewrite ?unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
  change (bv_unsigned (getr regs 2)) with (spZ regs). change (fs_frame_bytes 0) with 64.
  unfold shadow_addr, SHADOW_OFF in *.
  repeat split; try exact I; lia. }
specialize (HS2 HD3). clear HD3.
lazymatch type of HS2 with st_ok _ ?Ev ?ssv ?msv =>
  assert (E32c : ew Ev 32 = Z_to_bv 64 FL) by reflexivity;
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (cw_flag_region 32) HS2 eq_refl
    (cw_flag_region_ok B FFL Ev 32 ly3 S3 W3 (ms_mem ms1) _ 0 fpos HAR1 HIN3 E32c)) as HS3 end.
(* the flag byte is the fresh frame's, so it is no byte of the record (a caller object) *)
assert (Efl : flag_addr ly3 0 fpos = flag_addr lyc 0 fpos).
{ pose proof HJ0 as (_ & Hly0 & _). pose proof HJ3 as (_ & Hly3 & _). unfold flag_addr.
  destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
assert (HFLf : cw_fresh B lyc Sc FL).
{ eapply (cw_fresh_frame_j B LAWS FFL); [exact HJ0 | exact HJ | exact HP3 |].
  right. right. exact Efl. }
assert (HFLch : FL + 1 <= ch \/ ch + 24 <= FL).
{ destruct (Z_lt_le_dec FL ch) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec FL (ch + 24)) as [Hh|Hh]; [|right; lia]. exfalso.
  destruct HFLf as (_ & _ & HFLb & HFf).
  destruct HOBJ as [(bb & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
  - exact (HFLb bb m (FL - bb) Hin ltac:(lia) ltac:(lia)).
  - destruct (HFf cid pos Hin) as (Hn1 & _). apply Hn1. unfold in_zr, frame_rng in *. cbn [fst snd] in *. lia. }
lazymatch type of HS3 with ?P -> _ => assert (HD1 : P) end.
{ lazymatch goal with |- all_disjoint ?Ev _ _ =>
    assert (X8 : ew Ev 8 = getr regs3 8) by reflexivity;
    assert (X18 : ew Ev 18 = getr regs3 18) by reflexivity;
    assert (X20 : ew Ev 20 = getr regs3 20) by reflexivity;
    assert (X24 : ew Ev 24 = getr regs3 24) by reflexivity;
    assert (X32 : ew Ev 32 = Z_to_bv 64 FL) by reflexivity end.
  cbn [ss_mem all_disjoint]. unfold cts_fsh_region, cw_frame_region, cw_flag_region, extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
  rewrite ?X8, ?X18, ?X20, ?X24, ?X32, ?Hs0, ?Hs2, ?Hs4, ?Hs8.
  rewrite ?unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
  change (bv_unsigned (getr regs 2)) with (spZ regs). change (fs_frame_bytes 0) with 64.
  unfold shadow_addr, SHADOW_OFF in *.
  repeat split; try exact I; lia. }
specialize (HS3 HD1). clear HD1.
(* the release run, to ret *)
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E32n : ew Ev 32 = Z_to_bv 64 FL) by reflexivity;
  assert (E24n : ew Ev 24 = Z_to_bv 64 (shadow_addr F)) by (change (ew Ev 24) with (getr regs3 24); exact Hs8);
  assert (E18n : ew Ev 18 = Z_to_bv 64 F) by (change (ew Ev 18) with (getr regs3 18); exact Hs2) end.
assert (HF8b : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (E32b : ew (cts_E regs3 regs FL) 32 = Z_to_bv 64 FL) by reflexivity.
aj_run_flag_sh tfibtbl_lib_ok HS HJ;
[ lia
| eapply (cw_awrf_flag_front _ _ _ _ _ _ _ _ _ _ 32%nat);
  [ reflexivity
  | rewrite E32n, unsigned_lit_small by lia; reflexivity
  | cbn; lia | cbn; lia
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 fpos 24%nat);
    [ reflexivity
    | rewrite E24n, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia); reflexivity
    | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0 / 8) with 8; lia
    | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 fpos 18%nat);
      [ reflexivity | rewrite E18n, unsigned_lit_small by lia; reflexivity
      | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0) with 64; lia
      | cts_awr_ro ] ] ]
| flag0 E32b (eq_sym Efl)
| idtac ].
cw_norm_model.
(* every byte the release run wrote is a byte of the fresh frame, its shadow or its flag *)
lazymatch goal with HFr2 : frame_of ?Ev ?rs (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
  assert (X18 : ew Ev 18 = getr regs3 18) by reflexivity;
  assert (X24 : ew Ev 24 = getr regs3 24) by reflexivity;
  assert (X32 : ew Ev 32 = Z_to_bv 64 FL) by reflexivity;
  assert (X8 : ew Ev 8 = getr regs3 8) by reflexivity;
  assert (X20 : ew Ev 20 = getr regs3 20) by reflexivity;
  assert (HXr : forall a, in_wrange Ev rs a -> cw_fresh B lyc Sc a);
  [ intros a (r & Hr & Hwb);
    lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hwb;
        rewrite ?X18, ?X24, ?X32, ?X8, ?X20, ?Hs2, ?Hs8, ?Hs0, ?Hs4 in Hwb;
        rewrite ?unsigned_lit_small in Hwb by (unfold shadow_addr, SHADOW_OFF; lia);
        first
        [ lia
        | eapply (cw_fresh_frame_j B LAWS FFL); [exact HJ0 | exact HJ3 | exact HP3 |];
          unfold frame_rng, in_zr; cbn [fst snd]; rewrite <- Efa; fold F;
          change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64;
          first [ left; lia | right; left; lia | right; right; rewrite <- Efl; fold FL; lia ] ]
      | ]);
    destruct Hr
  | ] end.
(* the kept invariant at the return: one step from the cut's, over the wrapper's window and the release *)
pose proof HJ0 as (HAR0 & _).
lazymatch goal with HFr2 : frame_of ?Ev ?rs (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
  assert (KK : tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W3 (ms_mem ms2) (spZ regs)
    (fun x => ch <= x < ch + 24));
  [ apply (cw_kept_step B LAWS T_check_text_scribble lyc Sc W memc mdc W3 mem3 (ms_mem ms2) (spZ regs)
      (fun x => ch <= x < ch + 24) (fun a => (sp0 + o - 2 * ESTACK <= a < sp0 + o) \/ in_wrange Ev rs a));
    [ exact Hceil0
    | exact HAR0
    | exact HKEPT
    | intros a Ha HnX;
      rewrite (cw_kept_run (in_wrange Ev rs) Ev rs (w_H W3) (ms_mem ms1) (ms_mem ms1) (ms_mem ms2)
        ltac:(intros; reflexivity) HFr2 (fun a H => H) a Ha ltac:(intros Hx; apply HnX; right; exact Hx));
      apply KM; [exact Ha | intros Hx; apply HnX; left; exact Hx]
    | intros a [Hw | Hr];
      [ left; unfold o in Hw; change (2 * ESTACK) with 8192 in Hw;
        change T_check_text_scribble with 8352; lia
      | right; right; exact (HXr a Hr) ]
    | intros a Hp; eapply apresent_grows; [exact HG2|]; eapply apresent_grows; [exact HG1|];
      eapply apresent_grows; [exact HG0|]; apply Hpres2; eapply apresent_grows; [exact HG | exact Hp] ]
  | ] end.
(* the ret leaf *)
lazymatch goal with HSx : st_ok _ ?Ex _ (restrict (w_H W3) ms2) |- _ =>
  rreg HSx (1%bv : bv 5) R1;
  eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W3 Ex); [exact HSx | reflexivity | vm_compute; reflexivity |] end.
intros matx.
red. exists ly3, (stack_free_state 0 fpos S3), (ms_regs ms2), (ms_mem ms2). eexists.
assert (Rra : getr (ms_regs ms2) 1 = getr regs 1)
  by (rewrite R1; change (ew (cts_E regs3 regs FL) 33) with (Z_to_bv 64 (bv_unsigned (getr regs 1)));
      apply Z_to_bv_bv_unsigned).
split; [rewrite Rra, HraE; reflexivity|].
split; [unfold EV_CDC; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|].
(* every callee-saved register is the entry's: the epilogue put back the saves, gp / tp / s11 untouched *)
assert (HPRES : aregs_preserved regs (ms_regs ms2)).
{ lazymatch goal with HSx : st_ok _ _ _ (restrict (w_H W3) ms2) |- _ =>
    rreg HSx (2%bv : bv 5) P2;
    rreg HSx (3%bv : bv 5) P3;
    rreg HSx (4%bv : bv 5) P4;
    rreg HSx (8%bv : bv 5) P8;
    rreg HSx (9%bv : bv 5) P9;
    rreg HSx (18%bv : bv 5) P18;
    rreg HSx (19%bv : bv 5) P19;
    rreg HSx (20%bv : bv 5) P20;
    rreg HSx (21%bv : bv 5) P21;
    rreg HSx (22%bv : bv 5) P22;
    rreg HSx (23%bv : bv 5) P23;
    rreg HSx (24%bv : bv 5) P24;
    rreg HSx (25%bv : bv 5) P25;
    rreg HSx (26%bv : bv 5) P26;
    rreg HSx (27%bv : bv 5) P27 end.
  intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat destruct Hc as [-> | Hc]; [ | | | | | | | | | | | | | | subst r].
  all: (etransitivity; [
    first [exact P2 | exact P3 | exact P4 | exact P8 | exact P9 | exact P18 | exact P19 | exact P20 | exact P21
          | exact P22 | exact P23 | exact P24 | exact P25 | exact P26 | exact P27] |]).
  - exact Hs0.
  - exact (eq_trans Hgp3 (eq_sym HgpE)).
  - exact (eq_trans Htp3 (eq_sym HtpE)).
  - change (ew (cts_E regs3 regs FL) 34) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 8))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 35) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 9))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 36) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 18))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 37) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 19))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 38) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 20))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 39) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 21))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 40) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 22))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 41) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 23))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 42) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 24))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 43) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 25))));
    apply Z_to_bv_bv_unsigned.
  - change (ew (cts_E regs3 regs FL) 44) with (Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 26))));
    apply Z_to_bv_bv_unsigned.
  - exact Hs11. }
split; [exact HPRES|].
rename HP3 into P3. rename HM3 into M3.
split; [eapply cw_frames_back; [| exact HJ]; eassumption|].
split; [apply cw_perm_release; assumption|].
pose proof (same_io_materialized _ _ Hsame) as HIOb.
split; [cw_io|].
split; [apply (cw_mo_le_release _ MTF); assumption|].
split; [exact KK|].
(* the result: the record is in no write set of the tail, so it holds the cut's bytes *)
assert (HRECf : forall a, ch <= a < ch + 24 ->
  aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha.
  lazymatch goal with HFr2 : frame_of ?Ev ?rs (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
    rewrite (cw_kept_run (in_wrange Ev rs) Ev rs (w_H W3) (ms_mem ms1) (ms_mem ms1) (ms_mem ms2)
      ltac:(intros; reflexivity) HFr2 (fun a H => H) a ltac:(lia)
      ltac:(intros Hx; pose proof (HXr a Hx) as Hfa; destruct Hfa as (_ & _ & Hfb & Hff);
            destruct HOBJ as [(bb & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)];
            [ exact (Hfb bb m (a - bb) Hin ltac:(lia) ltac:(lia))
            | destruct (Hff cid pos Hin) as (Hn1 & _); apply Hn1;
              unfold in_zr, frame_rng in *; cbn [fst snd] in *; lia ])) end.
  apply KM; [lia | unfold o, coff_win in *; change (2 * ESTACK) with 8192;
                   change T_check_text_scribble with 8352 in Hchoff; lia]. }
unfold codec_owe.scribble_bytes. rewrite HAGR.
intros j Hj. destruct (HREC j Hj) as (Hvj & Hrj). split; [|exact Hrj].
apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 (ms_mem ms2) _ 1 _); [|exact Hvj].
intros x Hx. apply HRECf. rewrite app_length, repeat_length, HLEN in Hj. cbn in Hx. lia.
Qed.
End d.
End b.
