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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths and module names changed; 108 of its 189 lines of code are new or changed and 1008 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 4c23b042570d for reac-pw/fuzz_rate's
   image A: module paths changed; role's RPgSeg / RPgMem vocabulary (e_R, e_F, e_pp, e_src, e_left, rl_inw, rm_) becomes
   rate's (q_R, q_F, q_pp, q_src, q_left, rt_inw, rtm_); the segment pre is rate's rt_seg_pre, which does not carry the
   frame's prologue shadow, so rs_wr_shadow and rs_in_now take it as a premise (rs_start_M01 gives it); the image's
   first write range hi_w1 has six ranges; the frame's shadow pattern has 56 bytes; the real frame is 0x1e0 bytes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6cKit.v at 88912827c774 for the same unit's
   image B (fuzz_rate.asan-ubsan): Part 1 only, over lib/AU/RtPgSegB.v's cut vocabulary (rsb_) and lib/AU/RtPgMemB.v's
   lemmas (rtmb_); the names become w6k_; the frame for locals is class 4 (1024 bytes), the real frame 0x220 bytes, the
   frame's prologue shadow pattern hi_shA rate_himg_B has 88 bytes, and hi_w1 is RtPgImgB's six ranges. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the kit of the walk piece
   "ent_build A" of LLVMFuzzerTestOneInput (0x8076c). Proves no function (kind: segment lemma).

   A SEGMENT'S START FACTS AT A CUT. rate_build_contract states the input bytes, their shadow bytes and the read-only
   data at the segment's start memory (RtPgSegB rsb_in, rsb_pre); a piece runs at a cut's memory. w6k_in_now and
   w6k_rom_now carry them across what the segment may have written (RtPgSegB rsb_core: every byte outside the
   callees' stack [R - T_SEG_STK, R) and outside rsb_E1 is the start's), with RtPgMemB section 7's address facts:
   the input's shadow bytes lie in the shadow band, so outside F, pp, R's cells and the stack; they are outside
   [shF, shF + 88) because every byte of the prologue's pattern hi_shA is >= 8 and the input is addressable at the
   start; the 8-aligned hull of those shadow bytes may reach into [shF, shF + 88), which every cut keeps present
   (its rsb_fsh_at). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== start facts at a cut ===================================== *)
(* what a cut may have changed since the segment's start: outside [0, 2^64), the callees' stack, rsb_E1 *)
Definition w6k_wr (cx : rsb_scx segs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (q_R (x_e segs cx) - T_SEG_STK <= a < q_R (x_e segs cx)) \/ rsb_E1 segs cx a.

(* the address facts of the segment's start: R above the shadow band, F and pp in the application's memory *)
Lemma w6k_pre_geom : forall cx, rsb_pre segs B cx ->
spZ (x_regs segs cx) = q_R (x_e segs cx) /\
kHighMemBeg <= q_R (x_e segs cx) - T_SEG_STK /\ q_R (x_e segs cx) + 0x220 <= 2 ^ 47 /\
In (4, x_pos segs cx) (frames (x_Sc segs cx)) /\ q_F (x_e segs cx) = frame_addr (x_lyc segs cx) 4 (x_pos segs cx) /\
in_app (q_F (x_e segs cx)) 1024 /\ q_F (x_e segs cx) mod 32 = 0 /\
in_app (q_pp (x_e segs cx)) Layout.PP_SIZE.
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos] HP.
unfold rsb_pre, rt_seg_pre in HP.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_RLO x_RHI x_e x_pos] in *.
destruct HP as (HJ & _ & Hsp & _ & _ & HeS & HR16 & HRS & HSTK & Hown & HF & _ & Hpp & _).
cbn [hi_cid hi_rsz rate_himg_B] in *.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
pose proof alloc_ceiling_value as (Hc1 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok segs B) lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & HFapp & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) lyc Sc W memc mdc (q_pp e) Layout.PP_SIZE HAR Hpp) as (_ & _ & _ & Happ & _).
change (fs_frame_bytes 4) with 1024 in HFapp. rewrite <- HF in HFapp, HF32.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Happ by reflexivity.
assert (HR0 : 0 <= q_R e < 2 ^ 64) by (unfold T_SEG_STK, ASTACK in HSTK; unfold kHighMemBeg; lia).
split; [unfold spZ; rewrite Hsp; unfold w64; apply unsigned_lit_small; lia|].
split; [unfold T_SEG_STK, ASTACK in *; unfold kHighMemBeg; lia|].
split; [lia|].
split; [exact Hin4|]. split; [exact HF|]. split; [exact HFapp|]. split; [exact HF32 | exact Happ].
Qed.

Lemma w6k_core_kept : forall cx ly2 S2 W2 regs2 mem2 md2,
rsb_pre segs B cx -> rsb_core segs B MT cx (rsb_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ w6k_wr cx a -> aview segs (w_H W2) mem2 a = aview segs (w_H (x_W segs cx)) (x_memc segs cx) a.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
destruct (w6k_pre_geom cx HP) as (Hsp & _).
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold w6k_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in rsb_E1 or the callees' stack *)
Lemma w6k_wr_shadow : forall cx x, rsb_pre segs B cx ->
rt_fsh segs (w_H (x_W segs cx)) (x_memc segs cx) (q_F (x_e segs cx)) (hi_shA rate_himg_B) ->
0 <= x < kHighMemEnd ->
range_addressable (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) SHADOW_OFF x 1 ->
~ w6k_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hfsh Hx Hra.
destruct (w6k_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
pose proof (rtmb_shadow_band x Hx) as Hb.
pose proof (rtmb_ra_not_fsh segs _ _ _ _ x 1 Hra Hfsh rtmb_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length (hi_shA rate_himg_B))) with 88 in Hnf.
unfold w6k_wr, rsb_E1, rt_inw. cbn [hi_w1 rate_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in *. lia.
- apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
  + apply (rtmb_shadow_not_app x (q_F (x_e segs cx)) 1024 Hx HFapp). lia.
  + apply Hnf. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply (rtmb_shadow_not_app x (q_pp (x_e segs cx)) Layout.PP_SIZE Hx Happ). exact H.
Qed.

Lemma w6k_in_now : forall cx rest pat ly2 S2 W2 regs2 mem2 md2,
rsb_pre segs B cx -> rt_fsh segs (w_H (x_W segs cx)) (x_memc segs cx) (q_F (x_e segs cx)) (hi_shA rate_himg_B) ->
rsb_in segs cx rest -> rsb_core segs B MT cx (rsb_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
rsb_fsh_at segs cx W2 mem2 pat -> length pat = 88%nat ->
garr8 segs (mrestrict (w_H W2) mem2) (q_src (x_e segs cx)) (rsb_u8s rest) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (q_src (x_e segs cx)) (q_left (x_e segs cx)) /\
(0 < q_left (x_e segs cx) -> shadow_hull_vis (aview segs (w_H W2) mem2) (q_src (x_e segs cx)) (q_left (x_e segs cx))).
Proof.
intros cx rest pat ly2 S2 W2 regs2 mem2 md2 HP Hfsh0 HI HC Hfsh2 Hpat.
pose proof (w6k_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (w6k_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := q_src (x_e segs cx)) in *. set (n := q_left (x_e segs cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (rtmb_bytes_kept_wr segs (w6k_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. rewrite <- Hleft in Hx'. fold n in Hx'. destruct (Hdisj x Hx') as (D1 & D2 & D3).
  unfold w6k_wr, rsb_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- split.
  + apply (rtmb_ra_kept_wr segs (w6k_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
    intros x Hx'. apply w6k_wr_shadow; [exact HP | exact Hfsh0 | exact (Hx x Hx') |].
    apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
  + intros Hn. apply (rtmb_hull_kept segs _ _ _ _ src n (Hhull Hn)).
    intros s Hs Hnone.
    destruct (base.decide (w6k_wr cx s)) as [Hw|Hw].
    2:{ rewrite (HK s Hw). exact Hnone. }
    assert (Hsb : SHADOW_OFF <= s < kHighMemBeg).
    { pose proof (Hx src ltac:(lia)). pose proof (Hx (src + n - 1) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
      pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)).
      assert (2147450880 <= (2147450880 + src / 8) / 8 * 8).
      { assert (268431360 <= (2147450880 + src / 8) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert ((src + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      assert ((2147450880 + (src + n - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    unfold w6k_wr, rsb_E1, rt_inw in Hw. cbn [hi_w1 rate_himg_B] in Hw.
    destruct Hw as [H|[H|[H|H]]].
    * exfalso. unfold SHADOW_OFF, kHighMemBeg in Hsb. lia.
    * exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
      -- exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      -- unfold rsb_fsh_at, rt_fsh in Hfsh2. rewrite Hpat in Hfsh2.
         replace s with (shadow_addr (q_F (x_e segs cx)) + (s - shadow_addr (q_F (x_e segs cx)))) by lia.
         rewrite (Hfsh2 (s - shadow_addr (q_F (x_e segs cx))) ltac:(cbn; lia)). discriminate.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* rom_view at a cut: the image lies below the shadow band, outside every block and frame *)
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma w6k_rom_now : forall cx ly2 S2 W2 regs2 mem2 md2,
rsb_pre segs B cx -> rsb_core segs B MT cx (rsb_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 -> rom_view segs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
pose proof (w6k_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (w6k_pre_geom cx HP) as (_ & HRk & _ & Hin4 & HF & HFapp & _ & Happ).
assert (Hrom : rom_view segs (x_W segs cx) (x_memc segs cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAR : AR segs B (x_lyc segs cx) (x_Sc segs cx) (x_W segs cx) (x_memc segs cx) (x_mdc segs cx)).
{ destruct HP as (HJ & _). exact (proj1 HJ). }
assert (Hpp : In (q_pp (x_e segs cx), Layout.PP_SIZE) (ablocks B (x_lyc segs cx) (x_Sc segs cx))).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
apply (rtmb_rom_kept_wr segs (w6k_wr cx) (x_W segs cx) W2 (x_memc segs cx) mem2 Hrom HK).
intros a (sg & Hsg & _ & Ha). assert (Himg : in_img segs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (segs_low a Himg) as Hlow.
pose proof (al_client_img _ _ (AR_laws_ok segs B) _ _ _ _ _ a HAR) as Hcl.
unfold w6k_wr, rsb_E1, rt_inw. cbn [hi_w1 rate_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd in Hlow. lia.
- unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
  + assert (HinF : frame_addr (x_lyc segs cx) 4 (x_pos segs cx) <= a <
      frame_addr (x_lyc segs cx) 4 (x_pos segs cx) + fs_frame_bytes 4)
      by (rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia).
    apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 4 (ex_intro _ (x_pos segs cx) (conj Hin4 HinF))))))).
    exact Himg.
  + unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (q_F (x_e segs cx)) 8). unfold in_app in HFapp. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- assert (Hinp : q_pp (x_e segs cx) <= a < q_pp (x_e segs cx) + req_size Layout.PP_SIZE)
    by (change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia).
  apply (proj2 (Hcl (or_introl (ex_intro _ (q_pp (x_e segs cx)) (ex_intro _ Layout.PP_SIZE (conj Hpp Hinp)))))).
  exact Himg.
Qed.

End d.
End c.
End b.

Print Assumptions w6k_in_now.
Print Assumptions w6k_rom_now.
