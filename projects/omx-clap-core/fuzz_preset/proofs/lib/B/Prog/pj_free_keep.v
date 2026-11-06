(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: WHAT A CALL KEEPS in pj_free's image-B walk (lib/B/Prog/pj_free_defs.v): the facts the loop
   and tail segments carry across a callee (the recursive pj_free, fuzz_free) from the callee's journal (YCbqG.v
   ajournal_xR at any world relation R1, own = []: after a free it is at wle', YA0nH.v) and the allocator laws at the
   return state:
   - pfk_hblk (ONE COPY, lib/A/Prog/PjFreeCommon.v, with pfk_nohead): a byte of a harness block live before and after,
     outside the callee's footprint, is kept, and present after; a fake frame holding a node is a multiple of 8 bytes
     by lib/A/Prog/PjStringCommon.v pjs1_fsb8;
   - pfk_vnode: v's node facts (pf_vnode) at the return state (v apart from the footprint, v's place never freed);
   - pfk_items: the slots still to free (pf_oitemsR) at the return state (their bytes in harness blocks live before and
     after, outside the footprint);
   - pfk_frame: pj_free's frame (pf_frameR at any world relation R, pf_spill) at the return state, from the caller's
     composed journal at R and the callee's journal at the callee window below sp1 + 8;
   - pfk_acct_free / pfk_acct_null / pfk_acct_rec: the accounts (pf_acct) after a fuzz_free of the next block, a
     fuzz_free (NULL), a recursive pj_free of the next subtree.
   proves no function (kind: walk glue).
   Section hypotheses: AR_laws_x at head length cf_head; ARx_frame_hull_vis (YGcfFsVis.v, a MARKED kit fact the
   instance discharges by ARx_frame_hull_vis_cf_ok, as pj_parse_defs.v pjp_g_vis). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Existing Instance prh_img_B.
Open Scope bv_scope.
Open Scope Z_scope.

(* the saved-register slots lie in [sp1 + 24, sp1 + 128) *)
Lemma pfk_saved_rng : forall r o, In (r, o) PJF_SAVED -> 24 <= o <= 120.
Proof.
intros r o H. unfold PJF_SAVED in H.
repeat (destruct H as [H|H]; [injection H as _ <-; lia|]). destruct H.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- v's node at the return state ---- *)
Lemma pfk_vnode : forall (R1 : world SEGS -> world SEGS -> Prop)
    en nd ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1
    peak cnt fail ran most own peak2 cnt2 fail2 ran2 most2 own2,
  pf_vnode B en nd ly S Lam W mem ->
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ajournal_xR (SK := SK) SEGS B PST ARx R1 STK1 sp1 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (* the callee writes nothing of v's node *)
  (forall x, inFP FP1 x -> ~ (fe_v en <= x < fe_v en + 56)) ->
  (* the callee frees only blocks of D still in the ledger, and leaves every other ledger block *)
  (forall b, In b (ablocks B ly S) -> ~ In b (ablocks B ly2 S2) ->
     exists a k, In (a, k) (fe_D en) /\ In (a, k) Lam /\ b = (a - cf_head, k + cf_head)) ->
  (forall a k, In (a, k) Lam -> ~ In (a, k) (fe_D en) -> In (a, k) Lam2) ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam) ->
  (* the caller's window lies above alloc_ceiling (pf_pre's astk_ok), and every byte of the footprint is a byte of a
     block live at the call (so no shadow cell of v is in it) *)
  YM05.alloc_ceiling <= fe_sp0 en ->
  (forall x, inFP FP1 x -> exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) ->
  pf_vnode B en nd ly2 S2 Lam2 W2 mem2.
Proof.
intros R1 en nd ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran most own
  peak2 cnt2 fail2 ran2 most2 own2
  HV HAR HL HJ HL2 HFPv HFREE HKEEP HSUB HSP HFPb.
unfold pf_vnode in HV |- *. cbv zeta in HV |- *.
destruct HV as (H4096 & Hceil & Hal8 & Hamr & Rs & Rk & Ry & Rn & _ & _ & Hra & _ & Hplace).
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_blk HJ) as J2. pose proof (ajxR_frm HJ) as J4. clear HJ.
pose proof (@cf_head_nonneg cp) as Hc0.
assert (DZ : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HNF : forall x, fe_v en <= x < fe_v en + 56 -> ~ inFP FP1 x) by (intros x Hx Hf; exact (HFPv x Hf Hx)).
(* a shadow cell of v's bytes is no application address, so no byte of a live block *)
assert (HFPs : forall x, fe_v en <= x < fe_v en + 56 -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx Hf. destruct (HFPb _ Hf) as (b & m & Hbm & Hbx).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & _ & _ & Happ & _).
  pose proof (in_app_addr b (req_size m) _ Happ Hbx) as Ha.
  pose proof asan_consts as (C1 & _ & C3 & _ & _).
  unfold app_addr, shadow_of_addr, kLowShadowBeg, ASAN_CEIL in Ha. unfold SHADOW_OFF in Ha. lia. }
assert (X : (forall x, fe_v en <= x < fe_v en + 56 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x /\
    apresent (w_H W2) mem2 x /\ ~ aowned B ly2 S2 x) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (fe_v en) 56 /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) (fe_v en) 56 /\
  ((exists a k, In (a, k) Lam2 /\ ~ In (a, k) (fe_D en) /\ a <= fe_v en /\ fe_v en + 56 <= a + k) \/
   (exists b m, In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam2 /\ b <= fe_v en /\
      fe_v en + 56 <= b + m) \/
   (exists cid pos, In (cid, pos) (frames S2) /\
      frame_addr ly2 cid pos <= fe_v en /\ fe_v en + 56 <= frame_addr ly2 cid pos + fs_frame_bytes cid) \/
   (fe_sp0 en <= fe_v en /\ fe_v en + 56 <= fe_sp0 en + fe_d en))).
{ destruct Hplace as [(a & k & HaL & HaD & Hav & Hvk) | [(b & m & Hbm & HnL & Hbv & Hvm) |
    [(cid & pos & Hcp & Hf1 & Hf2) | (Hs0 & _)]]].
  - (* in a harness block the callee does not free: the block shadow law of its user range *)
    pose proof (HKEEP a k HaL HaD) as HaL2.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL HaL) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 a k most2 own2 HL2 HaL2) as (_ & Hab2 & Hhp2 & _).
    pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [_ Rk'].
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hby2 & _).
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2 Hhp2) as [Hbs Hbh].
    split; [|split; [|split]].
    + intros x Hx. split; [|exact (Hby2 x ltac:(lia))].
      pose proof (J2 (a - @cf_head cp) (k + @cf_head cp) (x - (a - @cf_head cp)) Hab Hab2 ltac:(lia)) as E.
      replace (a - cf_head + (x - (a - cf_head))) with x in E by lia. exact (E (HNF x Hx)).
    + exact (block_shadow_range _ SHADOW_OFF (a - @cf_head cp + @cf_head cp) (req_size (k + @cf_head cp) - @cf_head cp)
        (fe_v en) 56 Hbs ltac:(lia) ltac:(lia)).
    + exact (shadow_hull_vis_sub_cf _ (a - @cf_head cp + @cf_head cp) (req_size (k + @cf_head cp) - @cf_head cp)
        (fe_v en) 56 (Hbh ltac:(lia)) ltac:(lia) ltac:(lia)).
    + left. exists a, k. auto.
  - (* in an allocator block that is no harness block: the callee does not free it; no hidden head in it *)
    assert (Hbm2 : In (b, m) (ablocks B ly2 S2)).
    { destruct (in_dec DZ (b, m) (ablocks B ly2 S2)) as [Hi|Hn]; [exact Hi|]. exfalso.
      destruct (HFREE (b, m) Hbm Hn) as (a & k & _ & HaL & E). injection E as -> ->. apply HnL.
      replace (a - cf_head + cf_head) with a by lia. replace (k + cf_head - cf_head) with k by lia. exact HaL. }
    assert (HnL2 : ~ In (b + cf_head, m - cf_head) Lam2) by (intros Hi; exact (HnL (HSUB _ _ Hi))).
    pose proof (req_size_pos m ltac:(lia)) as [_ Rm].
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2) as (_ & _ & _ & _ & Hby2 & _).
    destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2
      (pfk_nohead B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b m HAR2 HL2 Hbm2 HnL2)) as [Hbs Hbh].
    split; [|split; [|split]].
    + intros x Hx. split; [|exact (Hby2 x ltac:(lia))].
      pose proof (J2 b m (x - b) Hbm Hbm2 ltac:(lia)) as E.
      replace (b + (x - b)) with x in E by lia. exact (E (HNF x Hx)).
    + exact (block_shadow_range _ SHADOW_OFF b (req_size m) (fe_v en) 56 Hbs ltac:(lia) ltac:(lia)).
    + exact (shadow_hull_vis_sub_cf _ b (req_size m) (fe_v en) 56 Hbh ltac:(lia) ltac:(lia)).
    + right; left. exists b, m. auto.
  - (* in a caller's fake frame: the journal's frame clause keeps its bytes and its shadow cells *)
    assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hcp).
    assert (Efa : frame_addr ly2 cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hf0 & Hfc & _).
    destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hfal & _).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfown & _).
    rewrite Efa in Hfown.
    pose proof (VISF ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as Hfh. rewrite Efa in Hfh.
    pose proof (PjStringCommon.pjs1_fsb8 cid ltac:(lia)) as Hfs8.
    split; [|split; [|split]].
    + intros x Hx. split; [|exact (Hfown x ltac:(lia))].
      apply (J4 cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HNF x Hx)].
    + eapply range_addressable_agree; [|exact Hra]. intros x Hx.
      apply (J4 cid pos); [exact Hcp | right | exact (HFPs x Hx)].
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      assert (Hfa8 : frame_addr ly cid pos mod 8 = 0) by lia.
      lia.
    + exact (shadow_hull_vis_sub_cf _ _ _ (fe_v en) 56 Hfh ltac:(lia) ltac:(lia)).
    + right; right; left. exists cid, pos. rewrite Efa. auto.
  - (* in the caller's window: above alloc_ceiling, so not v's place *)
    exfalso. lia. }
destruct X as (K & Hra2 & Hhv2 & Hpl2).
split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hal8|]. split; [exact Hamr|].
split; [apply (pfg_u64_keep W W2 mem mem2 _ _ Rs); intros x Hx; exact (proj1 (K x ltac:(lia)))|].
split; [apply (pfg_u64_keep W W2 mem mem2 _ _ Rk); intros x Hx; exact (proj1 (K x ltac:(lia)))|].
split; [apply (pfg_u64_keep W W2 mem mem2 _ _ Ry); intros x Hx; exact (proj1 (K x ltac:(lia)))|].
split; [apply (pfg_u64_keep W W2 mem mem2 _ _ Rn); intros x Hx; exact (proj1 (K x ltac:(lia)))|].
split; [split; [exact Hal8 | intros x Hx; apply (apresent_writable SEGS); exact (proj1 (proj2 (K x Hx)))]|].
split; [intros a Ha; exact (proj2 (proj2 (K a Ha)))|].
split; [exact Hra2|]. split; [exact Hhv2|]. exact Hpl2.
Qed.

(* ---- the slots still to free at the return state: their bytes lie in harness blocks live before and after, outside
   the callee's footprint ---- *)
Lemma pfk_items : forall (R1 : world SEGS -> world SEGS -> Prop)
    d ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1
    peak cnt fail ran most own peak2 cnt2 fail2 ran2 most2 own2 ks a ka n Dr Fr,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ajournal_xR (SK := SK) SEGS B PST ARx R1 STK1 sp1 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d) ks a ka n Dr Fr ->
  (forall x, pf_ofoot ks a ka n Dr x ->
     ~ inFP FP1 x /\ exists a' k', In (a', k') Lam /\ In (a', k') Lam2 /\ a' <= x < a' + k') ->
  (forall x k, In (x, k) Dr -> In (x, k) Lam2) ->
  pf_oitemsR SEGS (rdW W2 mem2) (prh_lin Lam2) (pj_foR SEGS (rdW W2 mem2) (prh_lin Lam2) d) ks a ka n Dr Fr.
Proof.
intros R1 d ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran most own
  peak2 cnt2 fail2 ran2 most2 own2
  ks a ka n Dr Fr HAR HL HJ HL2 HI HFT HDL.
apply (pf_oitemsR_frame SEGS d (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam2) ks a ka n Dr Fr HI).
- intros x k Hxk. exact (HDL x k Hxk).
- intros x Hx. destruct (HFT x Hx) as (Hnf & a' & k' & H1 & H2 & H3).
  destruct (pfk_hblkR B ARx LAWS R1 ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran
    most own
    peak2 cnt2 fail2 ran2 most2 own2 a' k' x HAR HL HJ HL2 H1 H2 H3 Hnf) as [Hv Hp'].
  split.
  + apply (mbyte_of_aview SEGS). exact Hv.
  + intros _. apply (apresent_writable SEGS). exact Hp'.
Qed.

(* ---- pj_free's frame at the return state: the callee journal runs at the callee window below sp1 + 8, its
   footprint below alloc_ceiling; the frame and the composed journal at any world relation R, the callee's journal at
   any R1 (only its conjuncts on bytes are read) ---- *)
Lemma pfk_frame : forall (R R1 : world SEGS -> world SEGS -> Prop)
    PB FX CTX0 en ly S Hp W rg mem md k STK1 e1 FP1 ly2 S2 Hp2 W2 rg2 mem2 md2 k1,
  pf_pre B ARx PB FX CTX0 en ->
  pf_frameR (SK := SK) B ARx R en ly S Hp W rg mem md k -> pf_spill en W mem ->
  ajournal_xR (SK := SK) SEGS B PST ARx R1 (STK1 + e1) (fe_sp1 en + e1) FP1 ly S Hp W mem md []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  0 <= STK1 -> 0 <= e1 <= 8 -> ~ YI16.sink_open_fp FP1 ->
  (forall x, inFP FP1 x -> x < YM05.alloc_ceiling) ->
  spZ rg2 = spZ rg -> getr rg2 3 = getr rg 3 -> getr rg2 4 = getr rg 4 ->
  (* the callee's m-form keep (fQmn) *)
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  pf_frameR (SK := SK) B ARx R en ly2 S2 Hp2 W2 rg2 mem2 md2 (k + k1) /\ pf_spill en W2 mem2.
Proof.
intros R R1 PB FX CTX0 en ly S Hp W rg mem md k STK1 e1 FP1 ly2 S2 Hp2 W2 rg2 mem2 md2 k1
  HPRE HFR HSP HJ1 HJ2 HSTK1 He1 Hsink _ Esp Eg3 Eg4 HMN.
assert (Hd0 : 0 <= fe_d en)
  by (unfold pf_pre in HPRE; cbv zeta in HPRE; destruct HPRE as (_ & _ & _ & _ & (Hd & _) & _); exact Hd).
unfold pf_frameR, pf_spill in *.
destruct HFR as (HJ0 & HWIN & Hsp & HSAV & HPRES & Hgp & Htp & HROD & HMN0).
destruct HSP as (Sp1 & Sp2).
pose proof (ajxR_stk HJ0) as Hast0.
destruct Hast0 as (_ & _ & A3 & A4 & A5 & A6 & _).
pose proof (ajxR_hi HJ1) as F1. pose proof (ajxR_img HJ1) as F3. pose proof (ajxR_pres HJ1) as Hpres1. clear HJ1.
rewrite pfg_stk in A4.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
unfold fe_sp1, PJF_FR in *.
(* every byte from sp1 + 8 up is above alloc_ceiling and outside the callee's window: kept *)
assert (K : forall a, fe_sp0 en - 128 + 8 <= a < 2 ^ 47 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply F1; lia. }
split.
- split; [exact HJ2|].
  split.
  { intros a Ha Hn. rewrite (K a ltac:(lia)). exact (HWIN a Ha Hn). }
  split; [rewrite Esp; exact Hsp|].
  split.
  { intros r o Hro. pose proof (pfk_saved_rng r o Hro) as Ho.
    apply (pfg_val_keep W W2 mem mem2); [exact (HSAV r o Hro)|].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K. lia. }
  split.
  { intros a Ha. destruct (Z_lt_le_dec a (fe_sp0 en - 128 + e1)) as [Hlt | Hge].
    - apply Hpres1. lia.
    - apply (apresent_transfer SEGS (w_H W) (w_H W2) mem mem2 a).
      + lia.
      + intros Hi. pose proof (Hsegs a Hi). lia.
      + apply F1; lia.
      + apply HPRES. lia. }
  split; [rewrite Eg3; exact Hgp|]. split; [rewrite Eg4; exact Htp|].
  split; [|intros H0; exact (HMN (HMN0 H0))].
  intros a Hro Hos Her.
  rewrite (F3 a); [exact (HROD a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsink].
  + destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
  + intros Hp'. exact (pst_not_ro_B a Hp' Hro).
- split.
  + apply (pfg_val_keep W W2 mem mem2); [exact Sp1|].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K. lia.
  + apply (pfg_val_keep W W2 mem mem2); [exact Sp2|].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K. lia.
Qed.

(* ---- the accounts after a call ---- *)
(* fuzz_free of the next block b of the order *)
Lemma pfk_acct_free : forall FX en ly S Hp W mem Fd b Fr Lam ly2 S2 Hp2 W2 mem2 l1 l2,
  pf_acct B FX en ly S Hp W mem Fd (b :: Fr) Lam ->
  FX ly S ly2 S2 (Some b) -> room_live_cf S2 ->
  Lam = l1 ++ b :: l2 ->
  (exists b1 b2, ablocks B ly S = b1 ++ (fst b - cf_head, snd b + cf_head) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 (l1 ++ l2) (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) ->
  pf_acct B FX en ly2 S2 Hp2 W2 mem2 (Fd ++ [b]) Fr (l1 ++ l2).
Proof.
intros FX en ly S Hp W mem Fd b Fr Lam ly2 S2 Hp2 W2 mem2 l1 l2 HA HFX HR2 ELam (b1 & b2 & E1 & E2) HL2.
destruct HA as (_ & _ & HPL & HPB & EF & HRE).
split; [exact HR2|]. split; [exact HL2|].
split.
{ subst Lam. eapply Permutation_trans; [exact HPL|]. rewrite <- app_assoc. apply Permutation_app_head.
  cbn [app]. apply Permutation_sym. apply Permutation_middle. }
split.
{ eapply Permutation_trans; [exact HPB|]. rewrite E1, E2. unfold prhPj_hbl. rewrite map_app. cbn [map].
  rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
split; [rewrite EF, <- app_assoc; reflexivity|].
eapply pf_reach_trans; [exact HRE|]. apply pf_reach_free1. exact HFX.
Qed.

(* fuzz_free (NULL) *)
Lemma pfk_acct_null : forall FX en ly S Hp W mem Fd Fr Lam ly2 S2 Hp2 W2 mem2,
  pf_acct B FX en ly S Hp W mem Fd Fr Lam ->
  FX ly S ly2 S2 None -> room_live_cf S2 ->
  ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) ->
  pf_acct B FX en ly2 S2 Hp2 W2 mem2 Fd Fr Lam.
Proof.
intros FX en ly S Hp W mem Fd Fr Lam ly2 S2 Hp2 W2 mem2 HA HFX HR2 Eab HL2.
destruct HA as (_ & _ & HPL & HPB & EF & HRE).
split; [exact HR2|]. split; [exact HL2|]. split; [exact HPL|].
split; [rewrite Eab; exact HPB|]. split; [exact EF|].
eapply pf_reach_trans; [exact HRE|]. apply pf_reach_null1. exact HFX.
Qed.

(* a recursive pj_free of the next subtree, whose blocks Di are freed in its order Fi *)
Lemma pfk_acct_rec : forall FX en ly S Hp W mem Fd Fi Fr Lam Di ly2 S2 Hp2 W2 mem2 Lam2,
  pf_acct B FX en ly S Hp W mem Fd (Fi ++ Fr) Lam ->
  room_live_cf S2 ->
  Permutation Lam (Di ++ Lam2) ->
  Permutation (ablocks B ly S) (prhPj_hbl Di ++ ablocks B ly2 S2) ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) ->
  pf_reach FX Fi ly S [] ly2 S2 -> Permutation Fi Di ->
  pf_acct B FX en ly2 S2 Hp2 W2 mem2 (Fd ++ Fi) Fr Lam2.
Proof.
intros FX en ly S Hp W mem Fd Fi Fr Lam Di ly2 S2 Hp2 W2 mem2 Lam2 HA HR2 HPL2 HPB2 HL2 HRi HFD.
destruct HA as (_ & _ & HPL & HPB & EF & HRE).
split; [exact HR2|]. split; [exact HL2|].
split.
{ eapply Permutation_trans; [exact HPL|]. rewrite <- app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [exact HPL2|]. apply Permutation_app_tail. apply Permutation_sym. exact HFD. }
split.
{ eapply Permutation_trans; [exact HPB|]. unfold prhPj_hbl in *. rewrite map_app, <- app_assoc.
  apply Permutation_app_head. eapply Permutation_trans; [exact HPB2|]. apply Permutation_app_tail.
  apply Permutation_map. apply Permutation_sym. exact HFD. }
split; [rewrite EF, app_assoc; reflexivity|].
eapply pf_reach_trans; [exact HRE|]. exact (pf_reach_app FX Fi ly S [] ly2 S2 Fr HRi).
Qed.
End k.
