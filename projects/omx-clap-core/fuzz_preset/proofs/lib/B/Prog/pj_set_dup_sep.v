(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the SEPARATION facts the DUP segment of pj_set's image-B walk needs (fuzz_preset
   asan-ubsan, B 0x86e8c; the cuts of lib/B/Prog/pj_set_defs.v, the DUP cut at +0xa8), at the allocator laws of the
   harness head length (YCbqG.v AR_laws_x at hl := cf_head).
   proves no function (kind: glue lemma).
   - pjsd_lam_disj: two distinct harness blocks of one ledger share no byte (their allocator blocks are distinct
     pairs of ablocks, sep_blocks_x).
   - pjsd_at_lam_disj: a struct placed as PRH_FnReader.v prhReader_at says shares no byte with a harness block it
     does not lie inside (one case per placement: another harness block, a non-harness allocator block, a live fake
     frame, the caller's window above the allocator ceiling).
   - pjsd_at_fresh_disj: ... nor with an allocator block that was not live at the state where the struct was placed
     (the block / frame cases at the later state, the frame address carried by alx_layout over layout_le).
   - pjsd_w_apart: at the DUP cut the value struct's 56 bytes lie outside the object's footprint over Do, as the
     entry premise says over js_D: the fresh blocks grow added (Dnew) cannot hold the value struct, by the four cases
     of its ENTRY placement.
   Numerals: 56 (LENGTH: the struct pj). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
S1ImgB pj_set_defs pj_set_trans pj_set_vis.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* a value occurring in both halves of a duplicate-free list is impossible *)
Lemma pjsd_nodup_apart : forall (l1 l2 : list Z) a, List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
intros l1 l2 a HN H1 H2. destruct (in_split a l1 H1) as (u & v & ->).
rewrite <- app_assoc in HN. cbn [app] in HN. apply (NoDup_remove_2 _ _ _ HN).
apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* a harness block of the ledger as its allocator block: live, below the ceiling, its user range inside *)
Lemma pjsd_hb : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\
  a - cf_head + req_size (k + cf_head) <= YM05.alloc_ceiling /\ k + cf_head <= req_size (k + cf_head).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HL as (_ & _ & HLF & _).
pose proof (proj1 (Forall_forall _ _) HLF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hce & _).
pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hce | exact Rq].
Qed.

(* (1) two distinct harness blocks of one ledger hold no byte in common *)
Lemma pjsd_lam_disj : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k',
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> a <> a' ->
  forall x, a <= x < a + k -> ~ (a' <= x < a' + k').
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' HAR HL Hin Hin' Hne x Hx Hx'.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjsd_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & _ & Rq).
destruct (pjsd_hb ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HL Hin') as (Hk0' & Hab' & _ & Rq').
assert (Hne2 : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head))
  by (intros E; injection E as E1 _; apply Hne; lia).
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* (2) at its weakest premise on the window: every byte of the caller's window is at or above the ceiling *)
Lemma pjsd_at_lam_core : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p n a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p n -> 0 < n -> YM05.alloc_ceiling <= spZ regs ->
  In (a, k) Lam -> ~ (a <= p /\ p + n <= a + k) ->
  forall x, p <= x < p + n -> ~ (a <= x < a + k).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p n a k HAR HL Hat Hn Hsp Hin Hout x Hx Hxa.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjsd_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & Hce & Rq).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a' a) as [Ea | Hne].
  + subst a'. pose proof HL as (_ & HND & _).
    pose proof (prh_fst_unique Lam a k' k HND Hin' Hin) as Ek. subst k'.
    apply Hout. split; assumption.
  + exact (pjsd_lam_disj ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k HAR HL Hin' Hin Hne x ltac:(lia) Hxa).
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 E2. apply HnL.
    replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia). exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbm Hab Hne) as Hd.
  pose proof (pjs_req m ltac:(lia)) as (Rm & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hcp) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* (2) a struct placed as prhReader_at says holds no byte of a harness block it does not lie inside *)
Lemma pjsd_at_lam_disj : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) STK e p n a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p n -> 0 < n -> 0 <= STK -> astk_ok STK ly (spZ regs) ->
  In (a, k) Lam -> 0 < k -> ~ (a <= p /\ p + n <= a + k) ->
  forall x, p <= x < p + n -> ~ (a <= x < a + k).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs STK e p n a k HAR HL Hat Hn HSTK Hstk Hin Hk Hout.
pose proof Hstk as (_ & _ & Hc & Hs & _).
exact (pjsd_at_lam_core ly S Hp W mem md Lam peak cnt fail ran most own regs e p n a k HAR HL Hat Hn ltac:(lia) Hin Hout).
Qed.

(* (3) at its weakest premise on the window: every byte of the caller's window is at or above the ceiling *)
Lemma pjsd_at_fresh_core : forall ly S Hp W mem md ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own
    (regs : bvmap 5 word) e p n q kq,
  ARx ly S Hp W mem md -> ARx ly' S' Hp' W' mem' md' ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p n -> 0 < n ->
  YM05.alloc_ceiling <= spZ regs ->
  frames S' = frames S ->
  layout_le (length (st_secs S)) ly ly' ->
  (forall b m, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S')) ->
  In (q, kq) (ablocks B ly' S') -> ~ In (q, kq) (ablocks B ly S) ->
  forall x, p <= x < p + n -> ~ (q <= x < q + req_size kq).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own regs e p n q kq
  HAR HAR' HL Hat Hn Hsp Hfrs Hlay Hmono Hq Hnq x Hx Hxq.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' q kq HAR' Hq) as (_ & _ & Hqce & _).
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (pjsd_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & _ & Rq).
  assert (Hne : (a - cf_head, k + cf_head) <> (q, kq)) by (intros E; rewrite E in Hab; exact (Hnq Hab)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ _ _ HAR' (Hmono _ _ Hab) Hq Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hne : (b, m) <> (q, kq)) by (intros E; rewrite E in Hbm; exact (Hnq Hbm)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ _ _ HAR' (Hmono _ _ Hbm) Hq Hne) as Hd.
  pose proof (pjs_req m ltac:(lia)) as (Rm & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md ly' HAR Hlay) as (_ & Hfa & _).
  assert (Hcp' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hcp).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ cid pos HAR' Hq Hcp') as Hd.
  rewrite Hfa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* (3) ... and no byte of an allocator block that was not live where the struct was placed *)
Lemma pjsd_at_fresh_disj : forall ly S Hp W mem md ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own
    (regs : bvmap 5 word) STK e p n q kq,
  ARx ly S Hp W mem md -> ARx ly' S' Hp' W' mem' md' ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p n -> 0 < n -> 0 <= STK -> astk_ok STK ly (spZ regs) ->
  frames S' = frames S ->
  layout_le (length (st_secs S)) ly ly' ->
  (forall b m, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S')) ->
  In (q, kq) (ablocks B ly' S') -> ~ In (q, kq) (ablocks B ly S) ->
  forall x, p <= x < p + n -> ~ (q <= x < q + req_size kq).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own regs STK e p n q kq
  HAR HAR' HL Hat Hn HSTK Hstk Hfrs Hlay Hmono Hq Hnq.
pose proof Hstk as (_ & _ & Hc & Hs & _).
exact (pjsd_at_fresh_core ly S Hp W mem md ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own regs e p n q kq
  HAR HAR' HL Hat Hn ltac:(lia) Hfrs Hlay Hmono Hq Hnq).
Qed.

(* (4) THE DELIVERABLE: at the DUP cut, the value struct's 56 bytes lie outside the object's footprint,
       exactly as the kit's entry premise says for the ENTRY block list js_D en (the cut at any world relation R) *)
Lemma pjsd_w_apart : forall (R : world SEGS -> world SEGS -> Prop)
    CTX0 dd en ly S Hp W regs mem md k Lam2 peak2 cnt2 fail2 ran2 most2 own2 Do Lr Dold Dnew Dr,
  pjs_pre B ARx CTX0 dd en ->
  pjs_invR B ARx R dd en ly S Hp W regs mem md k ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  Permutation (js_Lam en) (js_D en ++ js_Dw en ++ Lr) ->
  Permutation Lam2 (Do ++ js_Dw en ++ Lr) ->
  prhPj_blocks B (js_ly en) (js_S en) (js_Lam en) ly S Lam2 ->
  Permutation (js_D en) (Dold ++ Dr) -> Permutation Do (Dnew ++ Dr) ->
  prhPj_new B (js_ly en) (js_S en) Dnew ->
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam2 W (js_regs en) mem (js_w en) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam2) (js_w en) (js_tv en) (js_Dw en) ->
  (forall x, js_w en <= x < js_w en + 56 -> ~ pj_footR (js_o en) Do x).
Proof.
intros R CTX0 dd en ly S Hp W regs mem md k Lam2 peak2 cnt2 fail2 ran2 most2 own2 Do Lr Dold Dnew Dr
  HPRE HINV HL2 HPL HPL2 HBLK HPD HPDo HNEW HSLOT HNODE x Hx Hfoot.
pose proof (@cf_head_nonneg cp) as Hh0.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSW0 & _ & _ & HWO & _).
pose proof HFPRE as ((HAR0 & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof Hstk0 as (_ & HSTK0 & Hceil0 & Hslo0 & _).
assert (Hsp : YM05.alloc_ceiling <= spZ (js_regs en)) by lia.
destruct HINV as (HJ & _).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hlay. pose proof (ajxR_frs HJ) as Hfrs.
pose proof HSLOT as (_ & HSAT & _).
(* val's blocks are apart from val's header (pj_nodeR's second conjunct) *)
assert (HAPW : pj_apartR (js_Dw en) (js_w en)).
{ revert HNODE. destruct (js_tv en); intros HNODE; cbn [pj_nodeR] in HNODE; exact (proj1 (proj2 HNODE)). }
destruct Hfoot as [Ho | ([q kq] & Hb & Hh)].
- exact (HWO x Hx (or_introl Ho)).
- unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
  pose proof (Permutation_in _ HPDo Hb) as Hb'. apply in_app_or in Hb' as [Hnew | Hdr].
  2: { apply (HWO x Hx). right. exists (q, kq). split; [|unfold pj_holdsR; cbn [fst snd]; exact Hh].
       apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Hdr. }
  assert (HinL2 : In (q, kq) Lam2)
    by (apply (Permutation_in _ (Permutation_sym HPL2)); apply in_or_app; left; exact Hb).
  destruct (pjsd_hb ly S Hp W mem md Lam2 peak2 cnt2 fail2 ran2 most2 own2 q kq HAR HL2 HinL2) as (Hkq0 & Hqab & Hqce & Rq).
  pose proof (HNEW q kq Hnew) as Hqnew.
  (* the value struct does not lie inside the fresh block (q, kq): the four cases of its ENTRY placement *)
  assert (Hout : ~ (q <= js_w en /\ js_w en + 56 <= q + kq)).
  { intros (Hq1 & Hq2).
    destruct HSW0 as (_ & Hat0 & _).
    destruct Hat0 as [(a0 & k0 & Hin0 & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) |
      [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
    + (* an entry harness block: neither the object's nor val's, so one of Lr, live at Lam2, and not (q, kq) *)
      assert (HnD : ~ In (a0, k0) (js_D en)).
      { intros HD. apply (HWO (js_w en) ltac:(lia)). right. exists (a0, k0).
        split; [exact HD | unfold pj_holdsR; cbn [fst snd]; lia]. }
      assert (HnDw : ~ In (a0, k0) (js_Dw en)).
      { intros HD. exact (HAPW (a0, k0) (js_w en) HD ltac:(unfold pj_holdsR; cbn [fst snd]; lia) ltac:(lia)). }
      apply (Permutation_in _ HPL) in Hin0. apply in_app_or in Hin0 as [HD | Hin0]; [exact (HnD HD)|].
      apply in_app_or in Hin0 as [HD | HLr]; [exact (HnDw HD)|].
      assert (HinL2' : In (a0, k0) Lam2) by (apply (Permutation_in _ (Permutation_sym HPL2));
        apply in_or_app; right; apply in_or_app; right; exact HLr).
      assert (Hne : a0 <> q).
      { intros E. subst a0. pose proof HL2 as (_ & HND & _). apply NoDup_ListNoDup in HND.
        pose proof (Permutation_NoDup (Permutation_map fst HPL2) HND) as HND2. rewrite !map_app in HND2.
        apply (pjsd_nodup_apart (map fst Do) _ q HND2).
        - apply in_map_iff. exists (q, kq). split; [reflexivity | exact Hb].
        - apply in_or_app. right. apply in_map_iff. exists (q, k0). split; [reflexivity | exact HLr]. }
      exact (pjsd_lam_disj ly S Hp W mem md Lam2 peak2 cnt2 fail2 ran2 most2 own2 a0 k0 q kq HAR HL2 HinL2' HinL2 Hne
        (js_w en) ltac:(lia) ltac:(lia)).
    + (* an entry allocator block that is no harness block: unchanged (prhPj_blocks), live now, not (q, kq)'s *)
      destruct HBLK as (other & HB0 & HB1).
      assert (Hnh : ~ In (b, m) (prhPj_hbl (js_Lam en))).
      { intros Hh'. unfold prhPj_hbl in Hh'. apply in_map_iff in Hh' as ([a' k'] & E & Hin').
        cbn [fst snd] in E. injection E as E1 E2. apply HnL.
        replace (b + cf_head, m - cf_head) with (a', k') by (f_equal; lia). exact Hin'. }
      pose proof (Permutation_in _ HB0 Hbm) as Hbm'.
      apply in_app_or in Hbm' as [HH | Hoth]; [exact (Hnh HH)|].
      assert (Hbm2 : In (b, m) (ablocks B ly S))
        by (apply (Permutation_in _ (Permutation_sym HB1)); apply in_or_app; right; exact Hoth).
      assert (Hne : (b, m) <> (q - cf_head, kq + cf_head)) by (intros E; rewrite E in Hbm; exact (Hqnew Hbm)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbm2 Hqab Hne) as Hd.
      pose proof (pjs_req m ltac:(lia)) as (Rm & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + (* an entry fake frame: still live (the journal adds no frame), at the same address (alx_layout) *)
      assert (Hcp' : In (cid, pos) (frames S)) by (rewrite Hfrs; exact Hcp).
      destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ ly HAR0 Hlay) as (_ & Hfa & _).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hqab Hcp') as Hd.
      rewrite Hfa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + (* the caller's window lies at or above the ceiling, every block below it *)
      lia. }
  exact (pjsd_at_lam_core ly S Hp W mem md Lam2 peak2 cnt2 fail2 ran2 most2 own2 (js_regs en) (js_d en) (js_w en) 56 q kq
    HAR HL2 HSAT ltac:(lia) Hsp HinL2 Hout x Hx Hh).
Qed.

End s.
