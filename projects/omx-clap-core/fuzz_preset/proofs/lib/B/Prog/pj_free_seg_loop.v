(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   LOOP segment pfs_LH_holds: from the cut pf_LH at slot i (+0xa8) through the recursive call to pf_LK (+0xf0), then
   pfs_LK (the key's free, lib/B/Prog/pj_free_seg_lk.v) and pfs_LC_holds (the bound test, pj_free_seg_lc.v) to pf_LH
   at slot i + 1 or pf_LX (+0x14c).
     +0xa8  .. +0xb0  ASan check of v+24's cell (decided: shadow entry mkSHE 8 0 56); kids := v->kids (atom 33)
     +0xb4  .. +0xd0  a0 := kids + 56 i; UBSan pointer-overflow checks: `beq` decided, `bltu kids + 56 i, kids`
                      REFUTED (no wrap: kids + 56 n <= the kids block's end < 2 ^ 64)
     +0xd4  .. +0xe4  UBSan product check on 56 i: `bnez` REFUTED (pfg_U_mulchk: i < 2 ^ 42)
     +0xe8            a0 := kids + 56 i
     +0xec            jal pj_free (B 0x86b10): the RECURSIVE CALL, discharged by tpj_free_specO at the children's depth
                      d' (fe_n en = S d'), the induction hypothesis of the top theorem (pj_free_top.v), at the callee
                      window e1 = 0 (YCbqGcallW.v aj_call_xWR), v' = kids + 56 i, D1 / F1 = slot i's subtree's blocks and
                      order (pf_oitemsR), Lam = the current ledger, the slot in the kids block (prhReader_at's first
                      place), PB along F1 from pf_pre's pf_safe and pf_acct's pf_reach (pf_safe_after / pf_safe_prefix).
   The walk's relation is wle' SEGS RZ_cf (pj_free_defs.v): the R runners (YC1fPx paj_run_xR / paj_run_to_xR,
   YSRrG.paj_branchR) and the R call rule, with the journal at it; the child's text concludes SRr' SEGS RZ_cf with its
   post fpostWmR at it, which is the call rule's callee post fpostW_xR by conversion.
   After the call (pj_free_keep.v): the accounts (pfk_acct_rec, the order: Fd ++ F1), v's node (pfk_vnode), the slots
   i+1 .. n-1 (pfk_items), slot i's key (pfk_hblkR, lib/A/Prog/PjFreeCommon.v), the frame (pfk_frame).
   proves no function (kind: segment lemma). Section hypotheses: AR_laws_x at cf_head; ARx_frame_hull_vis (MARKED kit
   fact, YGcfFsVis.v; the instance's ARx_frame_hull_vis_cf_ok).
   Numerals: 236 / 240 (DERIVED: listing slot differences times 4), 128 (LENGTH: pj_free's frame), 56 / 8 (LENGTH).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_keep pj_free_lcut pj_free_seg_lc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.


Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).


(* ---- a callee-saved register is kept across a call ---- *)
Lemma pfl_pres_bv : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> acallee_saved (bv_unsigned r) -> getr r2 r = getr r1 r.
Proof. intros r1 r2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* ---- NoDup bookkeeping (stdpp's NoDup, the one pj_oshapeR states) ---- *)
Lemma pfl_nd_app : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. inversion HN as [|y' l' Hy HN']; subst.
destruct H1 as [<- | H1]; [apply Hy; apply list_elem_of_In; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
Lemma pfl_ndr : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1 as [|y l1 IH]; intros l2 HN; [exact HN|]. cbn [app] in HN. inversion HN; subst. apply IH. assumption. Qed.
Lemma pfl_ndl : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
induction l1 as [|y l1 IH]; intros l2 HN; [constructor|]. cbn [app] in HN. inversion HN as [|y' l' Hy HN']; subst.
constructor; [intros H; apply Hy; apply list_elem_of_In; apply list_elem_of_In in H; apply in_or_app; left; exact H
  | exact (IH l2 HN')].
Qed.
Lemma pfl_nd_perm : forall (l l' : list (Z * Z)), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros l l' HP HN. rewrite <- HP. exact HN. Qed.
Lemma pfl_lam_now : forall (L0 Fd Lam : list (Z * Z)) b, Permutation L0 (Fd ++ Lam) -> In b L0 -> ~ In b Fd -> In b Lam.
Proof.
intros L0 Fd Lam b HP Hb Hn. pose proof (Permutation_in _ HP Hb) as H2.
apply in_app_or in H2 as [H2|H2]; [contradiction | exact H2].
Qed.

(* ---- the footprint of harness blocks ---- *)
Lemma pfl_inFP_hbl : forall (D : list (Z * Z)) a k x, In (a, k) D ->
  a - cf_head <= x < a - cf_head + req_size (k + cf_head) -> inFP (ablocks_fp (prhPj_hbl D)) x.
Proof.
intros D a k x Hin Hx. exists (a - cf_head, a - cf_head + req_size (k + cf_head)). split; [|cbn [fst snd]; lia].
unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
Qed.
Lemma pfl_inFP_hbl_inv : forall (D : list (Z * Z)) x, inFP (ablocks_fp (prhPj_hbl D)) x ->
  exists a k, In (a, k) D /\ a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros D x (r & Hr & Hx). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
apply in_map_iff in Hr as ((a & k) & <- & Hin). cbn [fst snd] in Hx. exists a, k. split; [exact Hin | exact Hx].
Qed.

(* ---- two distinct harness blocks: the user bytes of one miss the allocator block of the other ---- *)
Lemma pfl_hb_apart : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> (a, k) <> (a', k') -> a <= x < a + k ->
  ~ (a' - cf_head <= x < a' - cf_head + req_size (k' + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x HAR HL H1 H2 Hne Hx Hx'.
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL H1) as (Hk0 & Ha0 & Hak & _ & Hab & _).
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL H2) as (Hk0' & Ha0' & Hak' & _ & Hab' & _).
assert (Hne' : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)).
{ intros E. injection E as E1 E2. apply Hne. f_equal; lia. }
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hab' Hne') as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq1 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq1) as [_ Hr1].
lia.
Qed.

(* ---- v's node misses the allocator block of every harness block of D in the ledger ---- *)
Lemma pfl_v_apart : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  pf_vnode B en nd ly S Lam W mem -> ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> YM05.alloc_ceiling <= fe_sp0 en ->
  In (a, k) Lam -> In (a, k) (fe_D en) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  ~ (fe_v en <= x < fe_v en + 56).
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x HVN HAR HL Hceil Hin HinD Hx Hv.
pose proof HVN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & _).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq2 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq2) as [_ Hr1].
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & _).
destruct Hplace as [(a' & k' & Hin' & HnD & Ha' & Hk') | [(b & m & Hb & Hnl & Hb1 & Hb2) |
  [(cid & pos & Hf & Hf1 & Hf2) | (Hw1 & Hw2)]]].
- assert (Hne : (a', k') <> (a, k)) by (intros E; rewrite E in HnD; exact (HnD HinD)).
  exact (pfl_hb_apart ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k x HAR HL Hin' Hin Hne ltac:(lia) Hx).
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 E2. apply Hnl.
    replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hb Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. assert (Hrq5 : 0 <= m) by lia. pose proof (req_size_pos (m) Hrq5) as [_ Hr2]. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* ---- a harness block's user bytes: addressable, hull visible, in application memory, not the runtime's ---- *)
Lemma pfl_hb_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x n,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  a <= x -> x + n <= a + k -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\ shadow_hull_vis (aview SEGS (w_H W) mem) x n /\
  amem_range x n /\ (forall y, x <= y < x + n -> ~ aowned B ly S y).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x n HAR HL Hin H1 H2 Hn.
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & Hhp).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq3 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq3) as [_ Hr1].
destruct (alx_hshadow SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab Hhp) as (Hbs & Hhv).
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & Happ & Hpo & _).
replace (a - cf_head + cf_head) with a in Hbs, Hhv by lia.
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [eapply shadow_hull_vis_sub_cf; [apply Hhv; lia | lia | lia]|].
split.
{ pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold in_app, amem_range, kLowShadowBeg, ASAN_CEIL in *. lia. }
intros y Hy. exact (proj2 (Hpo y ltac:(lia))).
Qed.


(* ---- THE LOOP SEGMENT ---- *)
Theorem pfs_LH_holds : forall PB FX CTX0 d',
  pf_texts (SK := SK) B ARx PB FX -> tpj_free_specO (PA := PA) B ARx SK PB FX CTX0 d' ->
  pfs_LK (SK := SK) B ARx PB FX CTX0 d' ->
  pfs_LH (SK := SK) B ARx PB FX CTX0 d'.
Proof.
intros PB FX CTX0 d' TXT IH SLK en nd i ly S Hp W regs mem md k HPRE HND HLH KLH KLX.
(* after the child: the key's free, then the bound test *)
assert (KLK : forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1,
  pf_LK (SK := SK) B ARx FX en nd d' i ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
  SRr' SEGS RZ_cf W1 (pf_cfg PJF_LK regs1 mem1 md1) (pf_FIN (SK := SK) B ARx FX en)).
{ intros ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HLK. apply (SLK en nd i ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HPRE HND HLK).
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HLC.
  exact (pfs_LC_holds B ARx LAWS PB FX CTX0 d' en nd i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HPRE HND HLC KLH KLX). }
clear SLK KLH KLX.
pose proof HLH as (En & Hi & HFR & HSP & HVR & HLR & Fd & Lam & Dr & Fr & HAC & HVN & HPD & HIT).
pose proof HFR as (HJ & HWIN & Hsp & HSV & HPRES & H3 & H4 & HROD).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HLR as (R20 & R21 & R24 & R25 & R26 & R27).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HAC as (HROOM & HLED & HPL & HPA & HFF & HRC).
destruct (pfl_basics B ARx LAWS PB FX CTX0 en nd i ly S Hp W regs mem md k HPRE HND Hi HFR)
  as ((kk & Hkkin & Hkkn & HDk & Hkid4 & Hkidc & Hkid16) & Hi42 & Hsp1 & Hspr & Hal & Hceil0).
pose proof HPRE as (HFPRE0 & HUNIV & HROOM0 & H100 & HWIN0 & HCASE0 & HSAFE0 & HLED0).
pose proof (HSAFE0 ltac:(lia)) as HSAFE.
pose proof HFPRE0 as (HAFN0 & HROD0 & HSTKHI0).
(* fpre's FRM0-ENTRY conjunct: pj_free runs no float instruction, so the recursive call gets pj_free's own *)
pose proof HFPRE0 as (_ & _ & _ & _ & HFRM0).
pose proof HAFN0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HND as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof (pfg_stk d') as ESTK'.
assert (Hn' : Z.of_nat (Datatypes.S (fe_n en)) = Z.of_nat d' + 2) by (rewrite En; lia).
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* ---- slot i: its key Dk, its subtree D1 / F1, the slots after it ---- *)
replace (Z.to_nat (fn_n nd - i)) with (Datatypes.S (Z.to_nat (fn_n nd - (i + 1)))) in HIT by lia.
destruct HIT as (Dk & D1 & F1 & D2 & F2 & EDr & EFr & HKEY & HFO1 & HIT2).
subst Dr Fr.
replace (fn_kids nd + 56 * i + 56) with (fn_kids nd + 56 * (i + 1)) in HIT2 by lia.
replace (fn_keys nd + 8 * i + 8) with (fn_keys nd + 8 * (i + 1)) in HIT2 by lia.
set (v' := fn_kids nd + 56 * i) in *.
assert (ND : NoDup (Fd ++ (Dk ++ D1 ++ D2) ++ fn_own nd)) by exact (pfl_nd_perm _ _ HPD HNDD).
assert (Hown_k : In (fn_kids nd, kk) (fn_own nd)) by (unfold fn_own; rewrite HDk; left; reflexivity).
assert (HkLam : In (fn_kids nd, kk) Lam).
{ apply (pfl_lam_now (fe_Lam en) Fd Lam _ HPL Hkkin). intros Hf.
  apply (pfl_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_k. }
assert (Hk_notD1 : ~ In (fn_kids nd, kk) D1).
{ intros H1. apply (pfl_nd_app (Dk ++ D1 ++ D2) (fn_own nd) (fn_kids nd, kk) (pfl_ndr _ _ ND));
  [apply in_or_app; right; apply in_or_app; left; exact H1 | exact Hown_k]. }
assert (HinD : forall b, In b (Fd ++ (Dk ++ D1 ++ D2) ++ fn_own nd) -> In b (fe_D en))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPD) Hb)).
assert (Hk_inD : In (fn_kids nd, kk) (fe_D en)) by (apply HinD; apply in_or_app; right; apply in_or_app; right; exact Hown_k).
assert (HD1D : forall b, In b D1 -> In b (fe_D en)).
{ intros b Hb. apply HinD. apply in_or_app; right; apply in_or_app; left; apply in_or_app; right;
  apply in_or_app; left; exact Hb. }
assert (HFD1 : pj_fdR SEGS (rdW W mem) (prh_lin Lam) d' v' D1 /\ Permutation F1 D1)
  by exact (pj_foR_fdR SEGS _ _ _ _ _ _ HFO1).
assert (HD1L : forall a k0, In (a, k0) D1 -> In (a, k0) Lam)
  by (intros a k0 H; exact (pj_foR_lblk SEGS _ _ _ _ _ _ HFO1 a k0 H)).
assert (Hv'rw : pj_rwR SEGS (rdW W mem) v').
{ destruct d' as [|d'']; cbn [pj_foR] in HFO1;
  destruct HFO1 as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk' & Dy & Di & Fi & Hhdr & _);
  exact (proj1 Hhdr). }
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HkLam) as (Hkk0 & Hkka & Hkkc & Hkk16 & Hkab & Hkhp).
assert (Hrq4 : 0 <= kk + cf_head) by lia. pose proof (req_size_pos (kk + cf_head) Hrq4) as [_ Hkreq].
destruct (pfl_hb_vis ly S Hp W mem md Lam _ _ _ _ _ _ (fn_kids nd) kk v' 56 HAR HLED HkLam ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hv'ra & Hv'hull & Hv'amr & Hv'own).
(* the order along F1: PB at every state the child reaches *)
assert (HSAFE1 : pf_safe FX PB F1 ly S).
{ pose proof (pf_safe_after FX PB _ _ _ _ _ _ HSAFE HRC) as H.
  rewrite <- !app_assoc in H. exact (pf_safe_prefix FX PB F1 _ ly S H). }
(* ---- +0xa8 .. +0xec: the engine to the recursive `jal` ---- *)
destruct (pfl_seat en nd i W regs mem PJF_LH HVR HLR Hspr Hal ltac:(lia) Hv8 Hstr Hkids Hkeys Hnn
  ltac:(lia) Hkid16 Hi42 Hvra Hamr) as [HS SHOK].
set (E := PFL_E regs nd) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, PFL_E; apply Eimg_env).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (HAE : env_agree 32 (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)]) E)
  by (unfold E, PFL_E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Ui : U E (SOff 26 0) = i).
{ apply (U_atom E 26 i); [rewrite (Er 26%nat 26%bv) by (first [lia | reflexivity]); exact R26 | lia]. }
assert (Ukids : U E (SOff 33 0) = fn_kids nd).
{ pose proof (EX 1%nat ltac:(lia)) as X1. change (32 + 1)%nat with 33%nat in X1. cbn [nth] in X1.
  apply (U_atom E 33 (fn_kids nd)); [exact X1 | lia]. }
assert (U24 : U E (SOff 24 0) = 56 * i).
{ apply (U_atom E 24 (56 * i)); [rewrite (Er 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | lia]. }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = fe_v en + c).
{ intros c Hc. apply (U_atom_off E 8 (fe_v en) c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U23 : U E (SOff 23 0) = SHADOW_OFF).
{ apply (U_atom E 23 SHADOW_OFF); [rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | unfold SHADOW_OFF; lia]. }
assert (Ucell : forall c, 0 <= c <= 56 -> U E (pfl_cell (SOff 8 c)) = (fe_v en + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pfl_cell. apply pfg_U_cell; [apply U8; lia | exact U23 | lia]. }
unfold pf_cfg, SRr'.
set (R := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (RUNTO := @paj_run_to_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fx) (rc := rc) (L := B_prog_listing) (PI := PA) R).
paj_run_tok_x RUN HS HJ SHOK PFL_Bspan; [pfl_awr|].
pfl_mm HF M1. clear HF HFr. rename HG into G1.
(* +0xd0: UBSan `bltu kids + 56 i, kids`: refuted (no wrap) *)
psrr_branch_tok RUN BR HS SHOK PFL_Bspan.
{ exfalso. rewrite branch_ltu_U, pfg_U_add, (pfg_U_mul56 E _ i Ui Hi42), Ukids in Hc.
  apply Z.ltb_lt in Hc. rewrite Z.mod_small in Hc by lia. lia. }
clear Hc.
paj_run_tok_x RUN HS HJ SHOK PFL_Bspan; [pfl_awr|].
pfl_mm HF M2. clear HF HFr. rename HG into G2.
(* +0xe4: UBSan `bnez` on the product check of 56 i: refuted *)
psrr_branch_tok RUN BR HS SHOK PFL_Bspan.
{ exfalso. rewrite branch_ne_U, U_SLit, (pfg_U_mulchk E _ i Ui Hi42) in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_to_tok_x RUNTO HS HJ SHOK PFL_Bspan (PJF_PC + 236); [pfl_awr|].
pfl_mm HF M3. clear HF HFr. rename HG into G3.
pfg_reg HS (10%bv : bv 5) Q10.
pfg_reg HS (9%bv : bv 5) Q9. pfg_reg HS (18%bv : bv 5) Q18. pfg_reg HS (19%bv : bv 5) Q19.
pfg_reg HS (20%bv : bv 5) Q20. pfg_reg HS (21%bv : bv 5) Q21. pfg_reg HS (22%bv : bv 5) Q22.
pfg_reg HS (27%bv : bv 5) Q27.
pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [2%bv; 3%bv; 4%bv; 8%bv; 23%bv; 24%bv; 25%bv; 26%bv] HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pmkst HS.
rewrite M3, M2, M1 in HJ |- *.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _; cfg_model := ?dd |} _ =>
  replace pc with (PJF_PC + 236) by (vm_compute; reflexivity); set (rg0 := rg) in *; set (md0 := dd) in * end.
(* ---- +0xec: jal pj_free ---- *)
pfg_fd (PJF_PC + 236) Hl1 Hd1.
eapply (pfg_step_jal fx R W rg0 mem md0 _ (PJF_PC + 236) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + PJF_LK))
  (Z_to_bv 64 (SIGMA AS_pj_free)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ)
  as HJ1.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsc := r) in *; set (mdc := m) in * end.
(* the call state's registers *)
assert (GR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 23%bv; 24%bv; 25%bv; 26%bv] -> getr regsc r = getr regs r).
{ intros r Hr. unfold regsc. rewrite getr_other; [exact (KR r Hr)|].
  cbn [In] in Hr. intros ->. repeat (destruct Hr as [Hr | Hr]; [apply (f_equal (fun x : bv 5 => bv_unsigned x)) in Hr; vm_compute in Hr; discriminate Hr |]); destruct Hr. }
assert (GQ : forall r : bv 5, r <> 1%bv -> getr regsc r = getr rg0 r) by (intros r Hr; unfold regsc; apply getr_other; exact Hr).
assert (HSPC : spZ regsc = fe_sp1 en) by (unfold spZ; rewrite (GR 2%bv) by (cbn [In]; tauto); exact Hsp).
assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite (GR 3%bv) by (cbn [In]; tauto); rewrite H3; exact Hgp0).
assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite (GR 4%bv) by (cbn [In]; tauto); rewrite H4; exact Htp0).
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + PJF_LK)) by (unfold regsc; apply getr_same; pfl_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + PJF_LK))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA)); [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity |].
  vm_compute. reflexivity. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + PJF_LK))) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold s0Z. rewrite (GR 8%bv) by (cbn [In]; tauto). rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HSPO : spZ regsc = fe_sp0 en + fe_d en + (-128 - fe_d en)) by (rewrite HSPC; unfold fe_sp1, PJF_FR; lia).
assert (Hal' : (-128 - fe_d en) mod 16 = 0) by (Z.div_mod_to_equations; lia).
assert (Hneg : -128 - fe_d en <= 0) by lia.
assert (HSTKF : 0 <= STK_pj_free d') by lia.
assert (Hbud : STK_pj_free d' - (-128 - fe_d en) <= STK_pj_free (fe_n en) + fe_d en) by lia.
assert (He0 : 0 <= 0) by lia.
assert (Hetop : -128 - fe_d en + 0 <= 0) by lia.
assert (HA10 : getr regsc 10 = w64 v').
{ rewrite (GQ 10%bv) by pfl_regne. unfold w64. apply (pfg_reg_of_U E _ _ _ Q10).
  rewrite pfg_U_add, U24, Ukids. rewrite Z.mod_small by (unfold v' in *; lia). unfold v'. lia. }
(* the child's slot: in the kids block *)
assert (HSLOT : prhPj_slot (PA := PA) B (STK_pj_free d') 0 ly S Lam W regsc mem v').
{ split; [lia|]. split; [left; exists (fn_kids nd), kk; split; [exact HkLam | lia]|].
  split; [exact Hv'rw|]. split; [exact Hv'amr|].
  split; [intros a Ha; split; [exact (Hv'own a Ha) | rewrite HSPC; unfold fe_sp1, fe_sp0, PJF_FR in *; lia]|].
  split; [exact Hv'ra | exact Hv'hull]. }
assert (Hv'ne : (v' =? 0) = false) by (apply Z.eqb_neq; lia).
set (FP1 := if v' =? 0 then [] else (v', v' + 56) :: ablocks_fp (prhPj_hbl D1)).
assert (HFP1 : forall a, inFP FP1 a -> (v' <= a < v' + 56) \/
  exists a' k', In (a', k') D1 /\ a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. unfold FP1 in Ha. rewrite Hv'ne in Ha. apply inFP_cons in Ha.
  destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact (pfl_inFP_hbl_inv D1 a Ha)]. }
assert (Hv0 : (fe_v en =? 0) = false) by (apply Z.eqb_neq; lia).
(* every byte of FP1 is a byte of a harness block of D, live in Lam *)
assert (HFPD : forall a, inFP FP1 a -> exists a' k', In (a', k') (fe_D en) /\ In (a', k') Lam /\
  a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. destruct (HFP1 a Ha) as [Ho | (a' & k' & Hin & Hr)].
  - exists (fn_kids nd), kk. split; [exact Hk_inD|]. split; [exact HkLam | lia].
  - exists a', k'. split; [exact (HD1D _ Hin)|]. split; [exact (HD1L _ _ Hin) | exact Hr]. }
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W regsc mem (SIGMA AS_pj_free)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_pj_free d') 0 FP1 (-128 - fe_d en) (Z_to_bv 64 (BASE + PJF_LK)) [] _
    HJ1 HSPO Hal' Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - (* the callee: the depth-d' text at d = 0, v = kids + 56 i, D1 / F1, Lam (SRr' SEGS RZ_cf, its post fpostWmR) *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (IH (fe_most en) (fe_own en) ly S Hp W regsc mem mdc [] 0 v' D1 F1 Lam (fe_peak en) (fe_cnt en) (fe_fail en)
      (fe_ran en)).
    + split; [exact HPRE1|]. split; [exact (proj1 HROD)|].
      split; [rewrite HSPC, Eshi; unfold fe_sp1, PJF_FR, fe_sp0 in *; lia|].
      split; [|exact HFRM0].
      unfold raZ. rewrite HRA1. eapply Z.lt_le_trans; [|apply (proj1 C1)]. apply Z.ltb_lt. vm_compute. reflexivity.
    + exact HUNIV.
    + exact HROOM.
    + exact HA10.
    + exact HWIN1.
    + right. split; [lia|]. split; [lia|]. split; [exact HFO1 | exact HSLOT].
    + intros _. exact HSAFE1.
    + exact HLED.
  - (* the footprint: within the caller's (D's blocks) *)
    intros a Ha. left. destruct (HFPD a Ha) as (a' & k' & HinD' & _ & Hr).
    unfold fe_FP. rewrite Hv0. apply inFP_cons. right. exact (pfl_inFP_hbl _ a' k' a HinD' Hr). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP2 & HK).
cbv beta in HK. destruct HK as [(HK0 & HREACH) HMNc]. unfold pf_K0post in HK0.
destruct HK0 as (HROOM2 & Lam' & HpL & HpA & HLED2 & _ & _).
apply (KLK ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
(* ---- what the call kept ---- *)
pose proof (ajxR_ar HJ1) as HARc.
replace (fe_sp0 en + fe_d en + (-128 - fe_d en) + 0) with (fe_sp1 en + 0) in HJc by (unfold fe_sp1, PJF_FR; lia).
assert (HFRc : pf_frameR (SK := SK) B ARx R en ly S Hp W regsc mem mdc k).
{ apply (pfl_frame_same B ARx en ly S Hp W regs regsc mem md mdc k HFR HJ1); apply GR; cbn [In]; tauto. }
assert (Hcs : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv;
  25%bv; 26%bv; 27%bv] -> getr regs2 r = getr regsc r).
{ intros r Hr. apply pfl_pres_bv; [exact HP2|]. cbn [In] in Hr. unfold acallee_saved.
  repeat (destruct Hr as [<- | Hr];
    [ vm_compute; first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
      | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
      | right; right; right; right; right; split; intro Hc; discriminate Hc ] |]); destruct Hr. }
assert (HL' : forall b, In b Lam -> ~ In b D1 -> In b Lam').
{ intros b Hb Hn. pose proof (Permutation_in _ HpL Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
assert (HL'L : forall b, In b Lam' -> In b Lam).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HpL)). apply in_or_app; right; exact Hb. }
assert (NDr : NoDup ((Dk ++ D1 ++ D2) ++ fn_own nd)) by exact (pfl_ndr _ _ ND).
assert (NDl : NoDup (Dk ++ D1 ++ D2)) by exact (pfl_ndl _ _ NDr).
assert (Nown_D1 : forall b, In b (fn_own nd) -> ~ In b D1).
{ intros b Ho H1. apply (pfl_nd_app _ _ b NDr); [apply in_or_app; right; apply in_or_app; left; exact H1 | exact Ho]. }
assert (Nown_D2 : forall b, In b (fn_own nd) -> ~ In b D2).
{ intros b Ho H2. apply (pfl_nd_app _ _ b NDr); [apply in_or_app; right; apply in_or_app; right; exact H2 | exact Ho]. }
assert (ND2_D1 : forall b, In b D2 -> ~ In b D1).
{ intros b H2 H1. exact (pfl_nd_app D1 D2 b (pfl_ndr _ _ NDl) H1 H2). }
assert (NDk_D1 : forall b, In b Dk -> ~ In b D1).
{ intros b Hk H1. apply (pfl_nd_app Dk (D1 ++ D2) b NDl Hk). apply in_or_app; left; exact H1. }
(* a harness block of Lam other than the kids block and D1's: its user bytes miss FP1 *)
assert (HNFP : forall a0 k0 y, In (a0, k0) Lam -> (a0, k0) <> (fn_kids nd, kk) -> ~ In (a0, k0) D1 ->
  a0 <= y < a0 + k0 -> ~ inFP FP1 y).
{ intros a0 k0 y Hin Hne HnD1 Hy Hfp. destruct (HFP1 y Hfp) as [Hv | (a' & k' & Hin' & Hr)].
  - apply (pfl_hb_apart ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 (fn_kids nd) kk y HAR HLED Hin HkLam Hne Hy). lia.
  - assert (Hne' : (a0, k0) <> (a', k')) by (intros Ee; rewrite Ee in HnD1; exact (HnD1 Hin')).
    exact (pfl_hb_apart ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 a' k' y HAR HLED Hin (HD1L _ _ Hin') Hne' Hy Hr). }
(* the kids block's bytes after v's slot miss FP1 *)
assert (HNFPk : forall y, v' + 56 <= y < fn_kids nd + kk -> ~ inFP FP1 y).
{ intros y Hy Hfp. destruct (HFP1 y Hfp) as [Hv | (a' & k' & Hin' & Hr)]; [lia|].
  assert (Hne' : (fn_kids nd, kk) <> (a', k')) by (intros Ee; rewrite Ee in Hk_notD1; exact (Hk_notD1 Hin')).
  exact (pfl_hb_apart ly S Hp W mem md Lam _ _ _ _ _ _ (fn_kids nd) kk a' k' y HAR HLED HkLam (HD1L _ _ Hin') Hne'
    ltac:(lia) Hr). }
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ unfold FP1. rewrite Hv'ne. apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_ablocks_fp.
  apply Forall_forall. intros b Hb. unfold prhPj_hbl in Hb. apply in_map_iff in Hb as ((a' & k') & <- & Hin).
  cbn [fst]. destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED (HD1L _ _ Hin)) as (_ & Ha' & _). lia. }
assert (HFPblk : forall x, inFP FP1 x -> exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m).
{ intros x Hx. destruct (HFPD x Hx) as (a' & k' & _ & Hin & Hr).
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin) as (_ & _ & _ & _ & Hab & _).
  exists (a' - cf_head), (k' + cf_head). split; [exact Hab | exact Hr]. }
assert (HFPLOW : forall x, inFP FP1 x -> x < YM05.alloc_ceiling).
{ intros x Hx. destruct (HFPblk x Hx) as (b & m & Hb & Hr).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & _ & Hcb & _). lia. }
assert (He8 : 0 <= 0 <= 8) by lia.
assert (Esp2 : spZ regs2 = spZ regsc) by (unfold spZ; f_equal; apply Hcs; cbn [In]; tauto).
destruct (pfk_frame B ARx R R PB FX CTX0 en ly S Hp W regsc mem mdc k (STK_pj_free d') 0 FP1 ly2 S2 Hp2 W2 regs2 mem2
  md2 k1 HPRE HFRc HSP HJc HJ2 HSTKF He8 HSINK HFPLOW Esp2 ltac:(apply Hcs; cbn [In]; tauto)
  ltac:(apply Hcs; cbn [In]; tauto) HMNc) as [HFR2 HSP2].
split; [exact En|]. split; [exact Hi|]. split; [exact HFR2|]. split; [exact HSP2|].
split.
{ unfold pf_vregs. unfold w64.
  split; [rewrite (Hcs 8%bv), (GR 8%bv) by (cbn [In]; tauto); exact R8|].
  split; [rewrite (Hcs 9%bv) by (cbn [In]; tauto); rewrite (GQ 9%bv) by pfl_regne;
          apply (pfg_reg_of_U E _ _ _ Q9); apply U8; lia|].
  split; [rewrite (Hcs 18%bv) by (cbn [In]; tauto); rewrite (GQ 18%bv) by pfl_regne;
          apply (pfg_reg_of_U E _ _ _ Q18); apply U8; lia|].
  split; [rewrite (Hcs 19%bv) by (cbn [In]; tauto); rewrite (GQ 19%bv) by pfl_regne;
          apply (pfg_reg_of_U E _ _ _ Q19); apply U8; lia|].
  split; [rewrite (Hcs 23%bv), (GR 23%bv) by (cbn [In]; tauto); exact R23|].
  rewrite (Hcs 22%bv) by (cbn [In]; tauto); rewrite (GQ 22%bv) by pfl_regne.
  apply (pfg_reg_of_U E _ _ _ Q22). apply (Ucell 40); lia. }
split.
{ unfold pf_lregs. unfold w64.
  split; [rewrite (Hcs 20%bv) by (cbn [In]; tauto); rewrite (GQ 20%bv) by pfl_regne;
          apply (pfg_reg_of_U E _ _ _ Q20); apply (Ucell 32); lia|].
  split; [rewrite (Hcs 21%bv) by (cbn [In]; tauto); rewrite (GQ 21%bv) by pfl_regne;
          apply (pfg_reg_of_U E _ _ _ Q21); rewrite U_SLit; reflexivity|].
  split; [rewrite (Hcs 24%bv), (GR 24%bv) by (cbn [In]; tauto); exact R24|].
  split; [rewrite (Hcs 25%bv), (GR 25%bv) by (cbn [In]; tauto); exact R25|].
  split; [rewrite (Hcs 26%bv), (GR 26%bv) by (cbn [In]; tauto); exact R26|].
  rewrite (Hcs 27%bv) by (cbn [In]; tauto); rewrite (GQ 27%bv) by pfl_regne.
  apply (pfg_reg_of_U E _ _ _ Q27). apply (Ucell 24); lia. }
exists (Fd ++ F1), Lam', Dk, D2, F2.
split.
{ apply (pfk_acct_rec B FX en ly S Hp W mem Fd F1 (Dk ++ F2 ++ fn_own nd) Lam D1 ly2 S2 Hp2 W2 mem2 Lam');
  [| exact HROOM2 | exact HpL | exact HpA | exact HLED2 | exact HREACH | exact (proj2 HFD1)].
  rewrite <- !app_assoc in HAC. exact HAC. }
split.
{ apply (pfk_vnode B ARx LAWS VISF R en nd ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d' + 0)
    (fe_sp1 en + 0) FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en) (fe_fail en)
    (fe_ran en) (fe_most en) (fe_own en) HVN HARc HLED HJc HLED2).
  - intros x Hx. destruct (HFPD x Hx) as (a' & k' & HinD' & Hin & Hr).
    exact (pfl_v_apart en nd ly S Hp W mem md Lam _ _ _ _ _ _ a' k' x HVN HAR HLED Hceil0 Hin HinD' Hr).
  - intros b Hb Hnb. pose proof (Permutation_in _ HpA Hb) as H. apply in_app_or in H as [H|H]; [|contradiction].
    unfold prhPj_hbl in H. apply in_map_iff in H as ((a' & k') & <- & Hin).
    exists a', k'. split; [exact (HD1D _ Hin)|]. split; [exact (HD1L _ _ Hin) | reflexivity].
  - intros a0 k0 Hin Hn. apply HL'; [exact Hin|]. intros H1. exact (Hn (HD1D _ H1)).
  - intros a0 k0 Hin. exact (HL'L _ Hin).
  - exact Hceil0.
  - exact HFPblk. }
split.
{ eapply Permutation_trans; [exact HPD|]. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_tail.
  apply Permutation_sym. exact (proj2 HFD1). }
split.
{ (* slot i's key: its word in the keys block, live before and after, outside FP1 *)
  unfold pj_keyR in HKEY |- *. destruct (fn_ks nd) eqn:Eks; [|exact HKEY].
  destruct HKEYSn as [(_ & Hks & _) | (_ & ky & Hky & Hkyn & HDy)]; [congruence|].
  assert (Hown_y : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite HDy; apply in_or_app; right; left; reflexivity).
  assert (HyLam : In (fn_keys nd, ky) Lam).
  { apply (pfl_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
    apply (pfl_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_y. }
  assert (Hyk : (fn_keys nd, ky) <> (fn_kids nd, kk)).
  { intros Ee. assert (NDo : NoDup (fn_own nd)) by exact (pfl_ndr _ _ NDr).
    unfold fn_own in NDo. rewrite HDk, HDy in NDo. rewrite Ee in NDo.
    apply (pfl_nd_app [(fn_kids nd, kk)] ([(fn_kids nd, kk)] ++ fn_Ds nd) (fn_kids nd, kk) NDo); left; reflexivity. }
  destruct HKEY as (x & Hrd & Hx). exists x. split.
  - apply (pfg_u64_keep W W2 mem mem2 _ x Hrd). intros y Hy.
    destruct (pfk_hblkR B ARx LAWS R ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d' + 0) (fe_sp1 en + 0)
      FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fn_keys nd) ky y HARc HLED HJc HLED2 HyLam (HL' _ HyLam (Nown_D1 _ Hown_y)) ltac:(lia)
      (HNFP _ _ y HyLam Hyk (Nown_D1 _ Hown_y) ltac:(lia))) as [Hv _].
    exact Hv.
  - destruct Hx as [Hx | (kx & Hkx & ->)]; [left; exact Hx|]. right. exists kx. split; [|reflexivity].
    apply HL'; [exact Hkx|]. apply NDk_D1. left; reflexivity. }
(* the slots i + 1 .. n - 1 *)
apply (pfk_items B ARx LAWS R d' ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d' + 0) (fe_sp1 en + 0)
  FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
  _ _ _ _ D2 F2 HARc HLED HJc HLED2 HIT2).
- intros x Hx. unfold pf_ofoot in Hx. rewrite Z2Nat.id in Hx by lia.
  destruct Hx as [Hx | [(Hks & Hx) | ((bx & bk) & Hb & Hh)]].
  + split; [apply HNFPk; unfold v' in *; lia|].
    exists (fn_kids nd), kk. split; [exact HkLam|]. split; [exact (HL' _ HkLam Hk_notD1) | lia].
  + destruct HKEYSn as [(_ & Hks' & _) | (_ & ky & Hky & Hkyn & HDy)]; [congruence|].
    assert (Hown_y : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite HDy; apply in_or_app; right; left; reflexivity).
    assert (HyLam : In (fn_keys nd, ky) Lam).
    { apply (pfl_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
      apply (pfl_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_y. }
    assert (Hyk : (fn_keys nd, ky) <> (fn_kids nd, kk)).
    { intros Ee. assert (NDo : NoDup (fn_own nd)) by exact (pfl_ndr _ _ NDr).
      unfold fn_own in NDo. rewrite HDk, HDy in NDo. rewrite Ee in NDo.
      apply (pfl_nd_app [(fn_kids nd, kk)] ([(fn_kids nd, kk)] ++ fn_Ds nd) (fn_kids nd, kk) NDo); left; reflexivity. }
    split; [exact (HNFP _ _ x HyLam Hyk (Nown_D1 _ Hown_y) ltac:(lia))|].
    exists (fn_keys nd), ky. split; [exact HyLam|]. split; [exact (HL' _ HyLam (Nown_D1 _ Hown_y)) | lia].
  + unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
    pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT2 bx bk Hb) as HbL. unfold prh_lin in HbL.
    assert (Hbk : (bx, bk) <> (fn_kids nd, kk)).
    { intros Ee. rewrite Ee in Hb. exact (Nown_D2 _ Hown_k Hb). }
    split; [exact (HNFP _ _ x HbL Hbk (ND2_D1 _ Hb) Hh)|].
    exists bx, bk. split; [exact HbL|]. split; [exact (HL' _ HbL (ND2_D1 _ Hb)) | exact Hh].
- intros x k0 Hin. pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT2 x k0 Hin) as HbL. unfold prh_lin in HbL.
  exact (HL' _ HbL (ND2_D1 _ Hin)).
Qed.

End l.
