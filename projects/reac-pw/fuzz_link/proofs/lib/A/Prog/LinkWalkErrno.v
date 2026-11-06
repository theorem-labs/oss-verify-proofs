(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the journal of fuzz_reply's ASan program walks.  It is the donor's
   journal (Reusable/YCbq.v:351 ajournal) with two extensions the donor's programs never needed, and the
   run chain of Reusable/YC80.v restated over it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_journal.v, with its module paths and module names changed; 226 of its 374 lines of code are new or changed and 747 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: errno on the caller's journal, for the walks of link's own functions that set errno
   themselves (fuzz_socket +0x38..+0x4c, fuzz_send +0x68..+0x7c, fuzz_recv +0x220..+0x234: `jal ___errno_location`, the
   instrumented check of the 4-byte store to a0, `sw rX, 0(a0)`).

   Two pieces:
   - aj_gx_errno_at: the call of ___errno_location (0x90a7c) on ajournal_gx, over the contract
     lib/A/Rt/RtErrnoLoc.v `aerrno_location_realizes` (a0 := tp - 164, every other register and every byte kept),
     lifted with link_ajkit.v aj_gx_call_at at window 0.
   - the program's own store to errno. The run engine of LinkWalk.v (W_journalG.v SRr_run_pi_tok_AJX) admits a write
     window only when each of its bytes is an awr_byte of the journal, a byte of G or an out cell (awr_ok_x), and errno
     is none of these for the caller's G (link_aaddr.v LA_G holds no errno). The journal itself does not track errno:
     its image clause (Reusable/YCbq.v:359) and its ly_extra clause (:367) except [as_errno B, as_errno B + 4). So a
     step that writes errno bytes keeps the journal as soon as the allocator state is kept, which AR's frame law
     (YG0d.v:447-454 AR_frame_law) gives when errno is not a byte the runtime owns: errno is an image byte
     (api_env, PALib's pal_env), so by AR_owned_image_law (YG0d.v:482-483) it is owned iff it is in as_owned_static.
     That fact is the hypothesis ERRF below. On the image instance it is a computation over the static table
     (lib/A/AF0m.v PcapSyms ts_errno, ts_owned; lib/A/AFk0.v errno_not_owned proves the same of TFIB_ERRNO), see
     LinkWalkErrnoInst.v.
     ajournal_errno_only (the donor journal across a change of errno bytes only), ajournal_gx_exec_e (W_journalG.v's
     ajournal_gx_exec with errno bytes admitted beside awr_ok_x's), and the run chain SRr_chain / run / run_to
     _pi_tok_AJXE (W_journalG.v Section e word for word, with awr_ok_xe for awr_ok_x), and their instances at link's
     listing paj_run_xe / paj_run_to_xe (LinkWalk.v's paj_run_x / paj_run_to_x). LinkPaLib's tactics paj_run_tok /
     paj_run_to_tok / psrr_branch_tok take paj_run_xe unchanged.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* ==========================================================================
   Section c: the call of ___errno_location on the journal
   ========================================================================== *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma aj_gx_errno_at : forall pc, aerrno_location_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  sp0 - STK <= spZ regsT -> spZ regsT <= sp0 ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       same_but_materialized mdc md2 /\
       getr regs2 10 = w64 (bv_unsigned (getr regsT 4) - 164) /\
       (forall r, 1 <= r < 32 -> r <> 10 -> getr regs2 (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)) /\
       (forall x, mem2 x = memT x)).
Proof.
intros pc HE G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw HG HJX Hlo Hhi Hra Hraw.
assert (HAR : AR segs B lyc Sc W memT mdc).
{ destruct HJX as (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). }
eapply SRr_mono.
{ apply (aj_gx_call_at SK segs B LAWS segs_low 0 (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md
    own lyc Sc mdc k raw
    (fun regs' mem' md' => AR segs B lyc Sc W mem' md' /\ same_but_materialized mdc md' /\
       getr regs' 10 = w64 (bv_unsigned (getr regsT 4) - 164) /\
       (forall r, 1 <= r < 32 -> r <> 10 -> getr regs' (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)) /\
       (forall x, mem' x = memT x))
    HG HJX ltac:(lia) ltac:(lia) Hhi Hra).
  - intros a [].
  - intros regs' mem' md' (HAR' & Hs & _ & _ & Hm).
    split; [exact HAR'|]. split; [exact Hs|]. split.
    + intros a _ _ _. unfold aview, mbyte, mrestrict. rewrite Hm. reflexivity.
    + intros a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hm. exact Hb.
  - eapply SRr_mono; [apply (HE lyc Sc W regsT memT mdc HAR); rewrite Hra; exact Hraw|].
    cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & -> & HAR' & Hs & H10 & Hr & Hm).
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
    exact (conj HAR' (conj Hs (conj H10 (conj Hr Hm)))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & Hs & H10 & Hr & Hm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
exact (conj HJ2 (conj Hs (conj H10 (conj Hr Hm)))).
Qed.
End c.

(* ==========================================================================
   Section e: a write of errno bytes on the journal
   ========================================================================== *)
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ENV : api_env segs B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

Definition aerrno (a : Z) : Prop := as_errno B <= a < as_errno B + 4.
Definition aerrnob (a : Z) : bool := (as_errno B <=? a) && (a <? as_errno B + 4).
Lemma aerrnob_spec : forall a, aerrnob a = true <-> aerrno a.
Proof.
intros a. unfold aerrnob, aerrno. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.
Lemma aerrnob_false : forall a, aerrnob a = false <-> ~ aerrno a.
Proof.
intros a. split.
- intros H HE. apply aerrnob_spec in HE. congruence.
- intros H. destruct (aerrnob a) eqn:E; [exfalso; apply H; apply aerrnob_spec; exact E | reflexivity].
Qed.
Lemma aerrno_img : forall a, aerrno a -> in_img segs a.
Proof. intros a Ha. exact (proj1 (proj2 ENV) a Ha). Qed.
Lemma aerrno_low : forall a, aerrno a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (proj1 ENV). unfold aerrno in Ha. lia. Qed.

(* The donor journal across a step that changes errno bytes only. *)
Lemma ajournal_errno_only : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc',
  ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall x : word, ~ aerrno (bv_unsigned x) -> memc' x = memc x) ->
  mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' HJ Hout Hgr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof (proj1 ENV) as [He0 He1].
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ aerrno a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha Hn. apply aview_eq_of. unfold mrestrict. rewrite Hout; [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (HAR' : AR segs B lyc Sc Wc memc' mdc).
{ eapply (al_frame _ _ LAWS); [exact HAR | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. apply Heqw; [exact Ha|]. intros HEa.
    apply (ERRF a HEa). exact (proj1 (al_owned_image _ _ LAWS lyc Sc Wc memc mdc a HAR (aerrno_img a HEa)) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
  - intros a _ Hh. apply Hout. intros HEa. unfold w64 in Hh.
    rewrite (hidden_not_img segs Wc (Z_to_bv 64 a) (aerrno_img _ HEa)) in Hh. discriminate. }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [lia|]. unfold aerrno. lia. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & _ & _ & _).
  apply Heqw; [lia|]. intros HEa.
  exact (blk_img segs B LAWS lyc Sc Wc memc mdc p n (p + i) HAR H2 ltac:(lia) (aerrno_img _ HEa)). }
split.
{ intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi).
  apply Heqw; [lia | exact He]. }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  destruct Hr as [Hr | Hr].
  - apply Heqw; [lia|]. intros HEa.
    exact (frm_img segs B LAWS lyc Sc Wc memc mdc cid pos a HAR HinC ltac:(lia) (aerrno_img _ HEa)).
  - apply Heqw; [lia|]. unfold aerrno. lia. }
split; [exact Hgone|].
split; [intros a Ha; eapply apresent_grows; [exact Hgr | apply Hpres, Ha]|].
split; [exact Hstatic|]. split; [|exact HQT].
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply Heqw; [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | exact He].
Qed.

(* awr_ok_x with errno bytes admitted too *)
Definition awr_ok_xe (E : env) (rs : smem) (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z))
(STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) (ly : alayout) (own : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a ->
((awr_byte STK sp0 FP bl0 blc ly own a /\ ~ (sp0 <= a < sp0 + XO)) \/ inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO))
\/ aerrno a.
Lemma awr_ok_xe_of_x : forall E rs G XO OUT STK sp0 FP bl0 blc ly own,
  awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own -> awr_ok_xe E rs G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E rs G XO OUT STK sp0 FP bl0 blc ly own H a Ha. left. exact (H a Ha). Qed.
Lemma awr_ok_xe_nil : forall E G XO OUT STK sp0 FP bl0 blc ly own, awr_ok_xe E [] G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E G XO OUT STK sp0 FP bl0 blc ly own a (r & Hin & _). destruct Hin. Qed.
Lemma awr_ok_xe_cons : forall E r rs G XO OUT STK sp0 FP bl0 blc ly own,
  (forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
   ((awr_byte STK sp0 FP bl0 blc ly own a /\ ~ (sp0 <= a < sp0 + XO)) \/ inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO))
   \/ aerrno a) ->
  awr_ok_xe E rs G XO OUT STK sp0 FP bl0 blc ly own -> awr_ok_xe E (r :: rs) G XO OUT STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs G XO OUT STK sp0 FP bl0 blc ly own H1 H2 a (r' & Hin & Hr). destruct Hin as [<- | Hin].
- exact (H1 a Hr).
- apply H2. exists r'. split; [exact Hin | exact Hr].
Qed.

(* W_journalG.v's ajournal_gx_exec with errno bytes admitted. *)
Lemma ajournal_gx_exec_e : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall x : word, w_H Wc x = true -> memc' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> ((awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) \/ aerrno a) ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HG HJ Hfr Hgr Hhid Hsame HW.
set (memM := fun x : word => if aerrnob (bv_unsigned x) then memc x else memc' x).
assert (EMe : forall x, aerrnob (bv_unsigned x) = true -> memM x = memc x)
  by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (EMn : forall x, aerrnob (bv_unsigned x) = false -> memM x = memc' x)
  by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (HJM : ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memM mdc' k).
{ apply (ajournal_gx_exec segs B LAWS segs_low G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memM mdc'
    (fun a => Wr a /\ ~ aerrno a) HG HJ).
  - intros x Hx. destruct (aerrnob (bv_unsigned x)) eqn:Ee.
    + unfold mrestrict. rewrite (EMe x Ee). reflexivity.
    + unfold mrestrict. rewrite (EMn x Ee). apply aerrnob_false in Ee.
      pose proof (Hfr x ltac:(intros HWx; apply Hx; split; [exact HWx | exact Ee])) as E. unfold mrestrict in E. exact E.
  - intros x Hx. pose proof (Hgr x) as Hg1. unfold mrestrict in Hx, Hg1 |- *.
    destruct (w_H Wc x); [exact Hx|]. destruct (aerrnob (bv_unsigned x)) eqn:Ee.
    + rewrite (EMe x Ee). exact Hx.
    + rewrite (EMn x Ee). exact (Hg1 Hx).
  - intros x Hh. destruct (aerrnob (bv_unsigned x)) eqn:Ee; [exact (EMe x Ee)|]. rewrite (EMn x Ee). exact (Hhid x Hh).
  - exact Hsame.
  - intros a [HWa Hn]. destruct (HW a HWa) as [H | H]; [exact H | exfalso; exact (Hn H)]. }
destruct HJM as (HSTK & HXO & (memS & HJi & Hag) & Hout).
assert (Hgr2 : mem_grows (mrestrict (w_H Wc) memM) (mrestrict (w_H Wc) memc')).
{ intros x Hx. pose proof (Hgr x) as Hg1. unfold mrestrict in Hx, Hg1 |- *.
  destruct (w_H Wc x); [exact Hx|]. destruct (aerrnob (bv_unsigned x)) eqn:Ee.
  - rewrite (EMe x Ee) in Hx. exact (Hg1 Hx).
  - rewrite (EMn x Ee) in Hx. exact Hx. }
pose proof (ajournal_errno_only _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memc' HJi
  ltac:(intros x Hx; symmetry; apply EMn; apply aerrnob_false; exact Hx) Hgr2) as HJ2.
apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k memS HSTK HXO HJ2 Hag).
intros a Ha Hno. rewrite <- (Hout a Ha Hno).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
apply aview_eq_of. unfold mrestrict. rewrite (EMn (Z_to_bv 64 a)); [reflexivity|].
apply aerrnob_false. rewrite unsigned_lit_small by lia. pose proof (proj1 ENV). unfold aerrno. lia.
Qed.

(* A kept clause that also excepts errno is the kept clause: akept's image clause excepts errno already, and errno
   is no byte of its other clauses (above the ceiling, a heap block, a side frame or its shadow). A walk whose run
   stores errno shows the kept clause with errno excepted (LinkWalk.v apost_leaf at E \/ aerrno) and gives the
   contract's apost by this. *)
Lemma akept_errno : forall lyc Sc W memc mdc W2 mem2 slo shi (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  akept segs B lyc Sc W memc W2 mem2 slo shi (fun a => E a \/ aerrno a) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof.
intros lyc Sc W memc mdc W2 mem2 slo shi E HAR (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof (proj1 ENV) as [He0 He1].
split; [|split; [|split; [|split]]].
- intros a Ha Hn HE. apply K1; [exact Ha | exact Hn |]. intros [H|H]; [exact (HE H) | unfold aerrno in H; lia].
- intros b m i Hin Hi HE. apply (K2 b m i Hin Hi). intros [H|H]; [exact (HE H)|].
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hc & _).
  exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hin ltac:(lia) (aerrno_img _ H)).
- intros a Hi Hno Herr HE. apply K3; [exact Hi | exact Hno | exact Herr |]. intros [H|H]; [exact (HE H) | exact (Herr H)].
- intros cid pos a Hin Hr HE. apply (K4 cid pos a Hin Hr). intros [H|H]; [exact (HE H)|].
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) (aerrno_img _ H)).
  + pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb. unfold aerrno in H. lia.
- split; [exact K5 | exact K6].
Qed.

Lemma apost_errno : forall K EV (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2,
  AR segs B lyc Sc W memc mdc ->
  apost SK segs B K EV (fun a => E a \/ aerrno a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W2 c2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2.
Proof.
intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q W2 c2 HAR
  (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & HP & Hfr & Hfd & Hfs & HK & HSK & HQ).
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|]. split; [exact Hfr|]. split; [exact Hfd|].
split; [exact Hfs|]. split; [exact (akept_errno lyc Sc W memc mdc W2 mem2 _ _ E HAR HK)|].
split; [exact HSK | exact HQ].
Qed.
End e.

(* ==========================================================================
   Section r: the run chain of W_journalG.v Section e with awr_ok_xe
   ========================================================================== *)
Section r.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ENV : api_env segs B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok segs B G.
Variable XO : Z.
Variable OUT : list (Z * Z).
Local Notation ajournal_gx := (ajournal_gx segs B G XO OUT).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
Local Notation run_post := (run_post_pi_tok_AJX psym segs B val sigma A_LIM G XO OUT).

Lemma SRr_chain_pi_tok_AJXE : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok_xe B E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_gx_exec_e segs B LAWS segs_low ENV ERRF G XO OUT) with (Wr := in_wrange E (ss_mem ss)); [exact HG | exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJXE : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_xe B E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJXE; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJXE : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_xe B E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJXE; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End r.

(* ==========================================================================
   Section g: the errno-tolerant run instances at LINK's listing (LinkWalk.v's paj_run_x / paj_run_to_x)
   ========================================================================== *)
Section g.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis ENV : api_env pa_segs B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

Definition paj_run_xe (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_pi_tok_AJXE lsym pa_segs B LAWS pa_segs_low ENV ERRF pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition paj_run_to_xe (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_to_pi_tok_AJXE lsym pa_segs B LAWS pa_segs_low ENV ERRF pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
End g.
End a.
