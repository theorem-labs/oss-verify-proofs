(* plugin-hostd/fuzz_reply.asan_ubsan, image B: the image-B twin of lib/A/CfRBridgeRulesFreeRh.v, under lib/B so the B
   tree is self-contained: the A file's text (a Theorem Labs lane's re-fit, a working branch
   c9793e3d61f5) with, in its code, the lib/B modules for lib/A's (A's CfParamsReply kept),
   CfImg_B, YB1v.tfibsegs, ReplyKfMeterB.MT_sec and the B target ReplyAllocTargetsB.afree_target_replyB in the fit Goal.
   The comments below are the A file's and cite lib/A. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (route R, the FREE half of Section TOPK at R; new file). rule 24: proves no function (kind:
   invariant lemma; the route-R free(NULL) crossing rule and the TOPK free rules at R over the journal).

   (a) aj_free_null_at_x_ct_rh is lib/A/CfRBridgeAjFreeN.v:71-88 aj_free_null_at_x_ct at R := wle' segs RZ_cf, the
       free(NULL) twin of lib/A/CfRBridgeFreeRh.v aj_free_at_x_ct_rh. Against aj_free_null_at_x_ct's text it changes,
       and only:
       - the realization afree_realizes_cf is afree_realizes_cf_rh segs B (lib/A/YG0dcfR.v:61; it covers p = PNull,
         its premise `p = PNull \/ In (p, n) (blocks S)`);
       - both journals are ajournal_xR segs B PST ARxs (wle' segs RZ_cf), the step is SRrG segs (wle' segs RZ_cf);
       - the post's leaf free_leaf_x segs B ARxs is free_leaf_cf_rh segs B (YG0dcfR.v:46), as aj_free_at_x_ct_rh does.
       QMm_cf segs B Sc memT is taken BY NAME, unchanged; the proof reads it only through YGcallcf's QMQ_cf and
       acall_pre_x_xs (in afree_realizes_x_xs_rh), so no memnorm use. The proof is aj_free_null_at_x_ct's with
       aj_free_at_x_ct_rh's R steps: afree_realizes_x_xs_rh (CfRBridgeFreeRh.v), amreal'_SRr'04, SRrG_mono, the callee
       journal from call_effect_journal_rh_cf_pst (lib/A/AjxCallRh.v:183) with the empty footprint, ajournal_x_subR
       with wle'_trans segs RZ_cf, acall_kept_of_journal_xR, and the projection free_leaf_x_xs_cf_rh.
   (b) AFREE_x_kf_rh / AFREEN_x_kf_rh are lib/A/CfRBridgeRules.v Section TOPK's AFREE_x_kf / AFREEN_x_kf at
       R := wle' segs RZ_cf: the conclusions are W_journal_x.v's afree_cf_rule_c_xR / afree_null_cf_rule_c_xR at
       RO := arodata_ok_cf segs TfibB and R := wle' segs RZ_cf, the premise is the primed realizer
       afree_realizes_cf_rh segs TfibB (ReplyAllocTargets.v afree_target_reply's body; the fit Goal at the end). The
       section header is TOPK's (CfF1's fit, a working branch 9118a6a96818), VERBATIM: top_x's relation
       ARX after W1 (its last conjunct arodata_ok_cf on the memory) with TOPK's FIT CHECK Goal, the meter equations
       including MT_ok, and the image rows HRS / HER. The witness Goals at the end (Section W) show the meter
       hypotheses the free rules use at the real instance MT := ReplyKfMeter.MT_sec YGcfNames.nsec_cf cf_kmax.
       They are proved, as the strict ones, through the room forms AFREE_x_room_rh / AFREEN_x_room_rh, CfRBridgeRules.v
       Section B's AFREE_x_room / AFREEN_x_room at R: both journals ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf),
       the step SRrG segs (wle' segs RZ_cf), and the rule's call-boundary premise `arodata_ok_cf segs TfibB memT ->`
       right after chain_pre (W_journal_x.v afree_cf_rule_c_xR / afree_null_cf_rule_c_xR; part 3c removed their memnorm
       premise). Section B's hypotheses verbatim (MO_OK_HULL_M / MO_OK_HULL_F, HRS / HER included). The proofs are the
       strict ones (CfF1's) over aj_free_at_x_ct_rh / aj_free_null_at_x_ct_rh: arodata at the call from the journal's
       ARX, cf_hull_ok from MO_OK_HULL_F, arodata at the post by arodata_post_keep from the primed leaf's raw frame,
       a Theorem Labs lane's journal copies aj_to_xs_xR / aj_of_xs_xR (lib/A/CfRBridgeRulesRh.v, aj_of_xs_xR taking the post's
       arodata) at R := wle' segs RZ_cf; the primed leaf's post is read through acall_post_cf_rh_unfold (ARcf at the
       post, ARxs by xs_placed_of_ARcf).
   The names this file uses from CfRBridgeRules.v (CfF1's fit) are that file's own, by Require (qualified):
   CfRBridgeRules.ablock_not_img_cfr, arodata_post_keep, img_visible, aview_img_eq, cb_cf, RP_cf, cnt_ok_cb_cf,
   kf_MO_LE_F, kf_MO_OK_HULL_F. They replace the restatements with the suffix _rh that this file carried while
   CfRBridgeRules.v did not compile; each restatement converted to its strict name (both directions) before they were
   dropped. CfRBridgeAjFreeN.v is not Required.
   Event terms: st_nev appears only in the journal index k + (st_nev S2 - st_nev Sc) of (a) and, in the proofs, in the
   call journal's index and in free_cf_nev's tick (k + 1), as YGcallx.v / CfRBridgeRules.v (exception 3, the tick
   update). No address, no ledger, no image numeral: 0 is the NULL pointer and the request size, 10 / 1 / 3 / 4 are
   RISC-V register numbers, 16 / 4096 / 16384 cgif's LENGTH constants (YGcallx.v:88-90), 1024 / 2 ^ 15 (= 32768)
   top_x's count fields (ReplyCnt.v), 64512 the primary cutoff in TOPK's MT_malloc (ReplyKfMeter.v sec_lit), copied. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0dH YG0dHc YCbq YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YGcallcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x YD2l YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt ReplyLSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfRBridgeCtxB CfRBridgePrimB CfRBridgeNevB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRehidePost YG0dcfR AjxCallRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfRBridgeFreeRhB CfRBridgeRulesRhB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyAllocTargetsB YB1v ReplyKfMeterB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNsec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CfRBridgeRulesB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* (a) The free(NULL) crossing rule at R := wle' segs RZ_cf.                       *)
Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).
(* YGcallcf.v's relation, verbatim (CfRBridgeAjFreeN.v:68) *)
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

(* CfRBridgeAjFreeN.v:71 aj_free_null_at_x_ct at R := wle' segs RZ_cf, re-hiding (changes in the header). *)
Lemma aj_free_null_at_x_ct_rh : afree_realizes_cf_rh segs B ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists trc, apath (free_cf PNull (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_cf_rh segs B lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros AFCF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
(* the Section r laws of YGcallx.v at ARxs (YGcallcf.v), and the primed contract at ARxs *)
pose proof L as LAWS. apply AR_laws_x_xs in LAWS.
pose proof L as OWNLOW. apply ARx_owned_low_law_xs in OWNLOW.
pose proof (ARx_wf_law_xs segs B) as WFL.
pose proof HU as AMX. apply alloc_model_laws_x_cf in AMX.
pose proof (afree_realizes_x_xs_rh segs B AFCF) as AFREE.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
assert (E0 : sptr_addr B lyc PNull = 0) by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
(* 0 is in no ghost list: each entry is a live block's base (amc_hp_live), at least 4096 (the blocks law) *)
assert (Hnhp : ~ In (sptr_addr B lyc PNull) Hpc).
{ rewrite E0. intros Hin0.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ (proj1 (proj1 HAR))) 0 Hin0) as (kc & Hkc & Hst & Eq & _).
assert (Hb : In (0, ck_req kc) (ablocks B lyc Sc)).
{ apply (proj2 (In_ablocks B lyc Sc 0 (ck_req kc))). exists kc.
split; [exact Hkc|]. split; [exact Hst|]. split; [symmetry; exact Eq | reflexivity]. }
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memT mdc 0 (ck_req kc) HAR Hb) as (_ & H4096 & _). lia. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
destruct AMX as [_ AMF].
pose proof (AMF Sc PNull 0 (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) HWF (QMQ_cf segs B Sc memT HQM)
  (or_introl eq_refl)
  (admits_fix _ _ Sc HU Htr))
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc PNull 0 ch HPRE (or_introl eq_refl) ltac:(rewrite E0; exact Ha0)
Hnhp (admits_fix _ _ Sc HU Htr)) as HREAL.
eapply SRrG_mono.
{ exact (amreal'_SRr'04 segs RZ_cf _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
(* the model keeps the blocks; its split arm would make (0, 0) a live block *)
assert (Hbl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ Hs] | Hsplit]; [rewrite Hbl2; exact Hs|].
exfalso.
assert (Hb : In (0, 0) (ablocks B lyc Sc)).
{ unfold ablocks. apply in_map_iff. exists (PNull, 0). split; [reflexivity|].
rewrite Hsplit. apply in_or_app. right. left. reflexivity. }
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memT mdc 0 0 HAR Hb) as (_ & H4096 & _). lia. }
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
(* the primed post: its world (wle_in over the call's dead set) and frame (off that set) are the callee journal's
   two premises that differ from acall_post_journal_x's *)
pose proof HPOST as (HAR2 & Hly2 & Hwin2 & HP & Hio2 & Hfr2 & Hpres2).
destruct (alx_layout _ _ _ LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ rewrite <- Eab. unfold ablocks. rewrite Hbl. reflexivity. }
(* the callee journal at PST = [] (call_effect_journal_rh_cf_pst): the leaf's frame set is empty at PNull, XW and the
   footprint are empty *)
assert (HJ1 : ajournal_xR segs B [] ARxs (wle' segs RZ_cf) ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ apply (call_effect_journal_rh_cf_pst segs B ARxs LAWS segs_low errno_low OWNLOW [] ASTACK lyc Sc Hpc W regsT memT mdc
  ly2 S2 Hpc W2 mem2 md2
  (fun a => PNull <> PNull /\ sptr_addr B lyc PNull <= a < sptr_addr B lyc PNull + req_size 0) (fun _ => False)
  [] [] (st_nev S2 - st_nev Sc));
  [exact HAR2 | exact Hly2 | exact Hwin2 | exact Hio2 | exact Hfr2 | exact Hpres2 | exact HAR | exact (proj1 HAR)
  | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | intros a [] | | | exact HQT2].
  - intros a [Hc _]. exfalso. exact (Hc eq_refl).
  - intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARxs LAWS segs_low (wle'_trans segs RZ_cf));
[exact HJ | eapply ajournal_x_nil_pstR; exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|].
split; [rewrite Eab2; apply Permutation_refl|].
split; [exact Hfrs2|].
split; [exact HPRE|].
split; [exists tr; split; [exact Hpath|]; split;
  [exact Hgf | exact (free_leaf_x_xs_cf_rh segs B _ _ _ _ _ _ _ _ _ _ _ _ Hleaf0)]|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR segs B ARxs segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

End n.

(* ---------------------------------------------------------------------------- *)
(* (b), room level: CfRBridgeRules.v Section B's free rules at R.                  *)
Section BR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.

(* CfRBridgeRules.v Section B's header (CfF1's fit), verbatim (its cb_cf is CfRBridgeRules.cb_cf). *)
Variable RM : astate -> nat -> Prop.
Variable CNT : list (Z * Z) -> Prop.
Hypothesis HRM : RM = fun S _ => room_live_cf S.
Hypothesis HCNT : forall l, CNT l -> CfRBridgeRulesB.cb_cf l.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Hypothesis MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
Hypothesis MO_LE_F : forall s s', nsec_cf s' <= nsec_cf s -> mo_le MT s s' (mo_free MT).
Hypothesis MO_LE_R : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n + mo_free MT).
(* The hull admission at the call (QMm_cf's cf_hull_ok), from the rule's own count premise: at a meter whose mo_ok bounds
   the count (MT_sec: nsec_cf s + m <= cf_kmax) with a nonnegative charge (Section TOPK derives both). *)
Hypothesis MO_OK_HULL_M : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n) -> cf_hull_ok s.
Hypothesis MO_OK_HULL_F : forall s, mo_ok MT s (mo_free MT) -> cf_hull_ok s.
(* The unit's two image rows the read-only data keep reads (YG0ncf.v): the read-only data lie in a segment, and errno's
   cell is apart from them. *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

(* top_x's relation (W_LLVMFuzzerTestOneInput_top_x.v:175-176 after W1: its last conjunct is arodata_ok_cf on the
   memory) and YGcallcf's (:218). *)
Local Abbreviation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf segs TfibB ly S Hp W mem md /\ Hp = [] /\ arodata_ok_cf segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

(* CfRBridgeRules.v Section B's AFREE_x_room at R (header (b)). *)
Definition AFREE_x_room_rh : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch (kr : nat),
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks TfibB lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
arodata_ok_cf segs TfibB memT ->
In (raZ regsT :: spine ch) CTX_AFREE ->
RM Sc (1 + kr) ->
CNT (ablocks TfibB lyc Sc) ->
(In (pa, n) (ablocks TfibB ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code TfibB))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks TfibB lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks TfibB ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ (pa <= a < pa + req_size n) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem AFREE_x_room_of_cf_rh : afree_realizes_cf_rh segs TfibB -> AFREE_x_room_rh.
Proof.
intros AF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch kr
  HJ Hin Ha0 Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HRO HCTX HRL HCB HFP HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & _).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_F Sc HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc Hpc W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_afree lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs_xR segs (wle' segs RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (Hnhp : ~ In pa Hpc) by (rewrite HHp; intros []).
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
pose proof (aj_free_at_x_ct_rh segs TfibB [] L segs_low errno_low HU AF
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch HJx Hin Hnhp Ha0 Hsp Hal Hneg Hbud
  Hgp Htp Hra Hraw HQM Hch Htr HFP) as HSR.
assert (HARxs : ARxs lyc Sc Hpc W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc)).
eapply SRrG_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & Hc2' & HJ2 & Hpres & Hsplit & Hfrs & HPRE & Htr2 &
  (q & trc & Hq & Hqin & Hpath & Hgf & Hleaf) & Hkept).
pose proof (free_cf_nev q _ Sc trc S2 Hpath) as Hnev.
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HPOST & HQT2 & HERR & HRAW).
cbn [fst snd] in HRAW.
assert (Emem : mem2 = mem') by (rewrite Hc2' in Hc'; unfold cfg_at in Hc'; injection Hc'; intros; congruence).
(* the primed post is ARcf at the post (acall_post_cf_rh_unfold); ARxs by xs_placed_of_ARcf *)
rewrite (acall_post_cf_rh_unfold segs TfibB) in HPOST. destruct HPOST as (HARc2 & _).
assert (HARxs2 : ARxs ly' S2 Hpc W2 mem' md') by exact (conj HARc2 (xs_placed_of_ARcf segs TfibB ly' S2 Hpc W2 mem' md' HARc2)).
pose proof HPRE as (_ & _ & _ & HSLO & _).
(* the post's arodata, from the leaf's raw frame: the freed block is a live block of the call state, off the image *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ rewrite Emem.
  apply (CfRBridgeRulesB.arodata_post_keep segs TfibB lyc Sc Hpc W regsT memT mdc ly' S2 Hpc W2 mem' md'
    (fun a => q <> PNull /\ sptr_addr TfibB lyc q <= a < sptr_addr TfibB lyc q + req_size n)
    HRS HER HARc HARc2 HSLO); [| |exact HAD].
  - intros a I1 I2 X1 X2 [_ Hb]. rewrite Hq in Hb.
    exact (CfRBridgeRulesB.ablock_not_img_cfr TfibB lyc Sc Hpc _ pa n a (proj1 HARc) Hin I1 Hb).
  - intros x NX. apply HRAW; intros H; apply NX; tauto. }
exists ly2, S2, Hpc, regs2, mem2, md2.
split; [exact Hc2'|].
split.
{ apply (aj_of_xs_xR segs (wle' segs RZ_cf)); [exact HHp | exact HAD2 |].
  replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hsplit|]. split; [exact Hfrs|].
split; [exact Hkept|].
split; [exact (MO_LE_F Sc S2 (cfx_ipost_apath _ _ trc (tt, S2) (nsec_free_cf q _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_intror (or_introl (ex_intro _ q (ex_intro _ _ (ex_intro _ trc Hpath)))))). }
split.
{ intros i Hi. rewrite Emem. apply (CfRBridgeRulesB.aview_img_eq segs segs_low).
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (HERR i Hi). }
intros a Hi Ho1 Ho2 He Hb [Hh (b & Hm)].
pose proof (segs_low a Hi) as Ha.
split; [exact (CfRBridgeRulesB.img_visible segs segs_low W2 a Hi)|]. exists b. rewrite Emem. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc Hpc W memT mdc a HARxs Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc Hpc W memT mdc HARxs)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  destruct HPRE as (_ & _ & _ & Hslo & _).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [_ Hblk]. apply Hb. rewrite <- Hq. exact Hblk.
Qed.

(* CfRBridgeRules.v Section B's AFREEN_x_room at R (header (b)). *)
Definition AFREEN_x_room_rh : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch (kr : nat),
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
arodata_ok_cf segs TfibB memT ->
In (raZ regsT :: spine ch) CTX_AFREE ->
RM Sc (1 + kr) ->
CNT (ablocks TfibB lyc Sc) ->
mo_ok MT Sc (mo_free MT) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code TfibB))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs TfibB [] ARX (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks TfibB ly2 S2) (ablocks TfibB lyc Sc) /\
frames S2 = frames Sc /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
mo_le MT Sc S2 (mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem AFREEN_x_room_of_cf_rh : afree_realizes_cf_rh segs TfibB -> AFREEN_x_room_rh.
Proof.
intros AF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch kr
  HJ Ha0 Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HRO HCTX HRL HCB HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & _).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_F Sc HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc Hpc W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_afree lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs_xR segs (wle' segs RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
pose proof (aj_free_null_at_x_ct_rh segs TfibB [] L segs_low errno_low HU AF
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch HJx Ha0 Hsp Hal Hneg Hbud
  Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
assert (HARxs : ARxs lyc Sc Hpc W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc)).
eapply SRrG_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & Hc2' & HJ2 & Hpres & Hperm & Hfrs & HPRE &
  (trc & Hpath & Hgf & Hleaf) & Hkept).
pose proof (free_cf_nev PNull _ Sc trc S2 Hpath) as Hnev.
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HPOST & HQT2 & HERR & HRAW).
cbn [fst snd] in HRAW.
assert (Emem : mem2 = mem') by (rewrite Hc2' in Hc'; unfold cfg_at in Hc'; injection Hc'; intros; congruence).
(* the primed post is ARcf at the post (acall_post_cf_rh_unfold); ARxs by xs_placed_of_ARcf *)
rewrite (acall_post_cf_rh_unfold segs TfibB) in HPOST. destruct HPOST as (HARc2 & _).
assert (HARxs2 : ARxs ly' S2 Hpc W2 mem' md') by exact (conj HARc2 (xs_placed_of_ARcf segs TfibB ly' S2 Hpc W2 mem' md' HARc2)).
pose proof HPRE as (_ & _ & _ & HSLO & _).
(* the post's arodata, from the leaf's raw frame: free(NULL) has no block exception *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ rewrite Emem.
  apply (CfRBridgeRulesB.arodata_post_keep segs TfibB lyc Sc Hpc W regsT memT mdc ly' S2 Hpc W2 mem' md'
    (fun a => PNull <> PNull /\ sptr_addr TfibB lyc PNull <= a < sptr_addr TfibB lyc PNull + req_size 0)
    HRS HER HARc HARc2 HSLO); [| |exact HAD].
  - intros a I1 I2 X1 X2 [Hc _]. exact (Hc eq_refl).
  - intros x NX. apply HRAW; intros H; apply NX; tauto. }
exists ly2, S2, Hpc, regs2, mem2, md2.
split; [exact Hc2'|].
split.
{ apply (aj_of_xs_xR segs (wle' segs RZ_cf)); [exact HHp | exact HAD2 |].
  replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hperm|]. split; [exact Hfrs|].
split; [exact Hkept|].
split; [exact (MO_LE_F Sc S2 (cfx_ipost_apath _ _ trc (tt, S2) (nsec_free_cf PNull _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_intror (or_introl (ex_intro _ PNull (ex_intro _ _ (ex_intro _ trc Hpath)))))). }
split.
{ intros i Hi. rewrite Emem. apply (CfRBridgeRulesB.aview_img_eq segs segs_low).
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (HERR i Hi). }
intros a Hi Ho1 Ho2 He [Hh (b & Hm)].
pose proof (segs_low a Hi) as Ha.
split; [exact (CfRBridgeRulesB.img_visible segs segs_low W2 a Hi)|]. exists b. rewrite Emem. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc Hpc W memT mdc a HARxs Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc Hpc W memT mdc HARxs)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  destruct HPRE as (_ & _ & _ & Hslo & _).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [Hc _]. exact (Hc eq_refl).
Qed.

End BR.

(* ---------------------------------------------------------------------------- *)
(* (b) KF-COUNT at R: CfRBridgeRules.v Section TOPK's free rules at R := wle' segs RZ_cf. The header is TOPK's     *)
(*    (CfF1's fit), verbatim, FIT CHECK Goal included.                                                               *)
Section TOPK_rh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_B segs TfibB mem).
(* FIT CHECK of the relation: the rules' ARX is top_x's relation after W1, whose text is quoted
   here VERBATIM from commit b27e847023f8, lib/A/W_LLVMFuzzerTestOneInput_top_x.v:171-172
   (Definition ARX's body); it closes by reflexivity only if the two are the same term. *)
Goal ARX = (
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem).
Proof. reflexivity. Qed.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
(* MT_sec's defining equations, its literal text (ReplyKfMeter.v at a968c6e24aec: mkAMeter (fun s m => nsec s + m <= KMAX)
   (fun s s' m => nsec s' <= nsec s + m) (fun n => if 64512 <? n then 1 else 0) 0); each holds by reflexivity at
   MT := MT_sec nsec_cf cf_kmax.  mo_ok is not used by these rules' posts. *)
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.
Hypothesis MT_le : forall s s' m, mo_le MT s s' m <-> nsec_cf s' <= nsec_cf s + m.
(* MT_sec's fourth defining equation, its mo_ok (MT_ok, the same text route R's TOPK_rh takes, commit
   07260ccc92a1 lib/A/CfRBridgeRulesRhTop.v:267): at MT := MT_sec YGcfNames.nsec_cf cf_kmax it holds by iff_refl. *)
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
(* The unit's two image rows (Section B's HRS / HER). *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

(* Section TOPK's kf_meter, its alternatives for the free rules' Section B hypotheses (TOPK's kf_MO_LE_F and
   kf_MO_OK_HULL_F at this header's MT / nsec_cf / MT_free / MT_le / MT_ok). *)
Ltac kf_meter_rh := first [ exact nsec_malloc_cf | exact nsec_free_cf
  | exact (CfRBridgeRulesB.kf_MO_LE_F MT nsec_cf MT_free MT_le) | exact (CfRBridgeRulesB.kf_MO_OK_HULL_F MT MT_free MT_ok)
  | exact HRS | exact HER ].

(* CfRBridgeRules.v Section TOPK's AFREE_x_kf at R := wle' segs RZ_cf. *)
Theorem AFREE_x_kf_rh : afree_realizes_cf_rh segs TfibB ->
  afree_cf_rule_c_xR segs TfibB [] ARX MT CfRBridgeRulesB.RP_cf (arodata_ok_cf segs TfibB) CTX_AFREE (wle' segs RZ_cf).
Proof.
intros AF. eapply (AFREE_x_room_of_cf_rh segs L segs_low errno_low (rp_RM CfRBridgeRulesB.RP_cf)
  (cnt_ok CfRBridgeRulesB.RP_cf) eq_refl CfRBridgeRulesB.cnt_ok_cb_cf MT nsec_cf); first [exact AF | kf_meter_rh].
Qed.

(* CfRBridgeRules.v Section TOPK's AFREEN_x_kf at R := wle' segs RZ_cf. *)
Theorem AFREEN_x_kf_rh : afree_realizes_cf_rh segs TfibB ->
  afree_null_cf_rule_c_xR segs TfibB [] ARX MT CfRBridgeRulesB.RP_cf (arodata_ok_cf segs TfibB) CTX_AFREE (wle' segs RZ_cf).
Proof.
intros AF. eapply (AFREEN_x_room_of_cf_rh segs L segs_low errno_low (rp_RM CfRBridgeRulesB.RP_cf)
  (cnt_ok CfRBridgeRulesB.RP_cf) eq_refl CfRBridgeRulesB.cnt_ok_cb_cf MT nsec_cf); first [exact AF | kf_meter_rh].
Qed.
End TOPK_rh.

(* FIT: the free target (ReplyAllocTargets.v afree_target_reply) is the premise of AFREE_x_kf_rh / AFREEN_x_kf_rh at
   segs := tfibsegs and TOPK_rh's instances CfImg_A / CfParams_reply. *)
Goal ReplyAllocTargetsB.afree_target_replyB -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @afree_realizes_cf_rh fx rc CfImg_B CfParams_reply YB1v.tfibsegs TfibB.
Proof. exact (fun h => h). Qed.

(* WITNESS: TOPK_rh's meter hypotheses used by the free rules (nsec_free_cf, MT_free, MT_le, MT_ok) hold at the real
   instance MT := ReplyKfMeter.MT_sec YGcfNames.nsec_cf cf_kmax, nsec_cf := YGcfNames.nsec_cf (the landed count,
   YGcfNsec.v), at CfImg_A / CfParams_reply; MT_ok is MT_sec's mo_ok by conversion. *)
Section W.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.
Goal forall p tr s, cfx_ipost (free_cf p tr s) (fun r => YGcfNames.nsec_cf (snd r) <= YGcfNames.nsec_cf s).
Proof. exact YGcfNsec.nsec_free_cf. Qed.
Goal mo_free (ReplyKfMeterB.MT_sec YGcfNames.nsec_cf cf_kmax) = 0.
Proof. reflexivity. Qed.
Goal forall s s' m, mo_le (ReplyKfMeterB.MT_sec YGcfNames.nsec_cf cf_kmax) s s' m <->
  YGcfNames.nsec_cf s' <= YGcfNames.nsec_cf s + m.
Proof. intros s s' m. reflexivity. Qed.
Goal forall s m, mo_ok (ReplyKfMeterB.MT_sec YGcfNames.nsec_cf cf_kmax) s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
Proof. intros s m. reflexivity. Qed.
End W.

(* The lane's checks: the statements with their implicit arguments, and Print Assumptions of every top
   (toolchain/allowed-axioms.txt). *)
Set Printing Implicit.
Check aj_free_null_at_x_ct_rh.
Check AFREE_x_kf_rh.
Check AFREEN_x_kf_rh.
Unset Printing Implicit.
About aj_free_null_at_x_ct_rh.
About AFREE_x_room_of_cf_rh.
About AFREEN_x_room_of_cf_rh.
About AFREE_x_kf_rh.
About AFREEN_x_kf_rh.
Print Assumptions aj_free_null_at_x_ct_rh.
Print Assumptions AFREE_x_room_of_cf_rh.
Print Assumptions AFREEN_x_room_of_cf_rh.
Print Assumptions AFREE_x_kf_rh.
Print Assumptions AFREEN_x_kf_rh.
