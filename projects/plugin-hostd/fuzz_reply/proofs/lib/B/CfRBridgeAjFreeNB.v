(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the free(NULL) CALL-SITE RULE over the cf allocator contract (a Theorem Labs lane R, new file).
   IMAGE B TWIN (row G-BCF): lib/A/CfRBridgeAjFreeN.v at c6394a5bd7e, under lib/B so the B tree is self-contained
   (as lib/B/CfParamsReplyB.v). One change, the P'' carry of record (Reusable YGcallx.v (sha256 1dd2a7cdc3ee; internal record), YG0dcf.v): the
   model law amx_free and afree_realizes_cf take `admits (as_universe B) tr S`; the rule keeps its `In` premise and
   converts it by YG01.admits_fix from HU, as YGcallx.v's own rules do (its header, line 6). The A file's text follows.
   Rule 24: no function proved. This is journal plumbing over afree_realizes_cf (YG0dcf.v) at the cf relation; the
   only facts read from the model are the model laws (YGcallcf.v alloc_model_laws_x_cf).

   aj_free_null_at_x_ct is the free(NULL) twin of lib/Reusable/YGcallx.v aj_free_at_x_ct (:507-613), and its proof
   follows that proof step by step. It is stated in Section n at the shared shape of YGcallcf.v:
     ARx := ARxs (YGcallcf.v:241, ARcf /\ xs_placed_cf), QM := QM_cf (:51), ft := free_cf, WFx := Wf_cf (as_universe B),
   with the Section r laws of YGcallx.v taken from YGcallcf.v: LAWS := AR_laws_x_xs L (:246), OWNLOW :=
   ARx_owned_low_law_xs L (:249), WFL := ARx_wf_law_xs (:252), the model laws := alloc_model_laws_x_cf HU (:179), and the
   contract at ARxs := afree_realizes_x_xs (:357). XSL (ARx_xs_law_xs, :258) is not used: a free writes no extent.

   The differences from aj_free_at_x_ct, each forced by p = PNull:
   (a) the block premises `In (pa, n) (ablocks B lyc Sc)`, `~ In pa Hpc` and the footprint premise on (pa, n) are
       dropped, and `getr regsT 10 = w64 pa` is `getr regsT 10 = w64 0` (sptr_addr B lyc PNull is 0 by its definition,
       YG0f.v:118-120, :257, so this is afree_realizes_x's register premise at p := PNull);
   (b) afree_realizes_x's premise `~ In (sptr_addr B lyc PNull) Hpc`, i.e. `~ In 0 Hpc`, is DERIVED, not assumed: every
       entry of Hpc is the base of a live block (ARmcf's amc_hp_live, YG0ncf.v:236) and every live block's base is at
       least 4096 (AR_laws_x's blocks law, YCbqG.v:48);
   (c) the request size given to the contract, the model law and the leaf is n := 0. Any n is allowed at p = PNull
       (afree_realizes_x's `p = PNull \/ In (p, n) (blocks S)`); the leaf reads n only under `p <> PNull`;
   (d) the model's free_post_x (YGcallx.v:296) at p = PNull keeps the blocks: its block-split arm would put
       (PNull, 0) in blocks Sc, so (0, 0) would be a live block of address 0 < 4096. So the post has
       `Permutation (ablocks B ly2 S2) (ablocks B lyc Sc)` (here an equality), the call journal has the empty footprint
       and the kept clause exempts nothing (fun _ => False), as aj_malloc_at_x_ct's NULL arm (YGcallx.v:988-1016);
   (e) the post also carries the call's pre (acall_pre_x) and the GRANTED model path with its leaf at (tt, S2), as
       aj_free_at_x_ct (YGcallx.v:721-725) does, without the trace conjunct (it is a premise here).
   The journal's count grows by the call's own tick count, as in YGcallx.v (exception 3, the tick update).
   SK (YI16.sink_head) is a Context parameter, as in YGcallx.v. No address, no ledger, no image numeral: 0 is the
   NULL pointer and the request size, 10 / 1 / 3 / 4 are RISC-V register numbers, 16 / 4096 / 16384 are cgif's
   LENGTH constants (YGcallx.v:95-97). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcallcf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).
(* YGcallcf.v:241's relation, verbatim *)
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

(* YGcallx.v:694 aj_free_at_x_ct at p = PNull (differences (a)-(e) in the header). *)
Lemma aj_free_null_at_x_ct : afree_realizes_cf segs B ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists trc, apath (free_cf PNull (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x segs B ARxs lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros AFCF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
(* the Section r laws of YGcallx.v at ARxs (YGcallcf.v) *)
pose proof L as LAWS. apply AR_laws_x_xs in LAWS.
pose proof L as OWNLOW. apply ARx_owned_low_law_xs in OWNLOW.
pose proof (ARx_wf_law_xs segs B) as WFL.
pose proof HU as AMX. apply alloc_model_laws_x_cf in AMX.
pose proof AFCF as AFREE. apply afree_realizes_x_xs in AFREE.
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
(* (b): 0 is in no ghost list: each entry is a live block's base (amc_hp_live), at least 4096 (the blocks law) *)
assert (Hnhp : ~ In (sptr_addr B lyc PNull) Hpc).
{ rewrite E0. intros Hin0.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ (proj1 (proj1 HAR))) 0 Hin0) as (kc & Hkc & Hst & Eq & _).
assert (Hb : In (0, ck_req kc) (ablocks B lyc Sc)).
{ apply (proj2 (In_ablocks B lyc Sc 0 (ck_req kc))). exists kc.
split; [exact Hkc|]. split; [exact Hst|]. split; [symmetry; exact Eq | reflexivity]. }
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memT mdc 0 (ck_req kc) HAR Hb) as (_ & H4096 & _). lia. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (admits_fix _ _ Sc HU Htr) as Htr'.
destruct AMX as [_ AMF].
pose proof (AMF Sc PNull 0 (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) HWF (QMQ_cf segs B Sc memT HQM)
  (or_introl eq_refl) Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc PNull 0 ch HPRE (or_introl eq_refl) ltac:(rewrite E0; exact Ha0)
Hnhp Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
(* (d): the model keeps the blocks; its split arm would make (0, 0) a live block *)
assert (Hbl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ Hs] | Hsplit]; [rewrite Hbl2; exact Hs|].
exfalso.
assert (Hb : In (0, 0) (ablocks B lyc Sc)).
{ unfold ablocks. apply in_map_iff. exists (PNull, 0). split; [reflexivity|].
rewrite Hsplit. apply in_or_app. right. left. reflexivity. }
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memT mdc 0 0 HAR Hb) as (_ & H4096 & _). lia. }
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (alx_layout _ _ _ LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ rewrite <- Eab. unfold ablocks. rewrite Hbl. reflexivity. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_x segs B ARxs LAWS segs_low errno_low OWNLOW);
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | exact HQT2].
- intros a [Hc _]. exfalso. exact (Hc eq_refl).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | eapply ajournal_x_nil_pst; exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|].
split; [rewrite Eab2; apply Permutation_refl|].
split; [exact Hfrs2|].
split; [exact HPRE|].
split; [exists tr; split; [exact Hpath|]; split; [exact Hgf | exact Hleaf0]|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_x segs B ARxs segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

End n.

Print Assumptions aj_free_null_at_x_ct.
