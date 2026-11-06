(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from lib/Reusable/YCbq.v:1551-1633 aj_malloc_at04 (copied from
   proofs/cgif/cgif_file_fuzzer/lib/YCbq.v) and lib/Reusable/YCbp.v:28-35 amalloc04_rule_triv (copied from
   proofs/cgif/cgif_file_fuzzer/lib/YCbp.v), at the calloc contract of lib/Reusable/YGCalloc.v. *)
(* The calloc call rule at the trivial meter, the calloc twin of YCbp.v amalloc04_rule_triv (rule 24: no function
   proved; this file is kit-level link lemmas).

   [aj_calloc_at04] is YCbq.v:1551-1633 aj_malloc_at04, line for line, with three changes:
   - it consumes the calloc contract YGCalloc.v:335-337 acalloc_realizes_cgif (the realizes form :213-222
     acalloc_realizesP at this unit's malloc tree, call precondition, amreal and malloc_leaf) in place of
     YG0d.v:254 amalloc_realizes, so the request is n = nm * sz with nm in a0 and sz in a1, and the call-depth
     premise [ly_bot lyc + cdepth < spZ regsT] and the size bound [nm * sz <= cmax] are passed on to it;
   - the post adds the zero conjunct of YGCalloc.v:205-208 calloc_leaf_with (:198-201 calloc_zeroed), read at the
     returned block (its a0 is the block address, below 2 ^ 64 by the AR block law);
   - the trace premise is YGCalloc.v:241-242 ctrace0 (the text of YCbq.v:317 call_trace0), and the one-element
     trace [pc0] is a premise ([UNIVC]): YCbq.v:808-811 api_env carries it for malloc's and free's pc0 only.
   [acalloc04_rule_triv] is YCbp.v:28-35 amalloc04_rule_triv at YGCalloc.v:255-276 acalloc04_rule. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG08 YCbq YI16 YC5d YGCalloc YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Local Notation ajournal := (ajournal segs B).
Lemma aj_calloc_at04 : forall pc pc0 cmax cdepth,
In [pc0] (as_universe B) ->
acalloc_realizes_cgif segs B pc pc0 cmax cdepth ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
ly_bot lyc + cdepth < spZ regsT ->
getr regsT 10 = w64 nm -> getr regsT 11 = w64 sz ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes Sc + nm * sz <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (ctrace0 pc0 regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nm * sz)] /\
(forall i, 0 <= i < nm * sz -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size (nm * sz))).
Proof.
intros pc pc0 cmax cdepth UNIVC ACALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz o raw ch
HJ Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
pose proof (Z.mul_nonneg_nonneg nm sz Hnm Hsz) as Hn0.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
change (In (call_trace0 pc0 regsT ch) (as_universe B)) in Htr.
pose proof (call_trace_in lyc _ regsT ch _ UNIVC Htr) as Htr'.
pose proof (ml_malloc_ns _ ML Sc (nm * sz) (call_trace lyc pc0 regsT ch) HWF (aregime_ok _ (aregime_small _ Hev))
(conj Hn0 Hn) Hlive (admits_fix _ _ Sc (am_universe _ _ _ _ (proj1 HAR)) Htr')) as HTOK.
pose proof (ACALLOC lyc Sc W regsT memT mdc nm sz ch HPRE Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive Htr') as HREAL.
cbv beta in HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
unfold calloc_leaf_with in Hleaf. destruct Hleaf as [Hleaf Hzero].
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2).
cbn [fst snd] in HPOST, Hres, HQT2.
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
-
exfalso. discriminate (HNS eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, nm * sz)] /\ ~ In p (map fst (blocks Sc))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl. destruct Hbl' as [Hbl Hfresh].
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nm * sz)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, nm * sz)]). rewrite Hbl, map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, nm * sz) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (nm * sz) HAR2 Hnew) as (_ & Hr4096 & Hrtop & _).
assert (Hrq : 0 <= req_size (nm * sz)) by (unfold req_size; destruct (nm * sz =? 0); lia).
assert (Hres64 : bv_unsigned (w64 res) = res).
{ unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size (nm * sz))).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, nm * sz) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ eapply (acall_post_journal segs B LAWS segs_low errno_low); [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2].
- intros a [_ Ha]. exists res, (nm * sz). split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res (nm * sz) a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. split; [exact Hr4096|]. split; [exact Eab2|].
split.
{ intros i Hi. pose proof (Hzero i Hi) as Hz. unfold cfg_at in Hz. cbn [cfg_ms ms_regs ms_mem mkst] in Hz.
rewrite Hres, Hres64 in Hz. apply Hz. lia. }
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
Theorem acalloc04_rule_triv : forall pc pc0 cmax cdepth,
In [pc0] (as_universe B) ->
acalloc_realizes_cgif segs B pc pc0 cmax cdepth ->
acalloc04_rule segs B (as_universe B) ajournal (acall_kept segs B)
(mo_ok ameter_triv) (mo_le ameter_triv) (mo_malloc ameter_triv) pc pc0 cmax cdepth.
Proof.
intros pc pc0 cmax cdepth UNIVC ACALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz o raw ch
HJ Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr _.
eapply SRr_mono; [exact (aj_calloc_at04 pc pc0 cmax cdepth UNIVC ACALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz o raw ch
HJ Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2, res. repeat (split; [assumption|]). exact I.
Qed.
End b.
