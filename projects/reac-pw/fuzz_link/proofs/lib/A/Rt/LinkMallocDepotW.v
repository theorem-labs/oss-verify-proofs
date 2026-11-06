(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths changed; 71 of its 180 lines of code are new or changed and 2853 lines of the source are left out. *)
(* The allocator's malloc rule with the depot step (lib/A/Rt/LinkMallocDepot.v amalloc04_rule_d) for a call whose
   trace may be WILD: its trace premise is `admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc`
   (the universe admits the trace at the call's state: it is in the carrier, inU, and fixed, already stored, or the
   depot has room for one more wild trace, YG01.v:152-155), which is what the malloc interceptor's realization asks
   (YG0d.v:265 amalloc_realizes), instead of amalloc04_rule_d's `In ... (as_universe B)` (u_fix, YG00.v:406), which
   no wild trace meets. text_of's call at 0x87fec is one: its frame record links to text_of's second argument, so the
   trace is [0x5436c; 0x87ff0] followed by a word the unwinder reads from the caller's frame (lib/A/ACejSites.v:84-88,
   text_of_c.v:132-137).
   - amalloc04_rule_dw MT: the rule;
   - amalloc04_rule_d_of_dw: it gives amalloc04_rule_d (a fixed trace is admitted, admits_fix);
   - admits_call_trace: a call whose frame record is not well formed records [pc0], a fixed row;
   - aj_malloc_at04_dw: LinkMallocDepot.v aj_malloc_at04_d with the admits premise (its proof body; the one change is
     the line that made `admits` from the fixed-row premise);
   - amalloc04_rule_dw_triv: the rule at the frame's trivial meter, from amalloc_realizes (as amalloc04_rule_d_triv).
   Generic in the frame's names; no image constant. Proves no function (kind: kit lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YI16 YC5d YCbp YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkMallocDepotPath.
Import ListNotations.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
Local Open Scope Z_scope.

(* a call whose frame record is not well formed records the one-word trace [pc0], a fixed row *)
Lemma admits_call_trace : forall U ly pc0 regs ch s, universe_ok U -> In [pc0] (u_fix U) ->
  admits U (call_trace0 pc0 regs ch) s -> admits U (call_trace ly pc0 regs ch) s.
Proof.
  intros U ly pc0 regs ch s HU H0 H. unfold call_trace. destruct (frame0_ok ly regs); [exact H|].
  exact (admits_fix U [pc0] s HU H0).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation code := (as_code B).

(* amalloc04_rule_d (LinkMallocDepot.v) with the trace premise `admits` at the call's state *)
Definition amalloc04_rule_dw : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n) /\
depot_step (call_trace lyc (pc_malloc_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).

(* a fixed trace is admitted: the wild rule gives the fixed one *)
Lemma amalloc04_rule_d_of_dw : amalloc04_rule_dw -> amalloc04_rule_d (SK := SK) segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
    HJ Ha0 Hn Hlive Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  pose proof HJ as (HAR & _).
  exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
    HJ Ha0 Hn Hlive Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch
    (admits_fix _ _ Sc (am_universe _ _ _ _ (proj1 HAR)) Htr) Hmo).
Qed.
End b.

(* LinkMallocDepot.v Section d0 (YCbq.v:813-818's hypotheses) *)
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Let UNIV0 : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B) := proj2 (proj2 errno_low).
Hypothesis ML : model_laws (as_universe B).
Local Notation code := (as_code B).
Local Notation ajournal := (ajournal segs B).
Let regime_ok_small' : forall s, st_nev s < EV_MAX -> regime_ok s := fun s H => or_introl H.
Lemma aj_malloc_at04_dw : amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
depot_step (call_trace lyc (pc_malloc_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
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
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (YG08.mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (admits_call_trace _ lyc _ regsT ch Sc (am_universe _ _ _ _ (proj1 HAR)) (proj1 UNIV0) Htr) as Htr'.
pose proof (ml_malloc_ns _ ML Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (regime_ok_small' _ Hev) Hn Hlive Htr') as HTOK.
pose proof (AMALLOC lyc Sc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
(* the depot across the call's model path: kept, or the call's trace appended once *)
pose proof (LinkMallocDepotPath.malloc_depot_path _ _ _ _ _ Hpath) as HDP.
destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
(* the depot after the call fits (Wf), so an appended trace was not stored *)
assert (HDS : depot_step (call_trace lyc (pc_malloc_ra0 code) regsT ch) (st_depot Sc) (st_depot S2))
  by exact (depot_step_of_fits _ _ _ _ (wf_depot _ _ _ _ _ HWF2) HDP).
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2).
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
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)] /\ ~ In p (map fst (blocks Sc))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl. destruct Hbl' as [Hbl Hfresh].
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl, map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
(* acall_post_journal / acall_kept_of_journal are YCbq.v Section d0 lemmas: outside it they take its hypotheses,
   closed here by `try first [...]` before the goals of the donor's proof *)
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ eapply acall_post_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2].
- intros a [_ Ha]. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. split; [exact Hr4096|]. split; [exact Eab2|].
split; [|exact HDS].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
End d0.

(* the rule at the trivial meter (YCbp.v:16 ameter_triv), as LinkMallocDepot.v amalloc04_rule_d_triv *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Theorem amalloc04_rule_dw_triv : amalloc_realizes segs B -> amalloc04_rule_dw (SK := SK) segs B ameter_triv.
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr _.
eapply SRr_mono; [exact (aj_malloc_at04_dw segs B LAWS segs_low errno_low ML AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2, res. do 8 (split; [assumption|]). split; [exact I | exact H9].
Qed.
End t.

About aj_malloc_at04_dw.
Print Assumptions aj_malloc_at04_dw.
About amalloc04_rule_dw_triv.
Print Assumptions amalloc04_rule_dw_triv.
