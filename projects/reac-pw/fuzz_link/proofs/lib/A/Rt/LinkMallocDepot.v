(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbq.v, with its module paths changed; 235 of its 473 lines of code are new or changed and 2730 lines of the source are left out. *)
(* The allocator's depot across one malloc call: the frame's malloc rule (lib/Reusable/YC5d.v amalloc04_rule, cgif's)
   with one more post clause, the depot step of the call's trace (lib/Reusable/YGwildCount.v depot_step: the depot is
   unchanged, or the trace was not stored and is appended once). The model's `malloc n trace` (lib/Reusable/YG00.v:417)
   puts its trace with one `depot_put` (:427) on its success path and touches the depot nowhere else; neither
   amalloc04_rule's post nor model_laws' malloc_post (YG01.v:543) says so, so a caller could not carry a bound on the
   depot's wild part (YG01.v wild_part) across a malloc. Generic in the frame's names (any segs, asyms and meter, as
   amalloc04_rule is stated); no image constant.
   - amalloc04_rule_d MT: the rule with the clause;
   - amalloc04_rule_of_d: it gives amalloc04_rule;
   - depot_step_fixed_wild / depot_step_wild_le: the clause bounds the wild part (no growth for a fixed trace, at most
     one for any trace);
   - aj_malloc_at04_d: lib/Reusable/YCbq.v aj_malloc_at04 (the released cgif lemma, :1549) with the clause, its proof
     body reused (a call of the lemma loses the model path): the clause is malloc_depot_path
     (lib/A/Rt/LinkMallocDepotPath.v) on the path of the call, made a depot_step by depot_step_of_fits
     (YGwildCount.v) with the depot invariant (YG01.v wf_depot) of malloc_post's Wf of the state after the call;
   - amalloc04_rule_d_triv: the rule at the frame's trivial meter, from the malloc interceptor's realization
     (YG0d.v amalloc_realizes), as YCbp.v amalloc04_rule_triv proves amalloc04_rule.
   The same for free (YG00.v:546 free puts its trace with one depot_put, :558): afree04_rule_d / afree_null04_rule_d
   are YC5d.v:75 afree04_rule / :97 afree_null04_rule with two more post clauses, `same_io mdc md2` (YG0d.v:37, the io
   part of the model kept, which the realization gives: YCbq.v aj_free_at_io) and then the depot step of the call's
   trace; afree04_rule_of_d / afree_null04_rule_of_d give the frame rules; aj_free_at_d / aj_free_null_at_d are
   YCbq.v aj_free_at_io (:1087) / aj_free_null_at_io (:1267) with the depot step (free_depot_path of
   LinkMallocDepotPath.v), and afree04_rule_d_triv / afree_null04_rule_d_triv the rules at the trivial meter, as YCbp.v
   afree04_rule_triv (:38) / afree_null04_rule_triv (:47).
   rule 24: proves no function (kind: kit lemma, the allocator model's depot across one malloc or free). The free
   pieces are ported per the rule-24 check: the model path from fuzz_preset lib/Reusable/YGcfDepotStep.v
   (LinkMallocDepotPath.v), the rule half from YCbq.v aj_free_at_io / aj_free_null_at_io. *)
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
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation code := (as_code B).

(* amalloc04_rule (YC5d.v:56), premises and post unchanged, and the depot step of the trace the call records
   (YG0d.v call_trace: call_trace0 when the frame record is well formed, else the one-word trace [pc0]) *)
Definition amalloc04_rule_d : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
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

Lemma amalloc04_rule_of_d : amalloc04_rule_d -> amalloc04_rule segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
    HJ Ha0 Hn Hlive Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  eapply SRr_mono; [exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
    HJ Ha0 Hn Hlive Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
  exists ly2, S2, regs2, mem2, md2, res. repeat (split; [assumption|]). exact H9.
Qed.

End b.

(* the depot step bounds the wild part *)
Lemma depot_step_wild_le : forall U tr d d', depot_step tr d d' ->
  (length (wild_part U d') <= length (wild_part U d) + 1)%nat.
Proof. intros U tr d d' H. pose proof (wild_part_step U tr d d' H). pose proof (wild_cost_le U tr d). lia. Qed.

Lemma depot_step_fixed_wild : forall U tr d d', depot_step tr d d' -> In tr (u_fix U) ->
  (length (wild_part U d') <= length (wild_part U d))%nat.
Proof.
  intros U tr d d' H Hf. pose proof (wild_part_step U tr d d' H) as W.
  unfold wild_cost in W. apply mem_trace_In in Hf. rewrite Hf in W. cbn [orb] in W. lia.
Qed.

(* the free rules with the io clause and the depot step of the call's trace, last (YC5d.v:75 afree04_rule, :97
   afree_null04_rule: premises unchanged) *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation code := (as_code B).
Definition afree04_rule_d : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT) /\
same_io mdc md2 /\
depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).

Definition afree_null04_rule_d : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
mo_le MT Sc S2 (mo_free MT) /\
same_io mdc md2 /\
depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).

Lemma afree04_rule_of_d : afree04_rule_d -> afree04_rule segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
    HJ Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP Hmo.
  eapply SRr_mono; [exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
    HJ Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP Hmo)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact H7.
Qed.

Lemma afree_null04_rule_of_d : afree_null04_rule_d -> afree_null04_rule segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
    HJ Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  eapply SRr_mono; [exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
    HJ Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact H7.
Qed.
End f.

(* YCbq.v aj_malloc_at04 (:1549-1631) with the depot step of the call's trace; Section d0's hypotheses (YCbq.v:813-818) *)
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
Lemma aj_malloc_at04_d : amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
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
pose proof (admits_fix _ _ Sc (am_universe _ _ _ _ (proj1 HAR)) (call_trace_in lyc _ regsT ch _ (proj1 UNIV0) Htr)) as Htr'.
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

(* YCbq.v aj_free_at_io (:1087-1183) with the depot step of the call's trace *)
Lemma aj_free_at_d : afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
same_io mdc md2 /\
depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n) Hin) as (q & Hq & Hqin).
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc pa n HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; zlia).
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
pose proof (admits_fix _ _ Sc (am_universe _ _ _ _ (proj1 HAR)) (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr)) as Htr'.
pose proof (ml_free _ ML Sc q n (call_trace lyc (pc_free_ra0 code) regsT ch) HWF Hev (or_intror Hqin) Htr') as HTOK.
pose proof (AFREE lyc Sc W regsT memT mdc q n ch HPRE (or_intror Hqin) ltac:(rewrite Hq; exact Ha0) Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
(* the depot across the call's model path: kept, or the call's trace appended once *)
pose proof (LinkMallocDepotPath.free_depot_path _ _ _ _ _ Hpath) as HDP.
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [[] S2]. unfold free_post in HQ. cbn [fst snd] in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
(* the depot after the call fits (Wf), so an appended trace was not stored *)
assert (HDS : depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2))
  by (cbn [fst snd] in HDP; exact (depot_step_of_fits _ _ _ _ (wf_depot _ _ _ _ _ HWF2) HDP)).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2). rewrite Hbl2, map_app.
f_equal; apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (q, n)) with (pa, n) by (subst fc; cbn [fst snd]; rewrite Hq; reflexivity). reflexivity. }
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as <- <-. apply HnE. zlia.
- apply in_or_app. right. exact Hb. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [(pa, pa + req_size n)] (p + i)).
{ intros p m i Hp Hnp Hi. exists (pa, pa + req_size n). split; [left; reflexivity|]. cbn [fst snd].
destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia|].
destruct (Z_lt_le_dec (p + i) (pa + req_size n)) as [H2|H2]; [zlia|]. exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ eapply acall_post_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2].
- exact (secs_ext_length _ _ Hsecs2).
- intros a [_ Ha]. rewrite Hq in Ha. exists pa, n. split; [left; exact Hin|]. split; [exact Ha|]. left.
exists (pa, pa + req_size n). split; [left; reflexivity | cbn; zlia]. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S)) as [H0|H0].
- left. split; [| exists pa, n; split; [exact Hin | zlia]].
replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right. exists pa, n. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|]. split; [| split; [exact Hio2 | exact HDS]].
rewrite Hsp' in HJ1. replace (sp0 + o - ASTACK) with (sp0 + o - ASTACK) by zlia.
eapply acall_kept_of_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HJ1 | exact HAR | | exact Hlive | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha.
Qed.

(* YCbq.v aj_free_null_at_io (:1267-1349) with the depot step of the call's trace *)
Lemma aj_free_null_at_d : afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
same_io mdc md2 /\
depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
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
pose proof (admits_fix _ _ Sc (am_universe _ _ _ _ (proj1 HAR)) (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr)) as Htr'.
pose proof (ml_free _ ML Sc PNull 0 (call_trace lyc (pc_free_ra0 code) regsT ch) HWF Hev (or_introl eq_refl) Htr') as HTOK.
pose proof (AFREE lyc Sc W regsT memT mdc PNull 0 ch HPRE (or_introl eq_refl) ltac:(cbn; exact Ha0) Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
(* the depot across the call's model path: kept, or the call's trace appended once *)
pose proof (LinkMallocDepotPath.free_depot_path _ _ _ _ _ Hpath) as HDP.
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [[] S2]. unfold free_post in HQ. cbn [fst snd] in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
(* the depot after the call fits (Wf), so an appended trace was not stored *)
assert (HDS : depot_step (call_trace lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2))
  by (cbn [fst snd] in HDP; exact (depot_step_of_fits _ _ _ _ (wf_depot _ _ _ _ _ HWF2) HDP)).
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (Hperm : Permutation (blocks S2) (blocks Sc) \/ (exists l1' l2', blocks Sc = l1' ++ (PNull, 0) :: l2' /\ blocks S2 = l1' ++ l2')).
{ destruct Hsplit as [[_ E12] | E12]; [left; rewrite Hbl2, E12; apply Permutation_refl | right; exists l1, l2; auto]. }
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (HnoNull : forall l1' l2', blocks Sc = l1' ++ (PNull, 0) :: l2' -> False).
{ intros l1' l2' E1.
assert (Hin : In (0, 0) (ablocks B lyc Sc)).
{ unfold ablocks. change (In (0, 0) (map fc (blocks Sc))). rewrite E1, map_app. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc 0 0 HAR Hin) as (_ & H4096 & _). zlia. }
assert (Ebl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ E12] | E12]; [rewrite Hbl2, E12; reflexivity | exfalso; exact (HnoNull l1 l2 E12)]. }
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Ebl. apply map_ext_in. exact Efc. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [] (p + i)).
{ intros p m i Hp Hnp Hi. exfalso. apply Hnp. rewrite Eab2. exact Hp. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ eapply acall_post_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2].
- exact (secs_ext_length _ _ Hsecs2).
- intros a [Hnn _]. exfalso. exact (Hnn eq_refl). }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia |].
intros a (rg & [] & _). }
split; [exact HP|].
split; [rewrite Eab2; apply Permutation_refl|].
split; [exact Hfrs2|]. split; [| split; [exact Hio2 | exact HDS]].
rewrite Hsp' in HJ1.
eapply acall_kept_of_journal; try first [exact LAWS | exact segs_low | exact errno_low | exact ML];
[exact HJ1 | exact HAR | | | exact sink_closed_nil].
- intros a (rg & [] & _).
- intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End d0.

(* the rule at the trivial meter (YCbp.v:16 ameter_triv), as YCbp.v:29 amalloc04_rule_triv; YCbp.v's hypotheses *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Theorem amalloc04_rule_d_triv : amalloc_realizes segs B -> amalloc04_rule_d (SK := SK) segs B ameter_triv.
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr _.
eapply SRr_mono; [exact (aj_malloc_at04_d segs B LAWS segs_low errno_low ML AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2, res. do 8 (split; [assumption|]). split; [exact I | exact H9].
Qed.

(* the free rules at the trivial meter, as YCbp.v:38 afree04_rule_triv / :47 afree_null04_rule_triv *)
Theorem afree04_rule_d_triv : afree_realizes segs B -> afree04_rule_d (SK := SK) segs B ameter_triv.
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP _.
eapply SRr_mono; [exact (aj_free_at_d segs B LAWS segs_low errno_low ML AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
exists ly2, S2, regs2, mem2, md2. do 6 (split; [assumption|]). split; [exact I|]. split; [exact H7 | exact H8].
Qed.

Theorem afree_null04_rule_d_triv : afree_realizes segs B -> afree_null04_rule_d (SK := SK) segs B ameter_triv.
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr _.
eapply SRr_mono; [exact (aj_free_null_at_d segs B LAWS segs_low errno_low ML AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
exists ly2, S2, regs2, mem2, md2. do 6 (split; [assumption|]). split; [exact I|]. split; [exact H7 | exact H8].
Qed.
End t.

About aj_malloc_at04_d.
Print Assumptions aj_malloc_at04_d.
About amalloc04_rule_d_triv.
Print Assumptions amalloc04_rule_d_triv.
About aj_free_at_d.
Print Assumptions aj_free_at_d.
About aj_free_null_at_d.
Print Assumptions aj_free_null_at_d.
About afree04_rule_d_triv.
Print Assumptions afree04_rule_d_triv.
About afree_null04_rule_d_triv.
Print Assumptions afree_null04_rule_d_triv.
