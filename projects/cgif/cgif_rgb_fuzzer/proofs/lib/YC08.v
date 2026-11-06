(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ02 YQ00 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YG0n YG0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YN04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC04.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Let UNIV0 : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B) := proj2 (proj2 errno_low).
Hypothesis ML : model_laws (as_universe B).
Local Notation code := (as_code B).
Local Notation ajournal := (ajournal segs B).
Local Notation acall_kept := (acall_kept segs B).
Local Notation acall_post_journal := (acall_post_journal segs B LAWS segs_low errno_low).
Local Notation acall_kept_of_journal := (acall_kept_of_journal segs B segs_low).
Lemma aj_free_null_atD : afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
vev Sc < VEV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
bud_le Sc S2 1 0 0 0 /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (proj2 (regime_big_vev _ Sc (am_wf _ _ _ _ (proj1 HAR)) HQT Hev))  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (proj1 HQT)]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF. pose proof (proj1 (regime_big_vev _ Sc HWF HQT Hev)) as HRB.
pose proof (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr) as Htr'.
pose proof (ml_free_big _ ML Sc PNull 0 (call_trace lyc (pc_free_ra0 code) regsT ch) HWF HRB (or_introl eq_refl) Htr') as HTOK.
pose proof (AFREE lyc Sc W regsT memT mdc PNull 0 ch HPRE (or_introl eq_refl) ltac:(cbn; exact Ha0) Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ & HBI2 & HFG). destruct r as [[] S2].
pose proof (jbud_free1 _ Sc _ _ ns' (tt, S2) HFG HQ) as HJB2. pose proof (bud_free _ Sc _ _ ns' (tt, S2) HFG HQ) as HBD2. unfold free_post in HQ. cbn [fst snd] in HQ, HBI2, HJB2, HBD2.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
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
{ eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | exact HJB2 | zlia | | | exact HgoneC | exact (conj HQT2 HBI2)].
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
split; [exact Hfrs2|].
split; [exact HBD2|].
rewrite Hsp' in HJ1.
eapply acall_kept_of_journal; [exact HJ1 | exact HAR | |].
- intros a (rg & [] & _).
- intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End d.
End c.
