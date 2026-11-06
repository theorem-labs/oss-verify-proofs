(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0qn X0px X0qc X0q2 X0q3 X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qi X0q4 X0pk X0p3 X0oz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
lb_remove p LB = lbrm LB (p, A, n).
Proof.
intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
- pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
- tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

Lemma auxv_ok_pres_B {RCEIL : RunCeiling} : forall C m m' B,
auxv_ok m B -> pres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, AUXV_CELL <= a < AUXV_CELL + 8 -> ~ C a) ->
auxv_ok m' B.
Proof.
intros C m m' B sfH_; first [ sf_destruct 13%nat sfH_ as av x3 x4 x5 x6 x11 x12 x23 rnd C1 A1 A2 H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) ]; intros HP HB HC.
first [ unshelve sf_eexists 9%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x6, x11, x12, x23, rnd ]. split; [|split; [|split; [|exact H]]].
- eapply pres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply pres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
- eapply pres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

Section FP.
Context {RCEIL : RunCeiling}.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.

#[using="RCEIL m MR LO LS"] Lemma fp_not_high a : sp <= a -> ~ FPT a.
Proof.
intros Ha. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- pose proof (free_fp_lt st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
- first [ sf_destruct 6%nat DR as rid r Hr _ _ Hin | sf_fb; destruct DR as (rid & r & Hr & _ & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- lia.
Qed.

#[using="RCEIL m MR LO"] Lemma fp_not_img a : 0x19000 <= a < 0x1b000 -> ~ (CTX <= a < CTX + 928) -> ~ (107900 <= a < 107904) -> ~ FPT a.
Proof.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ first [ sf_destruct 5%nat X as rid r Hr _ Hin | sf_fb; destruct X as (rid & r & Hr & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). pose proof (lr_lo_ge r). lia.
+ first [ sf_destruct 4%nat X as b gh Hb Hin | sf_fb; destruct X as (b & gh & Hb & Hin) ]. first [ pose proof (group_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb _ Sb0 Sb1 _ | sf_fb; destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). lia.
+ first [ sf_destruct 7%nat X as rid r v Hr _ Hin _ | sf_fb; destruct X as (rid & r & v & Hr & _ & Hin & _) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). lia.
- first [ sf_destruct 6%nat DR as rid r Hr _ _ Hin | sf_fb; destruct DR as (rid & r & Hr & _ & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). lia.
- exact (N2 ER).
Qed.

#[using="RCEIL m MR LO"] Lemma fp_not_image a : 0x19000 <= a < 0x1b000 -> ~ alloc_static a -> ~ FPT a.
Proof.
intros Ha NS. apply fp_not_img; [exact Ha| |]; intros X; apply NS; unfold alloc_static, LIBC, CTX, ERRNO, ATP in *; lia.
Qed.

#[using="RCEIL m C MR LO BLKR SHR"] Lemma fp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
first [ pose proof (WR _ _ Hrg) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RGC RGF | sf_fb; destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF) ]. destruct (reserved_disjoint _ _ RGF). unfold alloc_ceiling in RGC.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold CTX in X. lia.
+ first [ sf_destruct 5%nat X as rid r Hr NK Hin | sf_fb; destruct X as (rid & r & Hr & NK & Hin) ].
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ first [ sf_destruct 4%nat X as b gh Hb Hin | sf_fb; destruct X as (b & gh & Hb & Hin) ]. destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* first [ pose proof (group_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 _ | sf_fb; destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _) ].
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ first [ sf_destruct 7%nat X as rid r v Hr Kr Hin HC | sf_fb; destruct X as (rid & r & v & Hr & Kr & Hin & HC) ]. destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- first [ sf_destruct 6%nat DR as rid r Hr Hr' Kr Hin | sf_fb; destruct DR as (rid & r & Hr & Hr' & Kr & Hin) ].
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.

#[using="RCEIL st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma heap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> heap_pres LB' sp m m'.
Proof.
intros HLB a Ha CA. apply PE; [exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply fp_not_high. exact CA.
- apply fp_not_image; assumption.
- apply (fp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma auxv_ok_free B : auxv_ok m B -> sp <= B -> auxv_ok m' B.
Proof.
intros AV HB. eapply auxv_ok_pres_B; [exact AV | exact PE | |].
- intros a Ha. apply fp_not_high. lia.
- intros a Ha. apply fp_not_img; unfold AUXV_CELL, LIBC, CTX in *; lia.
Qed.

#[using="RCEIL st st' lo sp MR LO PE FPT"] Lemma medtab_free : rw_cells asegs m MEDTAB medtab_cells -> rw_cells asegs m' MEDTAB medtab_cells.
Proof.
intros H. eapply pres_except_rw_cells; [exact PE | exact H |]. cbn. intros a Ha.
apply fp_not_img; unfold MEDTAB, CTX in *; lia.
Qed.
End FP.

