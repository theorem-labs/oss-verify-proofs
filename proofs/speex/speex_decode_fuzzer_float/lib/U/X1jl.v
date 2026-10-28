(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qc X0qd X0qg X0qe X0qf X0qh X0qj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o1 X0o2 X0oj X0ob X0ns X0nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1m1 X1lw X1lx X1m4 X1k8 X1jk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rgmf_of_facts {RCEIL : RunCeiling} st LB sc g :
RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
first [ sf_destruct 9%nat FG as MSL AVr FRr LI FB SCr ML0 (ai & Hgh & AI & AVAI) _ | sf_fb; destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _) ].
pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
constructor.
- exact MSL.
- exact AVr.
- exact FRr.
- exact MW.
- exact SC48.
- exact GSC.
- exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
+ intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
exact (X Hmem Hgh S0).
+ intros o Ho. exact (GU b _ o Hgh Ho).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
- destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts {RCEIL : RunCeiling} st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
- intros g n GM Hn. first [ pose proof (gmf_grp _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as b gh Hmem _ | sf_fb; destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ].
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
first [ pose proof (gmf_links _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as n' p' En Ep | sf_fb; destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ].
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. first [ pose proof (gmf_grp _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as b gh Hmem _ | sf_fb; destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ].
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
first [ pose proof (gmf_links _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as n' p' En Ep | sf_fb; destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ].
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ B _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & B & _) ]. intros i. exact (B i).
Qed.

Section FPER.
Context {RCEIL : RunCeiling}.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

#[using="st m MR ER"] Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1b000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x1b000 \/ 0x3b000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x3b000 \/ 0x3d000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x3d000 \/ 0x6e000 <= r_base r).
Proof.
intros Hr. first [ pose proof (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' K' B' L' | sf_fb; destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L') ].
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
first [ pose proof (WR rid r' Hr') as sfP_; sf_destruct 5%nat sfP_ as RB0 RBAL RL0 RBC RF | sf_fb; destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as D1 D2 D3 D4 | sf_fb; destruct sfP_ as (D1 & D2 & D3 & D4) ].
pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. unfold alloc_ceiling in *. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_cases_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_image_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
0x10000 <= a < 0x6e000 -> RCTX <= a < RCTX + 928 \/ 0x4d3ac <= a < 0x4d3b0.
Proof.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- exfalso. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as D1 D2 D3 D4 | sf_fb; destruct sfP_ as (D1 & D2 & D3 & D4) ]. pose proof (lr_lo_ge r). lia.
- exfalso. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint _ _ RF) as sfP_; first [ sf_destruct 4%nat sfP_ as D1 D2 D3 D4 | sf_fb; destruct sfP_ as (D1 & D2 & D3 & D4) ]. pose proof (lr_lo_ge r). lia.
- exfalso. first [ pose proof (rst0_region (fst b) r Hr) as sfP_; sf_destruct 6%nat sfP_ as _ _ W1 W2 W3 W4 | sf_fb; destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4) ]. lia.
- exfalso. first [ pose proof (rst0_region (fst b) r Hr) as sfP_; sf_destruct 6%nat sfP_ as _ _ W1 W2 W3 W4 | sf_fb; destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4) ]. lia.
- exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

#[using="st m MR ER"] Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
first [ sf_destruct 14%nat AUX as av x3 x4 x5 x16 x6 x11 x12 x23 rnd _ _ _ HH | sf_fb; destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH) ]. unfold alloc_ceiling in *. lia.
- intros a Ha Hfp. unfold RAUXV_CELL in Ha.
destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

#[using="st m MR ER"] Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.
