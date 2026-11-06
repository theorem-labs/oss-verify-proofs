(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0ol X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ql X0q1 X0qf X0o1 X0oj X0ob X0ns.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition links_only (r r' : meta) : Prop :=
m_mem r' = m_mem r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
/\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.

Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. intros (ans & o' & H). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

Lemma leaf_of_vis_inv {R} o e (k : Z -> X1qu.M R) r :
leaf_of o (SVis e k) r ->
match e with
| EUndef _ => False
| EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
| _ => exists z, leaf_of o (k z) r
end.
Proof.
intros (ans & o' & H).
destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists ans, o'; exact H).
- rewrite mrun_peek in H. exists ans, o'. exact H.
- rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.

Lemma leaf_of_bad {R} o (bail : X1qu.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).

Lemma LO_refl st : LO st st.
Proof. intros q. repeat split; reflexivity. Qed.
Lemma LO_trans st1 st2 st3 : LO st1 st2 -> LO st2 st3 -> LO st1 st3.
Proof.
intros A B q. first [ pose proof (A q) as sfP_; sf_destruct 7%nat sfP_ as A1 A2 A3 A4 A5 A6 A7 | sf_fb; destruct (A q) as (A1 & A2 & A3 & A4 & A5 & A6 & A7) ]. first [ pose proof (B q) as sfP_; sf_destruct 7%nat sfP_ as B1 B2 B3 B4 B5 B6 B7 | sf_fb; destruct (B q) as (B1 & B2 & B3 & B4 & B5 & B6 & B7) ].
repeat split; congruence.
Qed.
Lemma LO_same st st' : (forall q, get_meta_rec st' q = get_meta_rec st q) -> LO st st'.
Proof. intros H q. rewrite H. apply LO_refl. Qed.

Lemma LO_upd_links st m f :
(forall r, links_only r (f r)) -> LO st (upd_meta m f st).
Proof.
intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
- rewrite get_meta_rec_put_same. apply Hf.
- rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.

Lemma lo_set_prev v r : links_only r (m_set_prev v r). Proof. repeat split; reflexivity. Qed.
Lemma lo_set_next v r : links_only r (m_set_next v r). Proof. repeat split; reflexivity. Qed.
Lemma lo_set_pn v w r : links_only r (m_set_prev v (m_set_next w r)). Proof. repeat split; reflexivity. Qed.

Lemma rec_set_head h v st q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.

Ltac lo_peel :=
first [ apply LO_refl
| apply LO_same; intros ?; reflexivity
| eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
| eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].

Lemma LO_dequeue h m st : LO st (dequeue h m st).
Proof.
unfold dequeue. cbv zeta.
destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.

Section AML.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.

Definition KOK (st : mstate) (k : mstate -> optr -> X1qu.M R) : Prop :=
forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : X1qu.M R) : Prop := forall r, leaf_of o bail r -> Φ r.

#[using="Type"] Lemma KOK_LO st st1 k : LO st st1 -> KOK st k -> KOK st1 k.
Proof. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.

#[using="Type"] Lemma am_take_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (am_take st k bail) r -> Φ r.
Proof.
intros K B H. unfold am_take in H.
destruct (c_avail_meta (ctx st)) as [m|].
- eapply K; [| exact H]. lo_peel.
- destruct (leaf_of_vis_inv o _ _ r H).
Qed.

#[using="Type"] Lemma am_carve_leaves st p k bail r : KOK st k -> BOK bail -> leaf_of o (am_carve st p k bail) r -> Φ r.
Proof.
intros K B H. unfold am_carve in H. cbv zeta in H.
eapply am_take_leaves; [| exact B| exact H].
eapply KOK_LO; [| exact K]. apply LO_same. intros q.
destruct (c_meta_area_tail _); reflexivity.
Qed.

#[using="Type"] Lemma am_finish_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_finish st nu k bail) r -> Φ r.
Proof.
intros K B H. unfold am_finish in H.
destruct (c_avail_meta_areas (ctx st)) as [p|]; [| destruct (leaf_of_vis_inv o _ _ r H)].
cbv zeta in H.
destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
- destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (mprotect_answer_ok z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct ((z =? 0) || (z =? TWO64 - ENOSYS)).
+ eapply am_carve_leaves; [exact K| exact B| exact Hz].
+ exact (K _ _ _ (LO_refl st) Hz).
- eapply am_carve_leaves; [exact K| exact B| exact H].
Qed.

#[using="Type"] Lemma am_after_brk_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_after_brk st nu k bail) r -> Φ r.
Proof.
intros K B H. unfold am_after_brk in H.
destruct (c_avail_meta_area_count (ctx st) =? 0).
- destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (mmap_answer_ok _ _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (is_err z); [exact (K _ _ _ (LO_refl st) Hz)|].
destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
eapply am_finish_leaves; [| exact B| exact Hz].
eapply KOK_LO; [| exact K]. apply LO_same. intros q.
replace st1 with (fst (new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st)) by (rewrite E; reflexivity). reflexivity.
- eapply am_finish_leaves; [exact K| exact B| exact H].
Qed.

#[using="Type"] Lemma alloc_meta_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (alloc_meta st k bail) r -> Φ r.
Proof.
intros K B H. unfold alloc_meta in H.
set (stI := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) in H.
assert (LI : LO st stI) by (apply LO_same; intros q; subst stI; destruct (c_init_done (ctx st) =? 0); reflexivity).
pose proof (KOK_LO st stI k LI K) as KI.
destruct (c_free_meta_head (ctx stI)) as [m|].
{ exact (KI _ _ _ (LO_dequeue LFree m stI) H). }
destruct (negb (c_avail_meta_count (ctx stI) =? 0)); [eapply am_take_leaves; [exact KI| exact B| exact H]|].
destruct ((c_avail_meta_area_count (ctx stI) =? 0) && _); [| eapply am_after_brk_leaves; [exact KI| exact B| exact H]].
destruct (c_brk (ctx stI)) as [| |rid off].
-
destruct (leaf_of_vis_inv o _ _ r H) as [cur Hc]. cbv beta in Hc.
destruct (negb (brk0_answer_ok cur)); [destruct (leaf_of_bad o _ _ Hc)|].
destruct (leaf_of_vis_inv o _ _ r Hc) as [z Hz]. cbv beta in Hz.
destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (negb (z =? _)).
+ eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
+ destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (leaf_of_vis_inv o _ _ r Hz) as [w Hw]. cbv beta in Hw.
destruct (negb (mmap_fixed_answer_ok _ w)); [destruct (leaf_of_bad o _ _ Hw)|].
destruct (new_region RKBrk _ _ stI) as [st1 rid1] eqn:E.
eapply am_after_brk_leaves; [| exact B| exact Hw]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
replace st1 with (fst (new_region RKBrk (round_up_pg cur) (2 * PGSZ) stI)) by (rewrite E; reflexivity). reflexivity.
-   eapply am_after_brk_leaves; [exact KI| exact B| exact H].
-
destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (negb (z =? _)).
+ eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
+ destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
unfold upd_region. destruct (get_region stI rid); reflexivity.
Qed.
End AML.

Lemma am_leaf_links_only : forall o st st' mo,
leaf_of o (alloc_meta st kS bS) (Some (st', mo)) ->
forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Proof.
intros o st st' mo H.
refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
- intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
- intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.

Lemma links_only_refl r : links_only r r.
Proof. repeat split; reflexivity. Qed.
Lemma links_only_trans a b c : links_only a b -> links_only b c -> links_only a c.
Proof. intros sfH_; first [ sf_destruct 7%nat sfH_ as ? ? ? ? ? ? ? | sf_fb; destruct sfH_ as (? & ? & ? & ? & ? & ? & ?) ]; intros sfH2_; first [ sf_destruct 7%nat sfH2_ as ? ? ? ? ? ? ? | sf_fb; destruct sfH2_ as (? & ? & ? & ? & ? & ? & ?) ]. repeat split; congruence. Qed.

Lemma ER_refl_tick st0 t : ENTRY_REL st0 (set_tick t st0).
Proof.
constructor; try reflexivity; try (intros; tauto).
- split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.

Lemma ER_ta st0 st sc st1 : ENTRY_REL st0 st -> ta_rel sc st st1 -> ENTRY_REL st0 st1.
Proof.
intros E T. destruct E as [ES EG EGR EM EME EGE EB EA].
constructor.
- rewrite (tr_shadow _ _ _ T). exact ES.
- intros b. rewrite <- (EG b). destruct (tr_groups _ _ _ T b) as [A B].
split; intros [x Hx]; [destruct (A (ex_intro _ x Hx)) as [y Hy]| destruct (B (ex_intro _ x Hx)) as [y Hy]]; rewrite Hy; eexists; reflexivity.
- intros rid r Hk. rewrite (tr_regions _ _ _ T). apply EGR. exact Hk.
- destruct EM as [R1 N1 S1]. split; [| rewrite (tr_next _ _ _ T); exact N1| rewrite (tr_reserved _ _ _ T); exact S1].
intros rid r Hr. rewrite (tr_regions _ _ _ T). exact (R1 rid r Hr).
- intros q. destruct (tr_geom _ _ _ T q) as (M & _). rewrite M. apply EME.
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). first [ pose proof (tr_geom _ _ _ T q) as sfP_; sf_destruct 5%nat sfP_ as M L F S P | sf_fb; destruct (tr_geom _ _ _ T q) as (M & L & F & S & P) ]. rewrite L, S. repeat split; try assumption.
unfold get_stride. rewrite L, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
- intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.

Lemma ER_am st0 st st1 m o : ENTRY_REL st0 st -> am_rel st st1 (Some m) ->
leaf_of o (alloc_meta st kS bS) (Some (st1, Some m)) -> ENTRY_REL st0 st1.
Proof.
intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
constructor.
- rewrite (amr_shadow _ _ _ A). exact ES.
- intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
- intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
+ destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
* first [ pose proof (amr_regions _ _ _ A rid r0 E0) as sfP_; sf_destruct 6%nat sfP_ as r' Hr' K' _ _ G' | sf_fb; destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G') ]. rewrite Hr in Hr'. inversion Hr'; subst r'.
rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
* exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
+ first [ pose proof (amr_regions _ _ _ A rid r Hr) as sfP_; sf_destruct 6%nat sfP_ as r' Hr' K' _ _ G' | sf_fb; destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G') ]. rewrite Hr'. f_equal. apply G'. exact Hk.
- destruct EM as [R1 N1 S1]. split.
+ intros rid r Hr. first [ pose proof (R1 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r1 H1 K1 B1 L1 | sf_fb; destruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1) ].
first [ pose proof (amr_regions _ _ _ A rid r1 H1) as sfP_; sf_destruct 6%nat sfP_ as r2 H2 K2 B2 L2 _ | sf_fb; destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _) ]. exists r2. repeat split; try congruence. lia.
+ pose proof (amr_next_rid _ _ _ A). lia.
+ rewrite (amr_reserved _ _ _ A). exact S1.
- intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). first [ pose proof (LO q) as sfP_; sf_destruct 7%nat sfP_ as M AV FR L2 F S P | sf_fb; destruct (LO q) as (M & AV & FR & L2 & F & S & P) ]. rewrite L2, S. repeat split; try assumption.
unfold get_stride. rewrite L2, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). first [ pose proof (LO q) as sfP_; sf_destruct 4%nat sfP_ as _ AV FR _ | sf_fb; destruct (LO q) as (_ & AV & FR & _) ]. rewrite <- AV, <- FR. exact Hb.
- intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

Lemma ticks_ok_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.

Lemma ALLC_tick st0 t :
(forall rid sh o v tk, (s_shadow st0) !! rid = Some sh -> (r_cells sh) !! o = Some (v, tk) -> (tk <= s_tick st0)%N) ->
(s_tick st0 < t)%N -> ALLC (set_tick t st0).
Proof. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.

Lemma ALLC_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ALLC st -> ALLC st1.
Proof. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.

Lemma ALLC_ta st sc st1 : ta_rel sc st st1 -> ALLC st -> ALLC st1.
Proof. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.

Lemma ALLC_am st st1 mo : am_rel st st1 mo -> ALLC st -> ALLC st1.
Proof. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.

Lemma gmf_of_facts {RCEIL : RunCeiling} st LB sc g :
ISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
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

Lemma taf_of_facts {RCEIL : RunCeiling} st LB sc : ISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| exact GSC]. eapply gmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
- intros g n GM Hn. first [ pose proof (gmf_grp _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as b gh Hmem _ | sf_fb; destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ].
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply gmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
first [ pose proof (gmf_links _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as n' p' En Ep | sf_fb; destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ].
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. first [ pose proof (gmf_grp _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as b gh Hmem _ | sf_fb; destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ].
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply gmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
first [ pose proof (gmf_links _ _ _ GM) as sfP_; sf_destruct 4%nat sfP_ as n' p' En Ep | sf_fb; destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ].
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ B _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & B & _) ]. intros i. exact (B i).
Qed.

Definition sc_mono_fn (a : Z) : bool := forallb (fun b => (size_class a <? size_class b)) (zseq (a + 1) (47 - a)).
Lemma sc_mono_check : forallb sc_mono_fn (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono a b : 0 <= a -> a < b < 48 -> size_class a < size_class b.
Proof.
intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.
Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof.
intros Ha Hb H. destruct (Z.lt_ge_cases a b) as [L|G]; [exact L|]. exfalso.
destruct (Z.eq_dec a b) as [->|NE]; [lia|]. pose proof (size_class_mono b a ltac:(lia) ltac:(lia)). lia.
Qed.

Definition nest_fn (q : Z) : bool := let j := stc_q q in (0 <=? j) && (j <=? 26) && (q + 1 <=? size_class j).
Lemma nest_check : forallb nest_fn (zseq 1 127) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nest_class_props q : 1 <= q <= 127 ->
0 <= stc_q q <= 26 /\ q + 1 <= size_class (stc_q q).
Proof.
intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.

Section FPER.
Context {RCEIL : RunCeiling}.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : mrep st m.
Hypothesis ER : ENTRY_REL st0 st.

#[using="st m MR ER"] Lemma st0_region rid r : (s_regions st0) !! rid = Some r ->
0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x19000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x19000 \/ 0x1b000 <= r_base r).
Proof.
intros Hr. first [ pose proof (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' K' B' L' | sf_fb; destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L') ].
pose proof (region_addr_facts st m rid r' MR Hr') as sfP_; first [ sf_destruct 5%nat sfP_ as R4 RAL RC RI1 RI2 | sf_fb; destruct sfP_ as (R4 & RAL & RC & RI1 & RI2) ].
pose proof (round_up_pg_mono _ _ L'). rewrite B' in *. lia.
Qed.

#[using="st m MR ER"] Lemma malloc_fp_cases_ER stE mE lo sp a :
mrep stE mE -> malloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold CTX in H. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. destruct (st0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (st0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="st m MR ER"] Lemma malloc_fp_image_ER stE mE lo sp a :
mrep stE mE -> malloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
0x19000 <= a < 0x1b000 -> CTX <= a < CTX + 928 \/ 0x1a57c <= a < 0x1a580.
Proof.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- exfalso. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). lia.
- exfalso. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). lia.
- exfalso. first [ pose proof (st0_region (fst b) r Hr) as sfP_; sf_destruct 4%nat sfP_ as _ _ _ RI2 | sf_fb; destruct (st0_region (fst b) r Hr) as (_ & _ & _ & RI2) ]. lia.
- exfalso. first [ pose proof (st0_region (fst b) r Hr) as sfP_; sf_destruct 4%nat sfP_ as _ _ _ RI2 | sf_fb; destruct (st0_region (fst b) r Hr) as (_ & _ & _ & RI2) ]. lia.
- exfalso. pose proof (fresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

#[using="st m MR ER"] Lemma auxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
mrep stE mE -> auxv_ok m1 B -> pres_except (malloc_fp st0 stE lo sp) m1 m' ->
alloc_ceiling <= lo -> sp <= B -> auxv_ok m' B.
Proof.
intros MRE AUX PE CLO SB. eapply auxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha Hfp. destruct (malloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
first [ sf_destruct 13%nat AUX as av x3 x4 x5 x6 x11 x12 x23 rnd _ _ _ HH | sf_fb; destruct AUX as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH) ]. unfold alloc_ceiling in *. lia.
- intros a Ha Hfp. unfold AUXV_CELL, LIBC in Ha.
destruct (malloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold CTX in X; lia.
Qed.

#[using="st m MR ER"] Lemma frame_keep_ER stE mE lo sp m1 m' A cs :
mrep stE mE -> pres_except (malloc_fp st0 stE lo sp) m1 m' -> rw_cells asegs m1 A cs ->
sp <= A -> alloc_ceiling <= A -> rw_cells asegs m' A cs.
Proof.
intros MRE PE H HA HC. eapply pres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (malloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.

#[using="st m MR ER"] Lemma medtab_keep_ER stE mE lo sp m1 m' :
mrep stE mE -> pres_except (malloc_fp st0 stE lo sp) m1 m' -> alloc_ceiling <= lo ->
rw_cells asegs m1 MEDTAB medtab_cells -> rw_cells asegs m' MEDTAB medtab_cells.
Proof.
intros MRE PE CLO H. eapply pres_except_rw_cells; [exact PE| exact H|].
unfold MEDTAB. cbn. intros a Ha Hfp. destruct (malloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold CTX in X; lia.
Qed.
End FPER.

Lemma unk_agree_xfer o stA mA stB mB :
unk_agree stA o mA ->
s_shadow stB = s_shadow stA ->
(forall rid r, r_kind r = RKGroup -> (s_regions stB) !! rid = Some r -> (s_regions stA) !! rid = Some r) ->
(forall b, is_Some ((s_groups stB) !! b) <-> is_Some ((s_groups stA) !! b)) ->
(forall rid r off h, (s_regions stA) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow stA rid) off = Unknown h -> ~ grp_hdr_cov stA rid off -> mB (wa (r_base r + off)) = mA (wa (r_base r + off))) ->
unk_agree stB o mB.
Proof.
intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov stA rid off).
{ intros sfH_; first [ sf_destruct 5%nat sfH_ as bq gh Hbq Hf Hoff | sf_fb; destruct sfH_ as (bq & gh & Hbq & Hf & Hoff) ]. apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

Lemma fm_proj st g :
let st' := as_fm_st st g in
s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
/\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
/\ (forall c, active st' c = active st c) /\ (forall i, usage st' i = usage st i)
/\ c_brk (ctx st') = c_brk (ctx st) /\ c_mmap_counter (ctx st') = c_mmap_counter (ctx st)
/\ (forall i, bounces st' i = bounces st i) /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ c_seq (ctx st') = c_seq (ctx st).
Proof.
unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
- cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; repeat split; reflexivity.
- repeat split; reflexivity.
Qed.
