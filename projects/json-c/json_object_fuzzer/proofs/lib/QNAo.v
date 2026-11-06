(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y QDUx Q4J3 QytA Qnxq QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QWTl QPjm QkQT QlkP QyjG QTyG QM7w Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5 QDUx.Mq1 QPjm.Mq4.
Import Qy5Y.Mq7 QkQT QDUx.Mqb QlkP QyjG QTyG.Mq0 QM7w.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition links_only (r r' : meta) : Prop :=
m_mem r' = m_mem r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
/\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.

#[using="Type"] Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. intros (ans & o' & H). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

#[using="Type"] Lemma leaf_of_vis_inv {R} o e (k : Z -> QUZl.M R) r :
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

#[using="Type"] Lemma leaf_of_bad {R} o (bail : QUZl.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).

#[using="Type"] Lemma LO_refl st : LO st st.
Proof. intros q. repeat split; reflexivity. Qed.
#[using="Type"] Lemma LO_trans st1 st2 st3 : LO st1 st2 -> LO st2 st3 -> LO st1 st3.
Proof.
intros A B q. destruct (A q) as (A1&A2&A3&A4&A5&A6&A7). destruct (B q) as (B1&B2&B3&B4&B5&B6&B7).
repeat split; congruence.
Qed.
#[using="Type"] Lemma LO_same st st' : (forall q, get_meta_rec st' q = get_meta_rec st q) -> LO st st'.
Proof. intros H q. rewrite H. apply LO_refl. Qed.

#[using="Type"] Lemma LO_upd_links st m f :
(forall r, links_only r (f r)) -> LO st (upd_meta m f st).
Proof.
intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
- rewrite get_meta_rec_put_same. apply Hf.
- rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.

#[using="Type"] Lemma lo_set_prev v r : links_only r (m_set_prev v r). Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma lo_set_next v r : links_only r (m_set_next v r). Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma lo_set_pn v w r : links_only r (m_set_prev v (m_set_next w r)). Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma rec_set_head h v st q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.
End RC__1.

Ltac lo_peel :=
first [ apply LO_refl
| apply LO_same; intros ?; reflexivity
| eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
| eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma LO_dequeue h m st : LO st (dequeue h m st).
Proof.
unfold dequeue. cbv zeta.
destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.

Section AML.
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.

Definition KOK (st : mstate) (k : mstate -> optr -> QUZl.M R) : Prop :=
forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : QUZl.M R) : Prop := forall r, leaf_of o bail r -> Φ r.

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
destruct (negb (mmap_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
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
-  eapply am_after_brk_leaves; [exact KI| exact B| exact H].
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

#[using="Type"] Lemma am_leaf_links_only : forall o st st' mo,
leaf_of o (alloc_meta st kS bS) (Some (st', mo)) ->
forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Proof.
intros o st st' mo H.
refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
- intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
- intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.

#[using="Type"] Lemma links_only_refl r : links_only r r.
Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma links_only_trans a b c : links_only a b -> links_only b c -> links_only a c.
Proof. intros (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.

#[using="Type"] Lemma ER_refl_tick st0 t : ENTRY_REL st0 (set_tick t st0).
Proof.
constructor; try reflexivity; try (intros; tauto).
- split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.

#[using="Type"] Lemma ER_ta st0 st sc st1 : ENTRY_REL st0 st -> ta_rel sc st st1 -> ENTRY_REL st0 st1.
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
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (tr_geom _ _ _ T q) as (M & L & F & S & P). rewrite L, S. repeat split; try assumption.
unfold get_stride. rewrite L, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
- intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.

#[using="Type"] Lemma ER_am st0 st st1 m o : ENTRY_REL st0 st -> am_rel st st1 (Some m) ->
leaf_of o (alloc_meta st kS bS) (Some (st1, Some m)) -> ENTRY_REL st0 st1.
Proof.
intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
constructor.
- rewrite (amr_shadow _ _ _ A). exact ES.
- intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
- intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
+ destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
* destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr in Hr'. inversion Hr'; subst r'.
rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
* exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
+ destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr'. f_equal. apply G'. exact Hk.
- destruct EM as [R1 N1 S1]. split.
+ intros rid r Hr. destruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1).
destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. repeat split; try congruence. lia.
+ pose proof (amr_next_rid _ _ _ A). lia.
+ rewrite (amr_reserved _ _ _ A). exact S1.
- intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (LO q) as (M & AV & FR & L2 & F & S & P). rewrite L2, S. repeat split; try assumption.
unfold get_stride. rewrite L2, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). destruct (LO q) as (_ & AV & FR & _). rewrite <- AV, <- FR. exact Hb.
- intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

#[using="Type"] Lemma ticks_ok_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.

#[using="Type"] Lemma ALLC_tick st0 t :
(forall rid sh o v tk, (s_shadow st0) !! rid = Some sh -> (r_cells sh) !! o = Some (v, tk) -> (tk <= s_tick st0)%N) ->
(s_tick st0 < t)%N -> ALLC (set_tick t st0).
Proof. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.

#[using="Type"] Lemma ALLC_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ALLC st -> ALLC st1.
Proof. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.

#[using="Type"] Lemma ALLC_ta st sc st1 : ta_rel sc st st1 -> ALLC st -> ALLC st1.
Proof. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.

#[using="Type"] Lemma ALLC_am st st1 mo : am_rel st st1 mo -> ALLC st -> ALLC st1.
Proof. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.

#[using="Type"] Lemma gmf_of_facts st LB sc g :
ISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
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

#[using="Type"] Lemma taf_of_facts st LB sc : ISTF st LB -> 0 <= sc < 48 -> taf st sc.
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
- intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply gmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply gmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Definition sc_mono_fn (a : Z) : bool := forallb (fun b => (size_class a <? size_class b)) (zseq (a + 1) (47 - a)).
#[using="Type"] Lemma sc_mono_check : forallb sc_mono_fn (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma size_class_mono a b : 0 <= a -> a < b < 48 -> size_class a < size_class b.
Proof.
intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.
#[using="Type"] Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof.
intros Ha Hb H. destruct (Z.lt_ge_cases a b) as [L|G]; [exact L|]. exfalso.
destruct (Z.eq_dec a b) as [->|NE]; [lia|]. pose proof (size_class_mono b a ltac:(lia) ltac:(lia)). lia.
Qed.

Definition nest_fn (q : Z) : bool := let j := stc_q q in (0 <=? j) && (j <=? 26) && (q + 1 <=? size_class j).
#[using="Type"] Lemma nest_check : forallb nest_fn (zseq 1 127) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma nest_class_props q : 1 <= q <= 127 ->
0 <= stc_q q <= 26 /\ q + 1 <= size_class (stc_q q).
Proof.
intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).

Hypothesis ER : ENTRY_REL st0 st.

End FPER.

#[using="Type"] Lemma unk_agree_xfer o stA mA stB mB :
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
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

#[using="Type"] Lemma fm_proj st g :
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

End RC__2.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay QXxF Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 QDUx.Mq1 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9 Q6y7.Mq2.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma follow_steq {R} (t1 t2 : QUZl.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma follow_sbind {R S} (t : QUZl.M R) (f : R -> QUZl.M S) :
forall ans x y, follow t ans = Some x ->
(forall ans', follow (f x) ans' = Some y) ->
follow (sbind t f) ans = Some y.
Proof.
induction t as [r | e k IH]; intros ans x y H Hf.
- cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
- rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

#[using="Type"] Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 -> forall ans r1 r2, follow t1 ans = Some r1 -> follow t2 ans = Some r2 -> RR r1 r2.
Proof.
induction 1 as [a b Hab | e k1 k2 Hk IH]; intros ans r1 r2 F1 F2.
- cbn in F1, F2. inversion F1; inversion F2; subst. exact Hab.
- cbn in F1, F2. destruct e; try discriminate; destruct ans as [|z ans]; try discriminate; eapply IH; eauto.
Qed.

#[using="Type"] Lemma mrun_enframe_full o st g b idx n ctr :
m_mem (get_meta_rec st g) = Some b ->
let stride := get_stride (get_meta_rec st g) in
let off := fold_off (if rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) =? 0 then Z.land ctr 255
else Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2)
+ 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
((stride - IB - n) / UNIT) in
mrun o (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p)))
= SRet (o, (havoc (snd (enframe_at st g idx n off)) n (fst (enframe_at st g idx n off)), Some (snd (enframe_at st g idx n off)))).
Proof.
intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
{ unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
rewrite (rd8_oracle pans_mem pans_mem_range).
assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
{ intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
((stride - IB - n) / UNIT) = off).
{ intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
clearbody off.
destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
- rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
- rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

#[using="Type"] Lemma strip_eq_proj a b : strip a = strip b ->
s_ctx a = s_ctx b /\ s_regions a = s_regions b /\ s_next_rid a = s_next_rid b /\ s_metas a = s_metas b
/\ s_areas a = s_areas b /\ s_groups a = s_groups b /\ s_slots a = s_slots b /\ s_reserved a = s_reserved b.
Proof.
intros E.
pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

#[using="Type"] Lemma mrun_fst {R} (t : QUZl.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
- cbn in H. inversion H. reflexivity.
- cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
+ unfold pupd_mem in H. eapply IH. exact H.
+ cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

#[using="Type"] Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
(B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
intros HB HS HT HK.
destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).

Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.

End TOPLEVEL.

End RC__1.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya QPiB Qatc QSfG QdBa QpFQ QaiD QYTG QLaA QQg5 QoCS QQCz QhnL Q4en QBv7 QlQE Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QdBa.Mq2 QaiD QYTG.Mq1 QLaA QLaA.Mq0 QQg5.Mq2 QoCS.Mq0 QQCz QhnL Q4en QBv7.
Import QnDM_c1.Mq0 QytA Qy5Y.Mq4 QlQE Q3o5.Mq1 QTyG.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section CF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="Type"] Lemma hostsB b g : QlQE.hosts st b g <-> hosts st b g.
Proof. reflexivity. Qed.
#[using="Type"] Lemma is_gmB g : is_gm st g <-> live_group st g.
Proof. reflexivity. Qed.

#[using="RC__ X L BL INV IA"] Lemma listed_meta_slot m h : In m (LS h) -> meta_slot st m.
Proof.
intros H. pose proof (listed_present _ _ _ _ _ INV m h H) as P. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). exists a, ar, k. auto.
Qed.

#[using="RC__ X L BL INV IL"] Lemma in_list_of_next m : m_next (MR st m) <> None -> exists h, In m (LS h).
Proof. intros H. exact (proj2 (proj1 (il_link _ _ IL m)) H). Qed.

#[using="RC__ X L BL LS INV IM IG IS"] Lemma sep_ghdr' m bm i m2 b2 : hosts st bm m -> 0 <= i <= m_last_idx (MR st m) ->
s_groups st !! (fst bm, sstart (MR st m) i) = None ->
hosts st b2 m2 -> fst b2 = fst bm ->
snd b2 + 16 <= sstart (MR st m) i \/ sstart (MR st m) (i + 1) <= snd b2.
Proof.
intros Hm Hi NH H2 Hf. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sst_lt _ _ _ IG _ _ i (i + 1) Hm ltac:(lia)) as L1. unfold UNIT in S0.
destruct (aptr_eq_dec m2 m) as [->|NEm].
- left. pose proof (hosts_inj _ _ _ IM _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
- pose proof (sstart0 _ _ _ IM _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ _ IM IG _ _ H2) as G2.
destruct (dichotomy _ _ _ _ IM IG IS _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
+ destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ _ _ IM IG IS _ _ _ Hm NH _ _ Ha)|].
destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
destruct (Z.lt_ge_cases j i).
* left. pose proof (sstart_mono _ _ _ IG _ _ (j + 1) i Hm ltac:(lia)). lia.
* right. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) j Hm ltac:(lia)). lia.
+ left. destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'.
destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
pose proof (sstart_mono _ _ _ IG _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
+ destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'.
destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hp'); subst bp'.
destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite (gend_eq st) in A2.
pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)).
destruct (Z.lt_ge_cases j1 j2).
* right. pose proof (sstart_mono _ _ _ IG _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
* left. pose proof (sstart_mono _ _ _ IG _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
Qed.

#[using="RC__ X L BL LS INV IA IL"] Lemma c_links : ci_links_t st.
Proof.
pose proof (old_lists _ _ _ _ _ INV) as LO.
constructor.
- intros m nx Hn. fold (MR st m) in Hn. fold (MR st nx). destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
destruct (lists_next_in st LS LO h m Hh) as (y & Hy & Ey & Py). rewrite Hn in Ey. inversion Ey; subst y.
split; [exact Py| exact (listed_meta_slot _ _ Hy)].
- intros m pv Hp. fold (MR st m) in Hp. fold (MR st pv).
destruct (m_next (MR st m)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL m) Ex) as P; rewrite Hp in P; discriminate].
destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
destruct (lists_prev_in st LS LO h m Hh) as (y & Hy & Ey & Ny). rewrite Hp in Ey. inversion Ey; subst y.
split; [exact Ny| exact (listed_meta_slot _ _ Hy)].
- intros m. fold (MR st m). split; [exact (proj2 (il_link _ _ IL m))|]. intros Hp.
destruct (m_next (MR st m)) as [x|] eqn:Ex; [| reflexivity]. exfalso.
destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
destruct (lists_prev_in st LS LO h m Hh) as (y & _ & Ey & _). rewrite Hp in Ey. discriminate.
- intros m Hn. fold (MR st m) in Hn. destruct (in_list_of_next m Hn) as [h Hh]. exact (listed_meta_slot _ _ Hh).
Qed.

#[using="RC__ X L BL LS INV IL"] Lemma c_heads : ci_heads_t st.
Proof.
constructor.
- intros h Hh. fold (MR st h). pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|]. pose proof (il_free _ _ IL h Hin) as E. rewrite E. reflexivity.
- intros sc a Ha. fold (MR st a). pose proof (head_listed _ _ _ _ _ INV (LActive sc) a Ha) as Hin.
destruct (il_active _ _ IL sc a Hin) as (Hsc & Hl & Esc). split; [exact Hsc|]. split; [exact (listed_next _ _ _ _ _ INV a _ Hin)|]. split; [exact Hl| exact Esc].
Qed.

#[using="RC__ X L BL LS INV IL"] Lemma c_homog : ci_homog st.
Proof.
intros m nx Hn. fold (MR st m) in Hn. fold (MR st m) (MR st nx).
destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
pose proof (next_listed _ _ _ _ _ INV h m nx Hh Hn) as Hnx.
destruct h as [sc|].
- destruct (il_active _ _ IL sc m Hh) as (_ & Lm & Em). destruct (il_active _ _ IL sc nx Hnx) as (_ & Ln & En).
split; [split; auto|]. intros _. rewrite Em, En. reflexivity.
- pose proof (free_not_live _ _ _ _ _ INV m Hh) as Nm. pose proof (free_not_live _ _ _ _ _ INV nx Hnx) as Nn.
split; [split; intros H'; exfalso; [exact (Nm H')| exact (Nn H')]|]. intros H'. exfalso. exact (Nm H').
Qed.

#[using="Type"] Lemma q_div b0 stride i off : stride mod 16 = 0 -> (b0 + 16 + stride * i + 16 * off - b0 - 16) / 16 * 16 = stride * i + 16 * off.
Proof.
intros Hs. pose proof (Z.div_mod stride 16 ltac:(lia)) as E. rewrite Hs, Z.add_0_r in E.
set (k := stride / 16) in *. clearbody k. subst stride.
replace (b0 + 16 + 16 * k * i + 16 * off - b0 - 16) with ((k * i + off) * 16) by lia.
rewrite Z.div_mul by lia. lia.
Qed.

#[using="Type"] Lemma mod16_addr a b st_ i off : a mod 4096 = 0 -> b mod 16 = 0 -> st_ mod 16 = 0 -> (a + (b + 16 + st_ * i) + 16 * off) mod 16 = 0.
Proof.
intros Ha Hb Hs.
pose proof (Z.div_mod a 4096 ltac:(lia)) as Ea. rewrite Ha, Z.add_0_r in Ea. set (a' := a / 4096) in *. clearbody a'.
pose proof (Z.div_mod b 16 ltac:(lia)) as Eb. rewrite Hb, Z.add_0_r in Eb. set (b' := b / 16) in *. clearbody b'.
pose proof (Z.div_mod st_ 16 ltac:(lia)) as Es. rewrite Hs, Z.add_0_r in Es. set (s' := st_ / 16) in *. clearbody s'.
subst a b st_. replace (4096 * a' + (16 * b' + 16 + 16 * s' * i) + 16 * off) with ((256 * a' + b' + 1 + s' * i + off) * 16) by lia.
apply Z_mod_mult.
Qed.

#[using="RC__ X L BL LS INV IR IA IM IG IS ISH"] Lemma c_gmeta : ci_gmeta st.
Proof.
intros b g Hm. destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI. pose proof (g_li _ _ _ _ _ _ GO) as LI.
pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r & Hr & Kr & A0 & GE).
pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
constructor; try (fold (MR st g)).
- pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. auto.
- split; [exact M1|]. apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia.
- split; [exact M2|]. apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia.
- exact LI.
- exact (g_freeable _ _ _ _ _ _ GO).
- destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia].
- split; [exact ML|]. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). unfold alloc_ceiling in CEIL.
destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. lia.
- intros i Hi. split; intros Ht; [pose proof (M3 i Hi Ht); lia| exact (M4 i Hi Ht)].
- exact (hosts_mem _ _ _ IM _ _ Hm).
- exists r. pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|].
split; [unfold QlQE.sstart_of; change (sstart (MR st g) (m_last_idx (MR st g) + 1) <= round_up_pg (r_len r)); rewrite <- (gend_eq st); exact GE|].
intros NZ. destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. auto.
- split; [exact SG| exact SM].
- intros MZ. destruct (g_nest _ _ _ _ _ _ GO MZ) as (p & i & Hsl & Hfst & Hend & Hsc & Hstr).
destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([bp Hp] & Hi & Es).
exists p, i, bp. split; [exact Hsl|]. split; [exact Hp|].
rewrite (hosts_gbase _ _ _ IM _ _ Hp) in Hfst. split; [exact Hfst|]. split; [exact Es|]. split; [exact Hi|].
pose proof Hp as [aip Hp']. pose proof (is_part _ _ _ IS bp p aip i Hp' Hi) as P. rewrite <- Es in P.
unfold one5, tbit in P. destruct P as (_ & _ & _ & nAD & _ & _ & nBD & _).
assert (D : s_groups st !! b <> None) by (rewrite Hb; discriminate).
split. { intros [F|A]; [apply nBD| apply nAD]; split; auto. }
fold (MR st p). split; [lia|].
destruct (ish_nest _ _ ISH b g p i Hm MZ Hsl) as ((v3 & K3 & L3 & R3) & K2 & K1 & Q). rewrite (hosts_gbase _ _ _ IM _ _ Hp) in K2, K1, Q.
exists v3, (byte_of ((snd b - snd bp - UNIT) / UNIT) 0), (byte_of ((snd b - snd bp - UNIT) / UNIT) 1).
split; [exact K3|]. split; [exact L3|]. split; [exact K2|]. split; [exact K1|].
rewrite u16_bytes by exact Q. rewrite (slot_start'_eq _ _ _ IM _ _ i Hp) in Es. rewrite Es. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hp).
pose proof (stride_ge _ _ _ IG _ _ Hp) as [_ SMp]. unfold UNIT in *. pose proof (q_div (snd bp) (get_stride (MR st p)) i 0 SMp). lia.
Qed.

#[using="RC__ X L BL LS INV IM"] Lemma c_groups : ci_groups st.
Proof. intros b gh Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _ & AI). exists m. auto. Qed.

#[using="RC__ X L BL LS INV IM"] Lemma c_group_inj : ci_group_inj st.
Proof. intros b1 b2 g H1 H2. exact (hosts_inj _ _ _ IM _ _ _ H1 H2). Qed.

#[using="RC__ X L BL LS INV IS"] Lemma c_slots : ci_slots st.
Proof. intros s g i Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (A & B & C). split; [exact A|]. split; [exact C| exact B]. Qed.

#[using="RC__ X L BL LS INV IS"] Lemma c_slots_total : ci_slots_total st.
Proof. intros b g i Hb Hi. exact (is_total _ _ _ IS _ _ _ Hb Hi). Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma c_ghdr_unk : ci_ghdr_unk st.
Proof. intros b gh o Hb Ho. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hb) as [m Hm]. exact (ish_ghdr _ _ ISH b m o Hm Ho). Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma c_hdr0 : ci_hdr0 st.
Proof. intros g b i Hm Hi. fold (MR st g) in *. exact (ish_hdr0 _ _ ISH b g i Hm ltac:(unfold cnt_of; lia)). Qed.

#[using="RC__ X L BL LS INV ZB IA"] Lemma c_ctx : ci_ctx st.
Proof.
pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
split; [exact C2|]. split.
{ intros i. unfold bounces, ctx. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)). }
split. { intros i. unfold unmap_seq, ctx. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)). }
split. { intros sc. pose proof (f_usage _ _ _ _ _ INV ZB sc) as U. rewrite usage_strip in U. lia. }
unfold ctx. destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia.
Qed.

#[using="RC__ X L BL LS INV IR"] Lemma c_brk : ci_brk st.
Proof.
intros rid off Hb. pose proof (ir_brk _ _ _ IR) as BR. unfold ctx in Hb. rewrite Hb in BR. destruct BR as (_ & r & Hr & Kr & _). exists r. auto.
Qed.

#[using="RC__ X L BL LS INV ZB"] Lemma c_mem_hosts : ci_mem_hosts st.
Proof. intros q b H. exact (mem_hosts _ _ _ _ _ INV ZB _ _ H). Qed.

#[using="Type"] Lemma metakind_ng r : is_metakind r -> r_kind r <> RKGroup.
Proof. intros [K|K]; rewrite K; discriminate. Qed.

#[using="RC__ X L BL LS INV IA"] Lemma area_ng a : s_areas st !! a <> None -> ng_ptr st (Some a).
Proof.
intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [| congruence].
destruct (ia_areas _ IA _ _ E) as ((r & Hr & MK & _) & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)].
Qed.

#[using="RC__ X L BL LS INV IR IA"] Lemma c_mptrs : ci_mptrs st.
Proof.
unfold ci_mptrs, ctx.
split. { destruct (c_avail_meta (s_ctx st)) as [q|] eqn:E; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & MK). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
split. { destruct (c_meta_area_head (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_head _ IA q E)). }
split. { destruct (c_meta_area_tail (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_tail _ IA q E)). }
split. { destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:E; [| exact I].
destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & MK & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
intros a ar Ha. destruct (a_next ar) as [a'|] eqn:E; [| exact I]. destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_ng _ (NXT a' E)).
Qed.

Variable LB : list block.
Hypothesis CR : CORR st LB BL.

#[using="RC__ X L BL LS INV IM IG IS ISH CR"] Lemma LB_blk_ok : Forall (blk_ok st) LB.
Proof.
apply List.Forall_forall. intros blk Hblk.
destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
destruct (is_blocks _ _ _ IS _ Hk) as (m' & i' & Hs & Hoff & _). cbn [bslot boff fst snd] in Hs, Hoff.
pose proof (is_total _ _ _ IS _ _ _ Hm Hi) as Hs'. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec, Hs in Hs'. inversion Hs'; subst m' i'.
constructor.
- exists m, i, bm. rewrite C1. split; [exact Hs|]. split; [exact Hm|]. split; [rewrite Ec; reflexivity|]. split; [exact Hi|]. fold (MR st m).
pose proof Hm as [ai Hb]. pose proof (is_part _ _ _ IS bm m ai i Hb Hi) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec in P.
unfold one5, tbit in P. destruct P as (_ & _ & nAC & _ & _ & nBC & _).
assert (C : In c (map bslot BL)) by (apply (in_map bslot _ _ Hk)).
split. { intros [F|A]; [apply nBC| apply nAC]; split; auto. }
exists off. split; [exact Ho|]. split; [rewrite Ea, Ec; unfold conc, get_region; cbn [fst snd]; rewrite Hr; lia|]. split; [rewrite C2; exact Fit|].
pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (K4 & K3 & K2 & K1 & Q & _). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, Q.
unfold known, SHd in K4, K3, K2, K1. rewrite (hosts_gbase _ _ _ IM _ _ Hm) in K2, K1, Q.
split; [unfold IB; replace (snd c + UNIT * off - 4) with (snd c + UNIT * off - 4) by lia; exact K4|].
eexists _, _, _. unfold aadd; cbn [fst snd]. split; [exact K3|].
split; [apply land31_idx; [destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai' & _ & GO'); pose proof (g_li _ _ _ _ _ _ GO'); lia| lia]|].
split; [exact K2|]. split; [exact K1|].
rewrite u16_bytes by exact Q. rewrite Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm).
pose proof (stride_ge _ _ _ IG _ _ Hm) as [_ SMm]. unfold UNIT in *. pose proof (q_div (snd bm) (get_stride (MR st m)) i off SMm). lia.
- rewrite C1. exact NH.
- rewrite C2. exact Hn.
Qed.

#[using="RC__ X L BL LS INV IR IM IG IS CR"] Lemma LB_blk_clear : Forall (blk_clear st LB) LB.
Proof.
apply List.Forall_forall. intros blk Hblk.
destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
pose proof (sstart_succ st m i) as SS. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)) as SM0.
pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SMm].
destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r' & Hr' & _ & A0 & GE). rewrite Hr in Hr'. inversion Hr'; subst r'.
pose proof (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16].
constructor.
- exists r. rewrite C1, Ec. cbn [fst]. split; [exact Hr|]. split; [exact Kr|].
split; [unfold UNIT in *; lia|].
split. { rewrite C2. rewrite (gend_eq st) in GE. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)). unfold UNIT, IB in *. lia. }
split. { rewrite Ea. destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & PG & _). unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm). unfold UNIT, PGSZ in *.
exact (mod16_addr _ _ _ _ _ PG A16 SMm). }
intros a Ha. pose proof (f_blk_unknown _ _ _ _ _ INV _ CR blk r Hblk ltac:(rewrite C1, Ec; exact Hr) a Ha) as U. rewrite C1, Ec in U. exact U.
- intros b gh Hgh Hf. rewrite C1, Ec in Hf. cbn [fst] in Hf. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hgh) as [m2 Hm2].
unfold conc, get_region. rewrite Hf, Hr. rewrite Ea, C2.
destruct (sep_ghdr' m bm i m2 b Hm Hi ltac:(rewrite Ec in NH; exact NH) Hm2 Hf) as [A|A]; unfold UNIT, IB in *; lia.
- intros blk' Hblk' NE Hf.
destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk') as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & D1 & D2 & Hm2 & Hi2 & Ec2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
rewrite C1, D1, Ec, Ec2 in Hf. cbn [fst] in Hf. rewrite Hf, Hr in R2. inversion R2; subst r2.
rewrite A2, Ea, D2, C2. pose proof (sstart_succ st m2 i2).
assert (NE' : m2 <> m \/ i2 <> i). { destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, D1, Ec, Ec2, Hf. reflexivity. }
rewrite Ec in NH. rewrite Ec2 in N2.
destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 bm2 i2 Hm2 Hf Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
End CF.
End RC__1.

Local Ltac inst f INV CR :=
first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
| exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Theorem areach_cinv_proof : forall {resv sec} st LB, AREACH_from resv sec st LB -> CINV st LB.
Proof.
intros resv sec st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
constructor.
- inst c_links INV CR.
- inst c_heads INV CR.
- inst c_homog INV CR.
- inst c_gmeta INV CR.
- inst c_groups INV CR.
- inst c_group_inj INV CR.
- inst c_slots INV CR.
- inst c_slots_total INV CR.
- inst c_ghdr_unk INV CR.
- inst c_hdr0 INV CR.
- inst LB_blk_ok INV CR.
- inst LB_nodup INV CR.
- inst c_ctx INV CR.
- inst c_brk INV CR.
- inst f_ticks INV CR.
- inst c_mem_hosts INV CR.
- inst c_mptrs INV CR.
- inst LB_blk_clear INV CR.
Qed.

End RC__2.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
0 < stride ->
let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
fst (Pos.iter F (0, tb) n) = Z.pos n
/\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
/\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
- cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
- rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
split; [lia|]. split.
+ rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
+ intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
* right. exists (Z.pos n). split; [lia| reflexivity].
* rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

#[using="Type"] Lemma add_slots_first' m p stride c st : 1 <= c -> 0 < stride ->
(s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
/\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
destruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

#[using="Type"] Lemma mask_upto_range' k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
change (2^32) with (2 * 2^31). lia.
Qed.

#[using="Type"] Lemma put_meta_wr8_comm mt r q v st : put_meta mt r (wr8 q v st) = wr8 q v (put_meta mt r st).
Proof. destruct st; reflexivity. Qed.
#[using="Type"] Lemma put_meta_zero_hdrs_comm mt r p size : forall k i st,
put_meta mt r (zero_hdrs p size i k st) = zero_hdrs p size i k (put_meta mt r st).
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
#[using="Type"] Lemma rec_zero_hdrs p size q : forall k i st, get_meta_rec (zero_hdrs p size i k st) q = get_meta_rec st q.
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.

Section SMG.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.

Definition sm_rec : meta :=
mkMeta (Some mt) (Some mt) (Some p) (mask_upto ai - 1) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.

#[using="Type"] Lemma smg_proj :
s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
/\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
/\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
/\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
/\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. repeat split; reflexivity. Qed.

#[using="SC CNT REC P0"] Lemma smg_rec_mt : get_meta_rec stF mt = sm_rec.
Proof.
unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.

#[using="ml SC CNT REC P0"] Lemma smg_rec_other q : q <> mt -> get_meta_rec stF q = get_meta_rec stT q.
Proof.
intros NE. unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
unfold stFin, stE, stD, stC, stB, stA. rewrite rec_set_active, get_meta_rec_put_other, rec_put_group, get_meta_rec_put_other, rec_set_usage, rec_hdr_havoc by exact NE.
reflexivity.
Qed.

#[using="Type"] Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
rewrite !active_upd_meta. reflexivity.
Qed.

#[using="Type"] Lemma smg_ctx :
ctx stF = set_active_map (<[sc := mt]> (c_active (ctx stT))) (set_usage_map (<[sc := usage stT sc + cnt]> (c_usage (ctx stT))) (ctx stT)).
Proof. reflexivity. Qed.

#[using="Type"] Lemma smg_usage i : usage stF i = if i =? sc then usage stT sc + cnt else usage stT i.
Proof.
unfold usage. rewrite smg_ctx. cbn [c_usage set_active_map set_usage_map].
destruct (Z.eqb_spec i sc) as [E|NE]; [rewrite E, lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

#[using="SC CNT"] Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
unfold UNIT. reflexivity.
Qed.

#[using="SC CNT REC"] Lemma smg_slot0 : 0 < get_stride sm_rec -> (s_slots stF) !! (fst p, snd p + 16) = Some (mt, 0).
Proof.
intros HS. unfold stF, st_model. cbv zeta.
match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
replace s with (get_stride sm_rec) end.
2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
reflexivity. }
change (fst p, snd p + 16) with (aadd p UNIT).
apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.

#[using="Type"] Lemma smg_shadow_other q : q <> fst p -> get_shadow stF q = get_shadow stT q.
Proof.
intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma smg_shadow_p :
get_shadow stF (fst p) = mkShadow (r_cells (get_shadow stT (fst p)))
(<[snd p / 16 := hav_add 12 (s_tick stT) (default [] ((r_hav (get_shadow stT (fst p))) !! (snd p / 16)))]> (r_hav (get_shadow stT (fst p))))
(r_havp (get_shadow stT (fst p))).
Proof.
unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. reflexivity.
Qed.

#[using="Type"] Lemma smg_group_p : (s_groups stF) !! p = Some (mkGhdr (Some mt) (Z.land ai 31)).
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.

#[using="Type"] Lemma smg_groups_inv b' gh : (s_groups stF) !! b' = Some gh -> (b' = p /\ gh = mkGhdr (Some mt) (Z.land ai 31)) \/ (b' <> p /\ (s_groups stT) !! b' = Some gh).
Proof.
rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
- left. rewrite lookup_insert_eq in H. inversion H. auto.
- right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.

#[using="P0"] Lemma smg_groups_old b' gh : (s_groups stT) !! p = None -> (s_groups stT) !! b' = Some gh -> (s_groups stF) !! b' = Some gh.
Proof.
intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.

#[using="SC"] Lemma smg_grp_hdr_cov off : snd p <= off < snd p + 12 -> grp_hdr_cov stF (fst p) off.
Proof. intros Ho. exists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.

#[using="P0"] Lemma smg_grp_hdr_cov_old q off : (s_groups stT) !! p = None -> grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros GN (b' & gh & Hb & Hf & Ho). exists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.

#[using="Type"] Lemma smg_conc q : conc stF q = conc stT q.
Proof. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.

#[using="Type"] Lemma smg_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.

#[using="SC CNT REC P0"] Lemma smg_ret_span rid' S len :
(exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
/\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
rid' = fst p /\ S = snd p + 16 /\ len = get_stride sm_rec - 4.
Proof.
intros (g & b & HA & HM & -> & -> & ->). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.

#[using="Type"] Lemma Zle_1_nonneg' x : 1 <= x < 2^28 -> 0 <= x /\ True.
Proof. intros H. split; [lia| exact I]. Qed.

Section SM.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.

Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).

#[using="Type"] Lemma sm_proj :
s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
/\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
/\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
/\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
/\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.

#[using="SC CNT REC P0"] Lemma sm_rec_mt : get_meta_rec stF mt = sm_rec sc cnt ai ml mt p.
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.

#[using="Type"] Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.

#[using="sc SC ML"] Lemma sm_ml_nz : (ml =? 0) = false.
Proof. apply Z.eqb_neq. lia. Qed.

#[using="SC CNT ML"] Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.

#[using="SC CNT REC"] Lemma sm_slot0 : 0 < get_stride (sm_rec sc cnt ai ml mt p) -> (s_slots stF) !! (rid, 16) = Some (mt, 0).
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.

#[using="SHT"] Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
apply cell_read_hh0; [exact SHT| exact Ho].
Qed.

#[using="SHT"] Lemma sm_cells_none off : (r_cells (get_shadow stF rid)) !! off = None.
Proof.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="SHT"] Lemma sm_hav_none off : 16 <= off -> (r_hav (get_shadow stF rid)) !! (off / 16) = None.
Proof.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="SHT"] Lemma sm_havp_none k : (r_havp (get_shadow stF rid)) !! k = None.
Proof.
clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="Type"] Lemma sm_shadow_other q : q <> rid -> get_shadow stF q = get_shadow stT q.
Proof. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.

#[using="GNT"] Lemma sm_groups_rid off gh : (s_groups stF) !! (rid, off) = Some gh -> off = 0 /\ gh = mkGhdr (Some mt) (Z.land ai 31).
Proof.
intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
- unfold p in E. inversion E. auto.
- rewrite GNT in H'. discriminate.
Qed.

#[using="SC"] Lemma sm_grp_hdr_cov off : 0 <= off < 12 -> grp_hdr_cov stF rid off.
Proof. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.

#[using="GNT P0"] Lemma sm_grp_hdr_cov_old q off : grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.

#[using="Type"] Lemma sm_conc q : conc stF q = conc stT q.
Proof. exact (smg_conc stT sc cnt ai mt p q). Qed.

#[using="Type"] Lemma sm_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.

#[using="SHT"] Lemma sm_rdv o : rdv pans_mem o stF (rid, 13) = 0.
Proof. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.

#[using="ml SC CNT ML REC P0"] Lemma sm_stride_mod16 : get_stride (get_meta_rec stF mt) mod 16 = 0.
Proof.
rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
- replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
- rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

#[using="SC CNT AI ML REC HrT Hk0 SHT GNT P0"] Lemma sm_slot_ok (req nd : Z) :
0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
(cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
meta_slot stT mt ->
slot_ok stF mt p r0 0 req
/\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
/\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
intros RQ FIT LEN EML NDR SZ NDC MS.
pose proof (size_class_range sc SC) as SZR.
assert (RU : round_up_pg nd = nd).
{ rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
{ rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
/\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
/\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
{ rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
- rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
- destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
destruct S20 as (G20 & GSP & GFIT & G31 & G18).
pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
split; [| split; [exact STR| split; [exact G20| nia]]].
constructor.
- rewrite sm_rec_mt. reflexivity.
- rewrite (proj1 sm_proj). exact HrT.
- exact Hk0.
- unfold p. cbn [snd]. lia.
- reflexivity.
- rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
- replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
- exact G20.
- apply sm_stride_mod16.
- exact G31.
- lia.
- exact GFIT.
- intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
- unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
- intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
- unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
- apply (proj1 (sm_meta_slot mt)). exact MS.
- rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
- rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

#[using="ml SC CNT REC P0"] Lemma sm_ret_span rid' S len :
(exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
/\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
rid' = rid /\ S = 16.
Proof.
intros H. destruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _). unfold p. cbn. split; reflexivity.
Qed.
End SM.

End RC__1.
