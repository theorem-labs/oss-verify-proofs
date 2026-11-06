(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QlEo_c1 QnDM_c1 Q2qa QytA Qy5Y Q4J3 QlQE QPjm QZAi QUZl Q7S0 Ql2m QGeV QFkE Q6y7 QJE4 Q3o5 QNAo Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 QFkE Q6y7 QJE4.Mq2 Q3o5.Mq0.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
lb_remove p LB = lbrm LB (p, A, n).
Proof.
intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
- pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
- tauto.
Qed.

#[using="Type"] Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

#[using="Type"] Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

#[using="Type"] Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.

End FP.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya QPiB Qatc QSfG QdBa QpFQ QaiD QYTG QjcB QLaA QQg5 Q1am QoCS QPWv QQCz QcV4 Q7RC QhnL Q4en QBv7 Qnxq Q8P7 QkQT QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QdBa.Mq2 QaiD QYTG.Mq1 QjcB QLaA QLaA.Mq0 QQg5.Mq2 Q1am.Mq0 QoCS QQg5 QSfG QPWv Q1am.Mq1 QoCS.Mq0 QQCz QcV4 Q7RC QhnL Q4en QBv7 QSfG.Mq1.
Import QnDM_c1.Mq0 QytA Qy5Y.Mq4 Qnxq QlQE Q8P7 Qy5Y.Mq7 QkQT Q3o5.Mq1 QTyG.Mq2 QNAo.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section GF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="RC__ X L BL INV IM"] Lemma lmem_listed m h : In m (LS h) -> live_group st m -> lmem (strip st) m.
Proof.
intros Hin [b Hb]. unfold lmem. rewrite !get_meta_rec_strip. fold (MR st m).
split; [rewrite (hosts_mem _ _ _ IM _ _ Hb); discriminate|].
split; [exact (listed_next _ _ _ _ _ INV m h Hin)|].
destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) h m Hin) as (y & _ & E & _). rewrite E. discriminate.
Qed.

#[using="RC__ X L BL LS INV ZB"] Lemma mem_live g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. exact (mem_hosts X st L BL LS INV ZB g b H). Qed.

#[using="RC__ X L BL INV ZB IL"] Lemma linked_group_listed g b : m_mem (MR st g) = Some b -> m_next (MR st g) <> None ->
In g (LS (LActive (m_sizeclass (MR st g)))).
Proof.
intros Hb Hn. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
destruct h as [sc|].
- destruct (il_active _ _ IL sc g Hh) as (_ & _ & <-). exact Hh.
- exfalso. apply (free_not_live _ _ _ _ _ INV g Hh). exists b. exact (mem_live _ _ Hb).
Qed.

#[using="RC__ X L BL LS INV ZB IM IL"] Lemma l_lists : fact_lists (strip st).
Proof.
split; [| split].
- intros sc g H. rewrite active_strip in H. pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
destruct (il_active _ _ IL sc g Hin) as (_ & Hl & _). exact (lmem_listed _ _ Hin Hl).
- intros g n Hm Hn. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st n) in *.
destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
pose proof (linked_group_listed _ _ Hb ltac:(rewrite Hn; discriminate)) as Hg.
pose proof (next_listed _ _ _ _ _ INV _ g n Hg Hn) as Hn'.
destruct (il_active _ _ IL _ n Hn') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hn' Hl)| exact Esc].
- intros g p Hm Hp. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st p) in *.
destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
destruct (m_next (MR st g)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL g) Ex) as P; rewrite Hp in P; discriminate].
pose proof (linked_group_listed _ _ Hb ltac:(rewrite Ex; discriminate)) as Hg.
pose proof (prev_listed _ _ _ _ _ INV _ g p Hg Hp) as Hp'.
destruct (il_active _ _ IL _ p Hp') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hp' Hl)| exact Esc].
Qed.

#[using="RC__ X L BL LS INV IL"] Lemma l_freelist : fact_freelist (strip st).
Proof.
intros h Hh. rewrite ctx_strip in Hh. rewrite !get_meta_rec_strip. fold (MR st h).
pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
assert (MS : forall m, In m (LS LFree) -> meta_slot (strip st) m).
{ intros m Hm. destruct (listed_meta_slot X st L BL LS INV m LFree Hm) as (a & ar & k & Ha & Hk & E). exists a, ar, k. auto. }
split; [exact (MS h Hin)|].
pose proof (il_free _ _ IL h Hin) as E. split; [rewrite E; reflexivity|].
split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|].
destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) LFree h Hin) as (p & Hp & Ep & Np).
exists p. split; [exact Ep|]. split; [exact (MS p Hp)|]. rewrite !get_meta_rec_strip. fold (MR st p).
pose proof (il_free _ _ IL p Hp) as Ep'. split; [rewrite Ep'; reflexivity|]. rewrite Np. discriminate.
Qed.
#[using="RC__ X L BL LS INV ZB IR IM IG"] Lemma l_mw : fact_mw (strip st).
Proof.
intros g. rewrite !get_meta_rec_strip. fold (MR st g).
destruct (m_mem (MR st g)) as [b|] eqn:Hb.
- destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
assert (AV : m_avail (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
assert (FR : m_freed (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
assert (MLB : m_maplen (MR st g) < 2 ^ 52).
{ destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r & Hr & _ & E & _).
destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & LT & _). pose proof (round_up_pg_spec (r_len r)). unfold LEN_MAX in LT. lia. }
split; [| lia]. unfold mw_ok. split; [exact LI|]. split; [rewrite (g_freeable _ _ _ _ _ _ GO); lia|].
split; [| lia]. destruct (g_sc _ _ _ _ _ _ GO) as [[S1 _]|(S1 & _)]; lia.
- rewrite (im_zero _ _ _ IM g Hb). cbn. unfold mw_ok. cbn. lia.
Qed.

#[using="RC__ X L BL LS INV ZB IG"] Lemma l_host_stride : fact_host_stride (strip st).
Proof.
intros g b Hb Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
unfold get_stride in *. destruct (m_last_idx (MR st g) =? 0) eqn:E0; [| reflexivity].
destruct (m_maplen (MR st g) =? 0) eqn:EM; cbn [andb negb] in *; [reflexivity|].
apply Z.eqb_eq in E0. apply Z.eqb_neq in EM. destruct (S2 E0) as [_ S27].
assert (Esc : m_sizeclass (MR st g) = 27) by lia. rewrite Esc in *. change (size_class 27) with 255 in *.
destruct S1 as [S1|S1]; [| lia].
pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT in *. lia.
Qed.

#[using="RC__ X L BL LS INV"] Lemma l_links : fact_links (strip st).
Proof.
intros g Hg. unfold lmem in Hg. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. destruct Hg as (Hm & Hn & Hp).
destruct (c_links X st L BL LS INV) as [CN CP _ _].
split.
- intros n E. rewrite get_meta_rec_strip. exact (proj1 (CN g n E)).
- intros p E. rewrite get_meta_rec_strip. exact (proj1 (CP g p E)).
Qed.

#[using="RC__ X L BL LS INV ZB IG"] Lemma l_sc0_full : fact_sc0_full (strip st).
Proof.
intros g b gh Hb Hgh Hsc. rewrite s_groups_strip in Hgh. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_live _ _ Hb) as Hh. destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai & Hg & GO).
rewrite Hg in Hgh. inversion Hgh; subst gh. cbn. exact (g_full0 _ _ _ _ _ _ GO Hsc).
Qed.

#[using="RC__ X L BL LS INV ZB NFR IG"] Lemma l_bit_stride : fact_bit_stride (strip st).
Proof.
intros g b i Hb Hi Hbits Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| exact GE].
exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 F0].
rewrite A0, F0, !Z.bits_0 in Hbits. discriminate Hbits.
Qed.

#[using="RC__ X L BL LS INV ZB NFR IR IM IL IG"] Lemma inv_lfacts : LFACTS (strip st).
Proof. constructor; [exact l_lists| exact l_freelist| exact l_mw| exact l_host_stride| exact l_links| exact l_sc0_full| exact l_bit_stride]. Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma inv_ghdr_unk : fact_ghdr_unk st.
Proof.
intros b gh o Hb Ho. destruct (hdr_hosts X st L BL LS INV b gh Hb) as [m Hm].
exact (ish_ghdr _ _ ISH b m o Hm ltac:(lia)).
Qed.

Variable resv : list (Z * Z).
Variable LB : list block.
Hypothesis CR : CORR st LB BL.
Hypothesis RESV : ld_resv L = resv.

Local Ltac inst f :=
first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV ZB) | exact (f _ _ _ _ _ INV ZB NFR)
| exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV ZB _ CR) | exact (f _ _ _ _ _ INV ZB NFR _ CR) ].

#[using="RC__ X L BL LS INV ZB NFR IR CR RESV"] Lemma inv_mfacts : @MFACTS_g resv st LB.
Proof.
constructor.
- inst LB_blocks_ok.
- inst LB_nodup.
- inst f_ticks.
- rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
- inst f_ctx.
- inst f_active.
- inst f_gmeta.
- inst f_avail_clear.
- inst f_hdr0.
- inst f_free_clear.
- inst f_hdr_clear.
- inst f_usage.
- inst f_masks.
- inst f_maplen.
- inst f_slots.
- inst f_slots_complete.
- inst f_ptrs.
- inst f_blk_unknown.
- inst f_blocks_disjoint.
- inst f_cell_ticks.
Qed.

#[using="RC__ X L BL LS INV ZB NFR IR IM IL IG ISH CR RESV"] Lemma inv_istf : @ISTF_g resv st LB.
Proof. constructor; [exact inv_mfacts| exact inv_lfacts| exact inv_ghdr_unk]. Qed.

#[using="RC__ X L BL LS INV IA"] Lemma frontier_fresh rid r o : s_regions st !! rid = Some r -> frontier st rid r <= o -> fresh_above st rid o.
Proof.
intros Hr Ho q Hq Hoq. split.
- exact (proj1 (above_frontier X st L BL LS rid r q INV Hr Hq ltac:(lia))).
- destruct (s_metas st !! q) as [mr|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & Em).
pose proof (proj2 (above_frontier X st L BL LS rid r a INV Hr ltac:(rewrite Em in Hq; exact Hq)
ltac:(rewrite Em in Hoq; unfold mslot, aadd in Hoq; cbn in Hoq; unfold AREA_HDR, META_SIZE, NSLOTS in *;
destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _);
rewrite Em in Hq; unfold mslot, aadd in Hq; cbn in Hq; rewrite Hq, Hr in Hr'; inversion Hr'; subst r'; rewrite Hq in F; unfold PGSZ in F; lia)) k Hk) as N.
rewrite <- Em, E in N. discriminate N.
Qed.

Context {sec : Z}.
Hypothesis SEC : s_secret st = sec.

#[using="RC__ X L BL LS INV ZB IR IA IM IL RESV SEC"] Lemma inv_ampre : @AMpre_g resv sec st.
Proof.
pose proof (ia_secret _ IA) as [S0 SD]. pose proof (ia_avail _ IA) as [AC AV]. pose proof (ir_cursor _ _ _ IR) as (C1 & C2 & C3).
assert (RB : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r < 2 ^ 47).
{ intros rid r Hr. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _). pose proof (round_up_ge (r_len r)). unfold alloc_ceiling in CE. lia. }
constructor.
-  unfold ctx. destruct SD as [(_ & E & _)|[_ E]]; rewrite E; lia.
- unfold ctx. destruct SD as [(E & _)|[E _]]; rewrite E; auto.
- exact SEC.
- unfold ctx. exact AC.
- unfold ctx. split; [exact C1|]. destruct (Z.eq_dec (c_avail_meta_area_count (s_ctx st)) 0) as [E|NE]; [rewrite E; lia|].
destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
destruct (C3 rid off eq_refl) as (r & Hr & _ & P1 & _ & E & _). pose proof (RB _ _ Hr). unfold PGSZ in *. nia.
- unfold ctx. destruct (ir_shift _ _ _ IR) as [SH0 [E|(rid & r & Hr & _ & E)]]; [lia|].
pose proof (RB _ _ Hr) as [_ LT]. rewrite E in LT. unfold PGSZ in LT. change 4096 with (2 ^ 12) in LT.
split; [exact SH0|]. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 38) as [|GT]; [assumption|]. exfalso.
assert (2 ^ 39 <= 2 ^ c_meta_alloc_shift (s_ctx st)) by (apply Z.pow_le_mono_r; lia). nia.
- rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
- exact (c_links X st L BL LS INV).
- intros h Hh. exact (ch_free _ (c_heads X st L BL LS INV) h Hh).
- intros g Hm Hn. fold (MR st g) in *. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
destruct h as [sc|].
{ exfalso. destruct (il_active _ _ IL sc g Hh) as (_ & [b Hb] & _). rewrite (hosts_mem _ _ _ IM _ _ Hb) in Hm. discriminate Hm. }
pose proof (il_free _ _ IL g Hh) as E. split; [rewrite E; reflexivity|]. split.
+ intros nx Hnx. fold (MR st nx). pose proof (il_free _ _ IL nx (next_listed _ _ _ _ _ INV LFree g nx Hh Hnx)) as E'. rewrite E'. reflexivity.
+ intros pv Hpv. fold (MR st pv). pose proof (il_free _ _ IL pv (prev_listed _ _ _ _ _ INV LFree g pv Hh Hpv)) as E'. rewrite E'. reflexivity.
- intros q mr Hq. destruct (ia_metas _ IA _ _ Hq) as (a & ar & k & Ha & Hk & Em). exists a, ar, k. auto.
- unfold ctx. intros NE. destruct (AV ltac:(lia)) as (a & Ht & Hav & FR).
pose proof (ia_tail _ IA a Ht) as Ha. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
exists a, ar, (NSLOTS - c_avail_meta_count (s_ctx st)). split; [exact Ea|]. split; [exact Hav|]. split; [lia|]. split; [lia|].
apply FR. lia.
- unfold ctx. intros tl Ht. pose proof (ia_tail _ IA tl Ht) as Ha. destruct (s_areas st !! tl) as [ar|]; [eexists; reflexivity| congruence].
- unfold ctx. intros NE. destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
destruct (C3 rid off eq_refl) as (r & Hr & MK & P1 & P2 & E & _).
exists (rid, off), r. cbn [fst snd]. split; [reflexivity|]. split; [exact Hr|].
split; [destruct MK as [K|K]; rewrite K; discriminate|]. split; [exact P2|]. split; [unfold PGSZ in P1; lia|].
split; [unfold lr_lo; destruct (r_kind r); unfold PGSZ in P1; lia|].
split; [pose proof (round_up_ge (r_len r)); lia|].
apply (frontier_fresh rid r off Hr). unfold frontier. rewrite EC, N.eqb_refl. lia.
- intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). exact L0.
- pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (QUZl.c_brk (s_ctx st)) as [| |rid off]; [exact I| exact I|].
destruct BR as [_ (r & Hr & K & Elen)]. exists r. split; [exact Hr|]. split; [exact K|]. split; [exact Elen|].
destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & _ & _ & MK). destruct (MK ltac:(left; exact K)) as [M1 M2].
split; [rewrite <- Elen; exact M1|]. split; [rewrite <- Elen; unfold PGSZ in *; lia|].
split; [apply (frontier_fresh rid r off Hr); rewrite (ir_brkfront _ _ _ IR _ _ Hr K); lia|].
intros q rq Hq Kq. exact (ir_brk1 _ _ _ IR _ _ _ _ Hq Hr Kq K).
- exact (f_ptrs X st L BL LS INV ZB).
Qed.
End GF.

#[using="Type"] Lemma CORR_GP X st st' L BL LS LB : INVL X st L BL LS -> GP st st' -> CORR st LB BL -> CORR st' LB BL.
Proof.
intros INV [GPR _] CR. eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3).
split; [exact C1|]. split; [exact C2|]. rewrite C3. rewrite (conc_same st st' (bslot k)); [reflexivity|].
destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

Definition JINVi (resv : list (Z * Z)) (sec : Z) (idle : list aptr) (st : mstate) (LB : list block) : Prop :=
exists L LS BL, INVL (X_as idle) st L BL LS /\ NoDup idle /\ TF0 st /\ ld_resv L = resv /\ s_secret st = sec /\ CORR st LB BL.
Definition JINV (resv : list (Z * Z)) (sec : Z) (st : mstate) (LB : list block) : Prop := exists idle, JINVi resv sec idle st LB.

#[using="Type"] Lemma jinv_top resv {sec} st0 LB t : AREACH_from resv sec st0 LB -> (s_tick st0 < t)%N -> JINV resv sec (set_tick t st0) LB.
Proof.
intros AR Ht. destruct (areach_inv resv st0 LB AR) as (L & LS & BL & INV & _ & RESV & SEC & CR).
exists [], L, LS, BL. split; [apply INVL_set_tick; [lia| exact INV]|].
split; [apply NoDup_nil; exact I|| constructor|]. split; [apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| exact Ht]|].
split; [exact RESV|]. split; [exact SEC|]. exact CR.
Qed.

#[using="Type"] Lemma jinv_ta resv {sec} idle st LB sc st1 :
JINVi resv sec idle st LB -> 0 <= sc < 48 -> ta_fail sc st st1 -> JINVi resv sec idle st1 LB /\ active st1 sc = None.
Proof.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc TA.
destruct (try_avail_ok (option (mstate * Z)) (X_as idle) L BL sc kS bS eq_refl eq_refl Hsc st LS INV) as (st1' & first & LS1 & E & TAF & RES).
unfold ta_fail in TA. rewrite E in TA. unfold kS in TA. inversion TA. subst st1' first.
destruct RES as [(_ & HA & INV1)|(g & bg & ai & idx & NZ & _)]; [| exfalso; exact (NZ eq_refl)].
split; [| exact HA]. exists L, LS1, BL. split; [exact INV1|]. split; [exact ND|].
split; [exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF)|]. split; [exact RESV|].
split; [rewrite (taf_ssec _ _ _ TAF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_taf _ _ _ TAF) CR).
Qed.

#[using="Type"] Lemma jinv_am resv {sec} idle st1 LB o st2 m :
JINVi resv sec idle st1 LB -> leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) -> JINVi resv sec (m :: idle) st2 LB.
Proof.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) (ans & o' & FL).
set (Post := fun (L' : mled) (r : option (mstate * optr)) =>
match r with
| Some (s2, Some m') => exists LS', INVL (X_as (m' :: idle)) s2 L' BL LS' /\ ~ In m' idle /\ AM_frame st1 s2 /\ L_frame L L'
| _ => True
end).
assert (FT : ftree L (alloc_meta st1 kS bS) Post).
{ apply (alloc_meta_ft _ BL Post kS bS (X_as idle) st1 L) with (LS := LS); [| | exact INV| apply amf_refl| apply lf_refl].
- intros s1 L1 LS1 _ _ _. exact I.
- intros s1 L1 LS1 m' INV1 NI AF LF. cbn. exists LS1. split; [exact INV1|]. split; [exact NI|]. split; [exact AF| exact LF]. }
pose proof (ftree_prun pans_mem pupd_mem pans_mem_range (alloc_meta st1 kS bS) L Post o FT) as PT.
unfold mrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L' & CP & POST). cbn in POST.
destruct POST as (LS' & INV2 & NI & AF & LF).
exists L', LS', BL. split; [exact INV2|].
split; [apply NoDup_cons; split; [intros Hin; apply NI; apply list_elem_of_In; exact Hin| exact ND]|].
split; [exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF)|].
split; [rewrite (lf_resv _ _ LF); exact RESV|].
split; [rewrite (amf_ssec _ _ AF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_amf _ _ AF) CR).
Qed.

#[using="Type"] Lemma ist_jinv resv {sec} st0 LB st : AREACH_from resv sec st0 LB -> IST st0 st -> JINV resv sec st LB.
Proof.
intros AR. induction 1 as [t Ht|o st sc st1 st2 m _ IH Hsc TA AM].
- exact (jinv_top resv st0 LB t AR Ht).
- destruct IH as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. exists (m :: idle). exact (jinv_am _ _ _ _ _ _ _ J1 AM).
Qed.

#[using="Type"] Lemma jinv_slot resv {sec} idle st LB o f sc req st3 idx :
JINVi resv sec idle st LB -> 0 <= sc < 48 -> req_ok sc req ->
leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)) ->
exists L LS BL L3 LS3, INVL (X_as idle) st L BL LS /\ SLOT_POST idle sc req st L BL st3 idx L3 LS3
/\ ld_resv L3 = resv /\ s_secret st3 = sec /\ CORR st3 LB BL.
Proof.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc [Hreq Hfit] (ans & o' & FL).
unfold mrun in FL. apply (@alloc_slot_follow_mono _ _ pans_mem pupd_mem full_lay f (f + 49)) in FL; [| lia].
set (Post := fun (L' : mled) (r : option (mstate * Z)) =>
match r with Some (s3, i) => exists LS3, SLOT_POST idle sc req st L BL s3 i L' LS3 | None => True end).
assert (FT : ftree L (alloc_slot full_lay (f + 49) st sc req kS bS) Post).
{ apply (alloc_slot_ft _ Post (f + 49)%nat sc idle st L BL LS req kS bS ltac:(lia) INV TF ND Hsc Hreq Hfit).
intros st1 i L1 LS1 SP. cbn. exists LS1. exact SP. }
pose proof (ftree_prun pans_mem pupd_mem pans_mem_range _ L Post o FT) as PT.
destruct (ptree_follow _ L _ ans PT FL) as (L3 & CP & POST). cbn in POST. destruct POST as [LS3 SP].
exists L, LS, BL, L3, LS3. split; [exact INV|]. split; [exact SP|].
split; [rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
destruct SP as (_ & _ & GP3 & _). split; [rewrite (proj1 (proj2 GP3)); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV GP3 CR).
Qed.

#[using="Type"] Theorem ist_facts_proof : forall {resv sec} st0 LB st, AREACH_from resv sec st0 LB -> IST st0 st -> @ISTF_g resv st LB.
Proof.
intros resv sec st0 LB st AR H. destruct (ist_jinv resv st0 LB st AR H) as (idle & L & LS & BL & INV & ND & TF & RESV & SEC & CR).
exact (inv_istf (X_as idle) st L BL LS INV eq_refl eq_refl resv LB CR RESV).
Qed.

#[using="Type"] Theorem istr_facts_proof : forall {resv sec} st0 LB st3, AREACH_from resv sec st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB.
Proof.
intros resv sec st0 LB st3 AR (o & st & f & sc & req & idx & H & Hsc & RQ & LF).
destruct (ist_jinv resv st0 LB st AR H) as [idle J].
destruct (jinv_slot resv idle st LB o f sc req st3 idx J Hsc RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & RESV & SEC & CR).
destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
- exact (inv_istf (X_as idle) st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
- exact (inv_istf _ st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
Qed.

#[using="Type"] Theorem nest_facts_proof : forall {resv sec} st0 LB st sc st1 o st2 m f j req o' st3 idx,
AREACH_from resv sec st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
0 <= j < 48 -> req_ok j req ->
leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
nest_ok m st3.
Proof.
intros resv sec st0 LB st sc st1 o st2 m f j req o' st3 idx AR H Hsc TA AM Hj RQ LF.
destruct (ist_jinv resv st0 LB st AR H) as [idle J].
destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. pose proof (jinv_am _ _ _ _ _ _ _ J1 AM) as J2.
destruct (jinv_slot resv (m :: idle) st2 LB o' f j req st3 idx J2 Hj RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & _).
assert (K : forall X3, INVL X3 st3 L3 BL LS3 -> x_idle X3 = m :: idle -> nest_ok m st3).
{ intros X3 INV3 XI. destruct (im_idle _ _ _ (proj1 (proj2 (proj2 INV3))) m ltac:(rewrite XI; left; reflexivity)) as [Em NI].
split; [unfold get_meta_rec; rewrite Em; reflexivity|].
intros h Hh. pose proof (head_listed _ _ _ _ _ INV3 LFree h Hh) as Hin. split.
- intros ->. apply NI. exists LFree. exact Hin.
- intros Hp. apply NI. exists LFree. exact (prev_listed _ _ _ _ _ INV3 LFree h m Hin Hp). }
destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
- exact (K _ INV3 eq_refl).
- exact (K _ INV3 eq_refl).
Qed.

#[using="Type"] Theorem areach_ampre_proof : forall {resv sec} st LB, AREACH_from resv sec st LB -> @AMpre_g resv sec st.
Proof.
intros resv sec st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & RESV & SEC & _).
exact (inv_ampre x0 st L BL LS INV eq_refl resv RESV SEC).
Qed.

#[using="Type"] Theorem ist_ampre_proof : forall {resv sec}, AMP_AS_g resv sec (am_pre_g resv sec).
Proof.
intros resv sec st0 LB st sc st1 AR H Hsc TA.
destruct (ist_jinv resv st0 LB st AR H) as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [(L & LS & BL & INV & _ & _ & RESV & SEC & _) _].
exact (inv_ampre (X_as idle) st1 L BL LS INV eq_refl resv RESV SEC).
Qed.

Local Definition g1 := (@ist_facts_proof : forall resv sec st0 LB st, AREACH_from resv sec st0 LB -> IST st0 st -> @ISTF_g resv st LB).
Local Definition g2 := (@istr_facts_proof : forall resv sec st0 LB st3, AREACH_from resv sec st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB).
Local Definition g3 := (@nest_facts_proof : forall resv sec st0 LB st sc st1 o st2 m f j req o' st3 idx,
AREACH_from resv sec st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
0 <= j < 48 -> req_ok j req ->
leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
nest_ok m st3).
Local Definition g4 := (@areach_ampre_proof : forall resv sec st LB, AREACH_from resv sec st LB -> @AMpre_g resv sec st).
Local Definition g5 := (@ist_ampre_proof : forall resv sec, AMP_AS_g resv sec (am_pre_g resv sec)).

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 QytA Qnxq QJE4.Mq4 QPjm.Mq4 Qy5Y.Mq5 QBpc.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QNAo.Mq1 Q3o5.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <->
rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
split.
- intros [[[W1 W2] [B1 B2]] WR].
pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
destruct WR as (HA & HN & HW).
split; [split; [split; assumption|] | split; [split; assumption|]].
+ split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
+ split; [lia|]. split; [lia|]. intros i Hi.
replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
- intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
pose proof (cells_bytes_length cs1 W1) as L1.
split; [split; [split; assumption|] |].
+ split; [exact B1|]. rewrite L1. exact B2.
+ split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
* apply HW1. lia.
* replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

End RC__1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma wr8_proj q v st :
s_regions (wr8 q v st) = s_regions st /\ s_groups (wr8 q v st) = s_groups st /\ s_areas (wr8 q v st) = s_areas st
/\ s_tick (wr8 q v st) = s_tick st /\ s_next_rid (wr8 q v st) = s_next_rid st /\ s_reserved (wr8 q v st) = s_reserved st
/\ s_ctx (wr8 q v st) = s_ctx st /\ s_slots (wr8 q v st) = s_slots st /\ s_metas (wr8 q v st) = s_metas st.
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma cells_wr8_other st q v o : o <> snd q ->
(r_cells (get_shadow (wr8 q v st) (fst q))) !! o = (r_cells (get_shadow st (fst q))) !! o.
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma cells_wr8_same st q v :
(r_cells (get_shadow (wr8 q v st) (fst q))) !! (snd q) = Some (Z.land v 255, s_tick st).
Proof. rewrite get_shadow_wr8_same. cbn [r_cells]. apply lookup_insert_eq. Qed.

#[using="Type"] Lemma hav_wr8 st q v : r_hav (get_shadow (wr8 q v st) (fst q)) = r_hav (get_shadow st (fst q))
/\ r_havp (get_shadow (wr8 q v st) (fst q)) = r_havp (get_shadow st (fst q)).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

#[using="Type"] Lemma cells_wr8_other' st rid off v o : o <> off ->
(r_cells (get_shadow (wr8 (rid, off) v st) rid)) !! o = (r_cells (get_shadow st rid)) !! o.
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

#[using="Type"] Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

#[using="Type"] Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

#[using="Type"] Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

#[using="Type"] Lemma cell_read_wr8_other' st rid off v o : o <> off ->
cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

#[using="Type"] Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

#[using="Type"] Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
- apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

#[using="Type"] Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

#[using="Type"] Lemma zh_proj : forall k i st,
let st' := zero_hdrs p s i k st in
s_regions st' = s_regions st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
/\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
/\ s_ctx st' = s_ctx st /\ s_slots st' = s_slots st /\ s_metas st' = s_metas st.
Proof.
induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

#[using="Type"] Lemma zh_hav : forall k i st,
r_hav (get_shadow (zero_hdrs p s i k st) (fst p)) = r_hav (get_shadow st (fst p))
/\ r_havp (get_shadow (zero_hdrs p s i k st) (fst p)) = r_havp (get_shadow st (fst p)).
Proof.
induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

#[using="Type"] Lemma zh_cells_other o : forall k i st,
(forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
(r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! o = (r_cells (get_shadow st (fst p))) !! o.
Proof.
induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
rewrite IH by (intros j Hj; apply Ho; lia).
pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma zh_cells_at : 0 < s -> forall k i st j, i <= j < i + Z.of_nat k ->
(r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! (snd p + UNIT + j * s - 4) = Some (0, s_tick st).
Proof.
intros HS. induction k as [|k IH]; intros i st j Hj; cbn [zero_hdrs]; [lia|].
destruct (Z.eq_dec j i) as [->|NE].
- rewrite zh_cells_other by (intros j' Hj'; nia).
pose proof (cells_wr8_same st (aadd p (UNIT + i * s - 4)) 0) as C. cbn [fst snd aadd] in C.
replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. rewrite C. reflexivity.
- rewrite (IH (i + 1) _ j) by lia. reflexivity.
Qed.

#[using="Type"] Lemma zh_cell_read_other o : forall k i st,
(forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="Type"] Lemma zh_ticks_ok : forall k i st, ticks_ok st -> ticks_ok (zero_hdrs p s i k st).
Proof. induction k as [|k IH]; intros i st TK; cbn [zero_hdrs]; [exact TK|]. apply IH. apply ticks_ok_wr8. exact TK. Qed.

#[using="Type"] Lemma zh_cell_read_at : 0 < s -> forall k i st j, ticks_ok st -> i <= j < i + Z.of_nat k ->
cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) (snd p + UNIT + j * s - 4) = Known 0.
Proof.
intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
destruct (Z.eq_dec j i) as [->|NE].
- rewrite zh_cell_read_other by (intros j' Hj'; nia).
pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
- apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

#[using="Type"] Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) :
(forall ch, f ch = true -> 12 < fst ch) ->
existsb f (filter (fun ch : Z * N => Is_true (12 <? fst ch)) l) = existsb f l.
Proof.
intros Hf. induction l as [|ch l IH]; [reflexivity|].
rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

#[using="Type"] Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

#[using="Type"] Lemma cell_read_hdr_havoc_other st b o :
snd b mod 16 = 0 -> ~ (snd b <= o < snd b + 12) ->
cell_read (get_shadow (hdr_havoc b st) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id].
unfold cell_read. cbn [r_cells r_hav r_havp].
destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
- rewrite E, lookup_insert_eq. cbn [default from_option id].
assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
fold (get_shadow st (fst b)).
destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma hav_hdr_havoc_other st b u : u <> snd b / 16 ->
(r_hav (get_shadow (hdr_havoc b st) (fst b))) !! u = (r_hav (get_shadow st (fst b))) !! u.
Proof.
intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma cells_hdr_havoc st b : r_cells (get_shadow (hdr_havoc b st) (fst b)) = r_cells (get_shadow st (fst b))
/\ r_havp (get_shadow (hdr_havoc b st) (fst b)) = r_havp (get_shadow st (fst b)).
Proof.
unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate :=
wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
(r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.

#[using="Type"] Lemma pp_eq : pp st3 g b idx = p.
Proof. reflexivity. Qed.

#[using="SC"] Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

#[using="r N SO STR"] Lemma nest_model_eq :
upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
unfold upd_meta. rewrite rec_zero_hdrs.
change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

#[using="Type"] Lemma ntW_proj :
s_regions nt_stW = s_regions st3 /\ s_groups nt_stW = s_groups st3 /\ s_areas nt_stW = s_areas st3
/\ s_tick nt_stW = s_tick st3 /\ s_next_rid nt_stW = s_next_rid st3 /\ s_reserved nt_stW = s_reserved st3
/\ s_ctx nt_stW = s_ctx st3 /\ s_slots nt_stW = s_slots st3.
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma ntT_proj :
s_regions nt_stT = s_regions st3 /\ s_groups nt_stT = s_groups st3 /\ s_areas nt_stT = s_areas st3
/\ s_tick nt_stT = s_tick st3 /\ s_next_rid nt_stT = s_next_rid st3 /\ s_reserved nt_stT = s_reserved st3
/\ s_ctx nt_stT = s_ctx st3 /\ s_slots nt_stT = s_slots st3.
Proof.
unfold nt_stT. destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

#[using="G0"] Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
destruct (decide (q = mm)) as [->|NE].
- rewrite get_meta_rec_put_same, G0. reflexivity.
- rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

#[using="Type"] Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

#[using="Type"] Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

#[using="Type"] Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

#[using="Type"] Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
rewrite get_shadow_wr8_other by exact NE.
change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma ntW_hav :
r_hav (get_shadow nt_stW (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stW (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
unfold nt_stW, enf0_st, wr16.
split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

#[using="Type"] Lemma ntT_hav :
r_hav (get_shadow nt_stT (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stT (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
rewrite A, B. exact ntW_hav.
Qed.

Definition nt_written (o : Z) : Prop :=
o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

#[using="jn sc szc N SC J"] Lemma ntW_cells_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
(r_cells (get_shadow nt_stW (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

#[using="jn sc szc N SC J"] Lemma ntW_cell_read_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
cell_read (get_shadow nt_stW (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="jn N SC J CNT"] Lemma ntT_cells_other o : ~ nt_written o ->
(r_cells (get_shadow nt_stT (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
rewrite zh_cells_other.
2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

#[using="jn N SC J CNT"] Lemma ntT_cell_read_other o : ~ nt_written o ->
cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="TK3"] Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
unfold nt_stW. apply ticks_ok_wr8.
assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

#[using="jn N SC J CNT TK3"] Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

#[using="jn N SC J CNT TK3"] Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
destruct (Z.eq_dec k 3) as [->|N3].
{ eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
rewrite 2 cell_read_wr8_other' by lia.
destruct (Z.eq_dec k 1) as [->|N1].
{ eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
assert (k = 2) by lia. subst k.
rewrite cell_read_wr8_other' by lia.
eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.

#[using="jn sc szc N SC J SO"] Lemma slot_geom :
m_mem (get_meta_rec st3 g) = Some b /\ (s_regions st3) !! (fst b) = Some r /\ r_kind r = RKGroup
/\ 0 <= snd b /\ snd b mod 16 = 0 /\ 0 <= idx /\ 16 <= strideg /\ strideg mod 16 = 0
/\ X + strideg <= round_up_pg (r_len r) /\ 0 <= strideg * idx
/\ (forall b' gh, (s_groups st3) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= X - 4 \/ X + strideg - 4 <= snd b').
Proof.
destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
fold strideg in Sspan, Ss16, Ssmod, Snogrp.
assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
repeat (split; [first [assumption | unfold X; lia] |]).
intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

#[using="r jn sc szc N SC J SO"] Lemma X_mod16 : X mod 16 = 0.
Proof.
destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

#[using="jn N SC J CNT SO G0 MSmm FRESH3"] Lemma nt_tail_hyps :
meta_slot nt_stT mm
/\ get_meta_rec nt_stT mm = mkMeta None None None 0 0 0 0 0 0
/\ (s_regions nt_stT) !! (fst p) = Some r
/\ 0 <= snd p /\ snd p mod 16 = 0 /\ snd p + 16 <= round_up_pg (r_len r)
/\ (s_groups nt_stT) !! p = None
/\ (forall b' gh, (s_groups nt_stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b')
/\ (forall o v t, snd p <= o < snd p + 12 -> (r_cells (get_shadow nt_stT (fst p))) !! o = Some (v, t) -> (t < s_tick nt_stT)%N)
/\ s_tick nt_stT = s_tick st3.
Proof.
destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
destruct ntT_proj as (PR & PG & PA & PT & _).
split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
split. { rewrite PR. exact Sreg. }
split. { unfold p, X. cbn. lia. }
split. { exact X_mod16. }
split. { unfold p. cbn [snd]. lia. }
split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
eapply FRESH3; [| exact Hc]. lia. }
exact PT.
Qed.

Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

#[using="r jn N SC J CNT SO G0 MSmm FRESH3"] Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

#[using="r jn N SC J CNT SO G0 MSmm FRESH3"] Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

#[using="Type"] Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

#[using="r jn N SC J SO"] Lemma ntF_cell_read_other o : ~ (X <= o < X + 12) ->
cell_read (get_shadow stF (fst b)) o = cell_read (get_shadow nt_stT (fst b)) o.
Proof.
intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

#[using="Type"] Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

#[using="Type"] Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

#[using="Type"] Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

#[using="jn N SC J CNT SO STR FITN G0 MSmm TK3 FRESH3"] Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
intros RQ FIT. pose proof szc_range as SZR.
destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
pose proof ntF_stride as STF.
pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
destruct ntT_proj as (PR & PG & PA & PT & _).
constructor; rewrite ?STF.
- rewrite ntF_rec_mt. reflexivity.
- rewrite PF1, PR. exact Sreg.
- exact Skind.
- exact TP0.
- exact TP16.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
- lia.
- rewrite Z.mul_comm. apply Z_mod_mult.
- lia.
- exact RQ.
- exact FIT.
- intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
+ left. unfold p. cbn [snd]. lia.
+ rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right]. (clear - CNT STR FITN RQ FIT H; nia).
- unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
- intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
- unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
- apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
- rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

#[using="jn N SC J CNT"] Lemma ntF_span_cells o : X + 16 <= o < X + 16 + 16 * szc - 4 ->
(r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

#[using="r jn N SC J SO"] Lemma ntF_span_hav o : X + 16 <= o -> (r_hav (get_shadow stF (fst b))) !! (o / 16) = (r_hav (get_shadow st3 (fst b))) !! (o / 16).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

#[using="r jn N SC J CNT SO"] Lemma ntF_rdv13 o :
(r_cells (get_shadow st3 (fst b))) !! (X + 13) = None ->
(r_hav (get_shadow st3 (fst b))) !! ((X + 13) / 16) = None ->
(r_havp (get_shadow st3 (fst b))) !! ((X + 13) / 4096) = None ->
rdv pans_mem o stF (fst b, X + 13) = 0.
Proof.
intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

#[using="r jn N SC J CNT SO TK3"] Lemma ntF_unknown off h : 0 <= off ->
cell_read (get_shadow stF (fst b)) off = Unknown h ->
grp_hdr_cov stF (fst b) off
\/ (cell_read (get_shadow st3 (fst b)) off = Unknown h /\ ~ (X - 3 <= off < X) /\ ~ (exists j, 0 <= j <= cnt /\ off = X + 12 + j * (16 * szc))).
Proof.
intros Ho Hc. pose proof szc_range as SZR.
destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
all: right; rewrite ntF_cell_read_other in Hc by lia.
- destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E). nia.
+ exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
- destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
[destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
+ exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

#[using="Type"] Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.

End RC__1.
