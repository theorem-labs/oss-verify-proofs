(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Qy5Y Q4J3 Qnxq QPjm QTyG QZAi QUZl Q7S0 Qfya Ql2m QGeV Qatc Q9kF QTp6 QCwx QFqQ QkLq QYnB Q98Z QnkH QlbW QYZ0 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Qy5Y.Mq4 Q4J3.Mq3 Qnxq QPjm.Mq4 Qy5Y.Mq6.

Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya Ql2m.Mq3 QGeV Qatc.

Import QTp6.
Import QCwx.Mq1 QFqQ.Mq0 QkLq.Mq2 QYnB.Mq7 Q98Z.Mq2 QkLq.Mq0 QnkH.Mq5 QlbW.Mq0 QYnB.Mq5.
Import QYZ0.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition aj_rstat : list (Z * Z) :=
[(RCTX, RCTX + 928); (RMLOCK, RMLOCK + 4); (RVMLOCK, RVMLOCK + 4); (RNEED_LOCKS, RNEED_LOCKS + 1); (RPAGE_SIZE, RPAGE_SIZE + 8);
(RGOT_SSP, RGOT_SSP + 8); (RSSP_GUARD, RSSP_GUARD + 8)].

Definition AJ_DATA_LO : Z := 0xe2000.
Definition AJ_IMG_HI : Z := 0x645000.
Definition S_AJ : mng_sig :=
MSIG RHEAP (fun m B => rauxv_ok m B /\ alloc_ceiling <= B) RATP rmalloc_entry RFREE_SYM 8192

0x10000 AJ_DATA_LO AJ_IMG_HI (RCTX, RCTX + 928) aj_rstat ref_reserved
[(RPAGE_SIZE, cells_bytes [C8 (wz 4096)]); (RGOT_SSP, cells_bytes [C8 (wz RSSP_GUARD)]); (RSSP_GUARD, cells_bytes [C8 rc_canary])].

Lemma wstat_static : forall a, in_ivs (mg_wstat S_AJ) a <-> ralloc_static a.
Proof.
intros a. unfold in_ivs, mg_wstat, ralloc_static. cbn [S_AJ mg_ctx mg_tp]. split.
- intros (iv & [<-|[<-|[]]] & Hr); cbn [fst snd] in Hr; [left | right]; unfold RATP, RERRNO, RCTX in *; lia.
- intros [Hr|Hr]; [exists (RCTX, RCTX + 928) | exists (RATP + -164, RATP + -164 + 4)];
(split; [cbn; auto | cbn [fst snd]; unfold RATP, RERRNO, RCTX in *; lia]).
Qed.

Lemma mclient_r : forall LB SP a, mclient S_AJ LB SP a <-> rclient_addr LB SP a.
Proof.
intros LB SP a. unfold mclient, rclient_addr. cbn [S_AJ mg_data_lo mg_img_hi]. rewrite wstat_static. reflexivity.
Qed.

Lemma mpres_r : forall LB SP m m', rheap_pres LB SP m m' -> mpres rsegs S_AJ LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc. apply H; [exact Ha| apply mclient_r; exact Hc]. Qed.

Lemma mrange_r : forall A n, rblock_range A n -> mrange S_AJ A n.
Proof. intros A n H. exact H. Qed.

Lemma aj_malloc : mmalloc_stmt rsegs S_AJ.
Proof.
unfold mmalloc_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB n lo B errv RH [AUX HB] Hsp STK Hlo Hlo2 ERR MI Etp Ea0 Hn.
cbn [S_AJ mg_heap mg_tp mg_stack mg_malloc] in *.
eapply implM_mono.
- exact (rmalloc_impl_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB n lo B errv RH AUX Hsp STK Hlo Hlo2 ERR MI Etp Ea0 Hn).
- intros r s' ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
E & MI' & STK' & ERR' & AUX' & PRES & _ & _ & CASE).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
split; [exact E|]. split; [exact MI'|]. split; [exact STK'|]. split; [exact ERR'|].
split; [split; [exact AUX'| exact HB]|]. split; [apply mpres_r; exact PRES|].
destruct r as [p|].
+ destruct CASE as (A & junk & Ea & RNG & RH' & CELLS & _). exists A, junk.
split; [exact Ea|]. split; [apply mrange_r; exact RNG|]. split; [exact RH'| exact CELLS].
+ exact CASE.
Qed.

Lemma aj_free : mfree_stmt rsegs S_AJ.
Proof.
unfold mfree_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB p A n lo B errv RH Hin [AUX HB] Hsp STK Hlo Hlo2 ERR MI Etp Ea0.
cbn [S_AJ mg_heap mg_tp mg_stack mg_free] in *.
eapply implM_mono.
- exact (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB p A n lo B errv RH Hin AUX Hsp STK Hlo Hlo2 ERR MI Etp Ea0).
- intros r s' ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
E & MI' & STK' & ERR' & AUX' & PRES & _ & _ & RH').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [exact E|]. split; [exact MI'|]. split; [exact STK'|]. split; [exact ERR'|].
split; [split; [exact AUX'| exact HB]|]. split; [apply mpres_r; exact PRES| exact RH'].
Qed.

Lemma aj_hinv : forall s LB m, RHEAP s LB m ->
exists st LBa, Permutation LBa LB /\ strip st = ps_m s /\ HINV_from ref_reserved rc_secret st (ps_brk s) LBa.
Proof. intros s LB m (st & LB0 & HP & Es & _ & HI). exists st, LB0. auto. Qed.

Lemma aj_ctx_wr : forall s LB m a, RHEAP s LB m -> RCTX <= a < RCTX + 928 -> wview rsegs m (wa a) <> None.
Proof.
intros s LB m a (st & LB0 & _ & _ & MR & _) Ha. destruct MR as (_ & CX & _). destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & _).
assert (W : forall A n, wr_at rsegs m A n -> A <= a < A + n -> wview rsegs m (wa a) <> None).
{ intros A n (_ & _ & H) Hr. replace a with (A + (a - A)) by lia. apply H. lia. }
destruct (Z.lt_ge_cases a (RCTX + 80)) as [L1|L1].
{ apply (W RCTX 80); [apply (rw_cells_wr_at rsegs m RCTX (ctx_head_cells st) 80 C1); cbn; lia | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 464)) as [L2|L2].
{ apply (W (RCTX + 80) 384); [destruct C2 as [_ Hw]; rewrite actives_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 848)) as [L3|L3].
{ apply (W (RCTX + 464) 384); [destruct C3 as [_ Hw]; rewrite usages_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 880)) as [L4|L4].
{ apply (W (RCTX + 848) 32); [destruct C4 as [_ Hw]; rewrite unmap_seqs_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 912)) as [L5|L5].
{ apply (W (RCTX + 880) 32); [destruct C5 as [_ Hw]; rewrite bouncess_length in Hw; exact Hw | lia]. }
apply (W (RCTX + 912) 16); [apply (rw_cells_wr_at rsegs m (RCTX + 912) (ctx_tail_cells st) 16 C6); cbn; lia | lia].
Qed.

Lemma region_dyn : forall st Lg BL LS rid r a,
INVL x0 st Lg BL LS -> (forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a.
Proof.
intros st Lg BL LS rid r a (IR & _) HPG Hr Ha.
assert (Hel : In (rid, r) (map_to_list (s_regions st))) by (apply list_elem_of_In, elem_of_map_to_list; exact Hr).
destruct (ir_shape _ _ _ IR rid r Hr) as (_ & _ & Hlen & _).
unfold lr_lo in Ha. destruct (r_kind r) eqn:K.
-  right. exists (r_base r + PGSZ, round_up_pg (r_len r) - PGSZ). split.
+ unfold doranges. apply in_or_app. right.
assert (E : ld_brkreg Lg = Some (r_base r, r_len r)) by (apply (ir_brkreg _ _ _ IR); exists rid, r; auto).
rewrite E. left. reflexivity.
+ cbn [fst snd]. unfold PGSZ. lia.
-  right. exists (r_base r, round_up_pg (r_len r)). split.
+ unfold doranges. apply in_or_app. left.
pose proof (ir_metas _ _ _ IR) as PM.
assert (Hm : In (r_base r, r_len r, frontier st rid r / PGSZ - 1) (ld_metas Lg)).
{ eapply Permutation_in; [apply Permutation_sym; exact PM|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [exact Hel| cbn [snd]; rewrite K; reflexivity]. }
apply in_map_iff. exists (r_base r, r_len r, frontier st rid r / PGSZ - 1). split; [reflexivity| exact Hm].
+ cbn [fst snd]. lia.
-  left. exists (r_base r), (r_len r).
pose proof (ir_groups _ _ _ IR) as PG.
assert (Hg : In (r_base r, r_len r) (ld_groups Lg)).
{ eapply Permutation_in; [apply Permutation_sym; exact PG|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [exact Hel| cbn [snd]; rewrite K; reflexivity]. }
split; [exact Hg|]. pose proof (HPG _ _ Hg) as Hmod.
assert (E : round_up_pg (r_len r) = r_len r).
{ unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
rewrite (Z.mod_opp_l_z (r_len r) 4096) by lia. lia. }
rewrite E in Ha. lia.
Qed.

Lemma aj_agree : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aj_rstat a \/ mng_dyn Lg a -> m' (wa a) = m (wa a)) -> RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aj_rstat -> lo <= a < hi -> in_ivs aj_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
eapply rmrep_transport_agree'; [exact MR|]. intros a Ha HF. apply AG; [exact Ha|].
destruct HF as [[C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C].
- left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
- left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
- left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
- left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
- left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
- right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
- right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
- right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
- left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
- left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- right. destruct C as (rid & r & Hr & K & Hin). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
Qed.

Lemma rrepfoot_not_block : forall st LB0 m b a, rmrep st m -> AREACH_from ref_reserved rc_secret st LB0 -> In b LB0 ->
blk_addr b <= a < blk_addr b + blk_size b -> ~ rrepfoot st a.
Proof.
intros st LB0 m b a MR AR INb Hab RF.
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4'. lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
- destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
+ rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
+ pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
- destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
- unfold RGOT_SSP in R8. lia.
- unfold RSSP_GUARD in R9. lia.
Qed.

Lemma aj_agree_blk : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aj_rstat a \/ mng_dyn Lg a -> ~ in_block LB a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG WV.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aj_rstat -> lo <= a < hi -> in_ivs aj_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
eapply rmrep_transport_agree; [exact MR| |].
- intros a Ha HF.
assert (NB : ~ in_block LB a).
{ intros (b & Hb & Hr). apply (rrepfoot_not_block st LB0 m b a MR (proj2 HI)); [| exact Hr| exact HF].
eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]. }
apply AG; [exact Ha| | exact NB].
destruct HF as [C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
+ left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
+ left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
+ left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
+ left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
+ right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
+ right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
+ right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
+ left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
+ left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- intros a Ha (rid & r & Hr & K & Hin). apply (WV a Ha). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
Qed.

Lemma rmrep_transport_rt : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) -> ~ (RGOT_SSP <= a < RGOT_SSP + 8) -> ~ (RSSP_GUARD <= a < RSSP_GUARD + 8) -> m' (wa a) = m (wa a)) ->
bytes_at rsegs m' RPAGE_SIZE (cells_bytes [C8 (wz 4096)]) ->
bytes_at rsegs m' RGOT_SSP (cells_bytes [C8 (wz RSSP_GUARD)]) ->
bytes_at rsegs m' RSSP_GUARD (cells_bytes [C8 rc_canary]) ->
wr_at rsegs m' RPAGE_SIZE 8 -> wr_at rsegs m' RGOT_SSP 8 -> wr_at rsegs m' RSSP_GUARD 8 ->
(forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
rmrep st m'.
Proof.
intros st m m' (WF & CX & GL & AR & GR & SH) AG B3 B4 B5 W3 W4 W5 WG.
pose proof WF as (Hres & WR & DJ & WA & WGr).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)) ->
rw_cells rsegs m' A cs).
{ intros A cs H HP HN. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha.
destruct (HN a Ha) as (N1 & N2 & N3). apply AG; [lia| apply HP; exact Ha| exact N1| exact N2| exact N3]. }
assert (RT : forall A cs, rw_cells rsegs m A cs -> bytes_at rsegs m' A (cells_bytes cs) -> wr_at rsegs m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs).
{ intros A cs [[Wf _] _] Hb Hw. split; [split; [exact Wf| exact Hb]| exact Hw]. }
assert (AG' : forall a, 0 <= a < 2^64 -> rrepfoot st a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8) -> m' (wa a) = m (wa a)).
{ intros a Ha Hf (N1 & N2 & N3). exact (AG a Ha Hf N1 N2 N3). }
assert (OFFIMG : forall a, a < 0x10000 \/ 0x645000 <= a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Ha. unfold RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. lia. }
assert (INCTX : forall a, RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RNEED_LOCKS <= a < RNEED_LOCKS + 1 \/ RVMLOCK <= a < RVMLOCK + 4 ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Ha. unfold RCTX, RMLOCK, RNEED_LOCKS, RVMLOCK, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. lia. }

assert (DYNOFF : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> a < 0x10000 \/ 0x645000 <= a).
{ intros rid r a Hr Ha. destruct (WR rid r Hr) as (R0 & _ & _ & _ & RF). pose proof (rreserved_disjoint1 _ _ RF) as D.
pose proof (lr_lo_ge r). lia. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
pose proof (u64arr_bound rsegs m _ _ C2) as Bd2. pose proof (u64arr_bound rsegs m _ _ C3) as Bd3.
pose proof (u8arr_bound rsegs m _ _ C4) as Bd4. pose proof (u8arr_bound rsegs m _ _ C5) as Bd5.
rewrite actives_length in Bd2. rewrite usages_length in Bd3. rewrite unmap_seqs_length in Bd4. rewrite bouncess_length in Bd5.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_ctx| apply INCTX; left]; unfold RCTX in *; lia.
+ eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ apply TC; [exact C6 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_ctx| apply INCTX; left]; unfold RCTX in *; lia.
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_mlock| apply INCTX; right; left]; unfold RMLOCK in *; lia.
+ apply TC; [exact G2 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_nl| apply INCTX; right; right; left]; unfold RNEED_LOCKS in *; lia.
+ exact (RT _ _ G3 B3 W3).
+ exact (RT _ _ G4 B4 W4).
+ exact (RT _ _ G5 B5 W5).
+ apply TC; [exact G6 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_vmlock| apply INCTX; right; right; right]; unfold RVMLOCK in *; lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3). destruct (WA ak ar Ha) as (ra & Hra & _).
assert (OFF : forall a, conc st ak <= a < conc st ak + 4096 -> ~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Hr. apply OFFIMG. exact (DYNOFF (fst ak) ra a Hra (rarea_in_live st ak ar ra a WF Ha Hra Hr)). }
split; [|split].
+ apply TC; [exact A1 | |]; intros a H; cbn in H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk | |]; unfold meta_cells; cbn [cells_size csize Nat.add length];
unfold AREA_HDR, META_SIZE, NSLOTS in *; intros a H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
+ apply TC; [exact A3 | |]; intros a H; cbn in H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. destruct (WGr b gh Hb) as (rb & Hrb & _).
apply TC; [exact R | |]; intros a H; cbn in H; [eapply rrepfoot_group; [exact Hb|lia]|].
apply OFFIMG. apply (DYNOFF (fst b) rb a Hrb). apply (rgroup_in_live st b gh rb a WF Hb Hrb). lia.
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
split.
+ destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG'; [lia| |].
* eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
* apply OFFIMG. apply (DYNOFF rid r a Hr). rewrite (lr_lo_group r Hk). lia.
Qed.

Lemma aj_agree_rt : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aj_rstat a \/ mng_dyn Lg a -> ~ in_block LB a ->
~ (exists c, In c (mg_rtc S_AJ) /\ fst c <= a < fst c + Z.of_nat (length (snd c))) -> m' (wa a) = m (wa a)) ->
Forall (fun c => bytes_at rsegs m' (fst c) (snd c) /\ wr_at rsegs m' (fst c) (Z.of_nat (length (snd c)))) (mg_rtc S_AJ) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG RTC WM.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aj_rstat -> lo <= a < hi -> in_ivs aj_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
cbn [S_AJ mg_rtc] in RTC, AG. inversion RTC as [|c1 l1 [B3 W3] RTC1]; subst. inversion RTC1 as [|c2 l2 [B4 W4] RTC2]; subst. inversion RTC2 as [|c3 l3 [B5 W5] _]; subst.
cbn [fst snd] in B3, B4, B5, W3, W4, W5.
eapply rmrep_transport_rt; [exact MR| | exact B3| exact B4| exact B5| exact W3| exact W4| exact W5|].
2: { intros a Ha (rid & r & Hr & K & Hin). apply (WM a Ha). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin. }
intros a Ha HF N1 N2 N3.
assert (NB : ~ in_block LB a).
{ intros (b & Hb & Hr). apply (rrepfoot_not_block st LB0 m b a MR (proj2 HI)); [| exact Hr| exact HF].
eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]. }
apply AG; [exact Ha| | exact NB|].
- destruct HF as [C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
+ left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
+ left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
+ left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
+ left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
+ right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
+ right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
+ right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
+ left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
+ left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- intros (c & [<-|[<-|[<-|[]]]] & Hr); cbn [fst snd] in Hr; change (Z.of_nat (length (cells_bytes [C8 ?w]))) with 8 in Hr.
+ apply N1. cbn in Hr. exact Hr.
+ apply N2. cbn in Hr. exact Hr.
+ apply N3. cbn in Hr. exact Hr.
Qed.

Lemma wr_at_sub_aj : forall segs m A N a n, wr_at segs m A N -> A <= a -> a + n <= A + N -> wr_at segs m a n.
Proof.
intros segs m A N a n (W0 & W1 & HW) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
replace (a + i) with (A + (a - A + i)) by lia. apply HW. lia.
Qed.

Lemma aj_slack : forall s LB m b, RHEAP s LB m -> In b LB ->
exists junk, bytes_at rsegs m (blk_addr b + blk_size b) junk /\ Z.of_nat (length junk) = (16 - blk_size b mod 16) mod 16.
Proof.
intros s LB m b0 RH Hin0.
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hin0) as (R1 & R2 & R3 & R4 & R5).
destruct RH as (st & LBp & HPp & Hst & MR & [_ AR]).
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (INp : In b0 LBp) by (eapply Permutation_in; [apply Permutation_sym; exact HPp| exact Hin0]).
destruct (rblock_inside st LBp m b0 MF MR INp) as (r & g & idx & Hr & Hk & _ & LO & HI & _ & _ & _ & IMG).
destruct MR as (WF & _ & _ & _ & _ & SH). destruct (SH _ _ Hr Hk) as [W _].
destruct WF as (_ & WF2 & _). pose proof (WF2 _ _ Hr) as (_ & AL & _).
pose proof (QoCS.round_up_pg_mod (r_len r)) as RM. unfold PGSZ in RM.
set (k := (16 - blk_size b0 mod 16) mod 16).
assert (Hk16 : 0 <= k < 16) by (subst k; apply Z.mod_pos_bound; lia).
assert (FIT : blk_addr b0 + blk_size b0 + k <= r_base r + round_up_pg (r_len r)).
{ subst k. pose proof (Z_div_mod_eq_full (blk_addr b0) 16). pose proof (Z_div_mod_eq_full (blk_size b0) 16). pose proof (Z.mod_pos_bound (blk_size b0) 16 ltac:(lia)).
pose proof (Z_div_mod_eq_full (r_base r) 4096). pose proof (Z_div_mod_eq_full (round_up_pg (r_len r)) 4096).
destruct (Z.eq_dec (blk_size b0 mod 16) 0) as [E|NE].
- rewrite E. change ((16 - 0) mod 16) with 0. lia.
- rewrite Z.mod_small by lia. nia. }
destruct (rwr_at_bytes_exist m (blk_addr b0 + blk_size b0) k) as (bs & Hlen & Hbs).
- eapply wr_at_sub_aj; [exact W| lia| lia].
- lia.
- lia.
- exists bs. split; [exact Hbs|]. rewrite Hlen. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Theorem aj_laws : mng_laws rsegs S_AJ.
Proof.
constructor.
- exact aj_malloc.
- exact aj_free.
- exact aj_hinv.
- exact aj_agree.
- exact aj_agree_blk.
- exact aj_agree_rt.
- exact RHEAP_blocks_nodup_proof.
- exact RHEAP_blocks_disjoint_proof.
- intros s LB m a RH Ha. exact (aj_ctx_wr s LB m a RH Ha).
- intros m m' B [_ HB] _. split; [exact (rauxv_ok_I _ _ I)| exact HB].
- intros m B [_ HB]. exact HB.
- intros m m' B [_ HB]. split; [exact (rauxv_ok_I _ _ I)| exact HB].
- cbn. unfold AJ_DATA_LO, AJ_IMG_HI. lia.
- unfold mg_wstat. cbn [S_AJ mg_rstat mg_ctx mg_tp mg_data_lo mg_img_hi aj_rstat app].
unfold RCTX, RMLOCK, RVMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RATP, AJ_DATA_LO, AJ_IMG_HI.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- cbn. lia.
- exact aj_slack.
Qed.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnB.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlbW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlbW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnB.Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition aju_rstat : list (Z * Z) :=
[(RCTX, RCTX + 928); (RMLOCK, RMLOCK + 4); (RVMLOCK, RVMLOCK + 4); (RNEED_LOCKS, RNEED_LOCKS + 1); (RPAGE_SIZE, RPAGE_SIZE + 8);
(RGOT_SSP, RGOT_SSP + 8); (RSSP_GUARD, RSSP_GUARD + 8)].

Definition AJU_DATA_LO : Z := 0xe4000.
Definition AJU_IMG_HI : Z := 0x647000.
Definition S_AJU : mng_sig :=
MSIG RHEAP (fun m B => rauxv_ok m B /\ alloc_ceiling <= B) RATP rmalloc_entry RFREE_SYM 8192

0x10000 AJU_DATA_LO AJU_IMG_HI (RCTX, RCTX + 928) aju_rstat ref_reserved
[(RPAGE_SIZE, cells_bytes [C8 (wz 4096)]); (RGOT_SSP, cells_bytes [C8 (wz RSSP_GUARD)]); (RSSP_GUARD, cells_bytes [C8 rc_canary])].

Lemma wstat_static : forall a, in_ivs (mg_wstat S_AJU) a <-> ralloc_static a.
Proof.
intros a. unfold in_ivs, mg_wstat, ralloc_static. cbn [S_AJU mg_ctx mg_tp]. split.
- intros (iv & [<-|[<-|[]]] & Hr); cbn [fst snd] in Hr; [left | right]; unfold RATP, RERRNO, RCTX in *; lia.
- intros [Hr|Hr]; [exists (RCTX, RCTX + 928) | exists (RATP + -164, RATP + -164 + 4)];
(split; [cbn; auto | cbn [fst snd]; unfold RATP, RERRNO, RCTX in *; lia]).
Qed.

Lemma mclient_r : forall LB SP a, mclient S_AJU LB SP a <-> rclient_addr LB SP a.
Proof.
intros LB SP a. unfold mclient, rclient_addr. cbn [S_AJU mg_data_lo mg_img_hi]. rewrite wstat_static. reflexivity.
Qed.

Lemma mpres_r : forall LB SP m m', rheap_pres LB SP m m' -> mpres usegs S_AJU LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc. apply H; [exact Ha| apply mclient_r; exact Hc]. Qed.

Lemma mrange_r : forall A n, rblock_range A n -> mrange S_AJU A n.
Proof. intros A n H. exact H. Qed.

Lemma aju_malloc : mmalloc_stmt usegs S_AJU.
Proof.
unfold mmalloc_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB n lo B errv RH [AUX HB] Hsp STK Hlo Hlo2 ERR MI Etp Ea0 Hn.
cbn [S_AJU mg_heap mg_tp mg_stack mg_malloc] in *.
eapply implM_mono.
- exact (rmalloc_impl_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB n lo B errv RH AUX Hsp STK Hlo Hlo2 ERR MI Etp Ea0 Hn).
- intros r s' ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
E & MI' & STK' & ERR' & AUX' & PRES & _ & _ & CASE).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
split; [exact E|]. split; [exact MI'|]. split; [exact STK'|]. split; [exact ERR'|].
split; [split; [exact AUX'| exact HB]|]. split; [apply mpres_r; exact PRES|].
destruct r as [p|].
+ destruct CASE as (A & junk & Ea & RNG & RH' & CELLS & _). exists A, junk.
split; [exact Ea|]. split; [apply mrange_r; exact RNG|]. split; [exact RH'| exact CELLS].
+ exact CASE.
Qed.

Lemma aju_free : mfree_stmt usegs S_AJU.
Proof.
unfold mfree_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB p A n lo B errv RH Hin [AUX HB] Hsp STK Hlo Hlo2 ERR MI Etp Ea0.
cbn [S_AJU mg_heap mg_tp mg_stack mg_free] in *.
eapply implM_mono.
- exact (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m s LB p A n lo B errv RH Hin AUX Hsp STK Hlo Hlo2 ERR MI Etp Ea0).
- intros r s' ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
E & MI' & STK' & ERR' & AUX' & PRES & _ & _ & RH').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [exact E|]. split; [exact MI'|]. split; [exact STK'|]. split; [exact ERR'|].
split; [split; [exact AUX'| exact HB]|]. split; [apply mpres_r; exact PRES| exact RH'].
Qed.

Lemma aju_hinv : forall s LB m, RHEAP s LB m ->
exists st LBa, Permutation LBa LB /\ strip st = ps_m s /\ HINV_from ref_reserved rc_secret st (ps_brk s) LBa.
Proof. intros s LB m (st & LB0 & HP & Es & _ & HI). exists st, LB0. auto. Qed.

Lemma aju_ctx_wr : forall s LB m a, RHEAP s LB m -> RCTX <= a < RCTX + 928 -> wview usegs m (wa a) <> None.
Proof.
intros s LB m a (st & LB0 & _ & _ & MR & _) Ha. destruct MR as (_ & CX & _). destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & _).
assert (W : forall A n, wr_at usegs m A n -> A <= a < A + n -> wview usegs m (wa a) <> None).
{ intros A n (_ & _ & H) Hr. replace a with (A + (a - A)) by lia. apply H. lia. }
destruct (Z.lt_ge_cases a (RCTX + 80)) as [L1|L1].
{ apply (W RCTX 80); [apply (rw_cells_wr_at usegs m RCTX (ctx_head_cells st) 80 C1); cbn; lia | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 464)) as [L2|L2].
{ apply (W (RCTX + 80) 384); [destruct C2 as [_ Hw]; rewrite actives_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 848)) as [L3|L3].
{ apply (W (RCTX + 464) 384); [destruct C3 as [_ Hw]; rewrite usages_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 880)) as [L4|L4].
{ apply (W (RCTX + 848) 32); [destruct C4 as [_ Hw]; rewrite unmap_seqs_length in Hw; exact Hw | lia]. }
destruct (Z.lt_ge_cases a (RCTX + 912)) as [L5|L5].
{ apply (W (RCTX + 880) 32); [destruct C5 as [_ Hw]; rewrite bouncess_length in Hw; exact Hw | lia]. }
apply (W (RCTX + 912) 16); [apply (rw_cells_wr_at usegs m (RCTX + 912) (ctx_tail_cells st) 16 C6); cbn; lia | lia].
Qed.

Lemma region_dyn : forall st Lg BL LS rid r a,
INVL x0 st Lg BL LS -> (forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a.
Proof.
intros st Lg BL LS rid r a (IR & _) HPG Hr Ha.
assert (Hel : In (rid, r) (map_to_list (s_regions st))) by (apply list_elem_of_In, elem_of_map_to_list; exact Hr).
destruct (ir_shape _ _ _ IR rid r Hr) as (_ & _ & Hlen & _).
unfold lr_lo in Ha. destruct (r_kind r) eqn:K.
-  right. exists (r_base r + PGSZ, round_up_pg (r_len r) - PGSZ). split.
+ unfold doranges. apply in_or_app. right.
assert (E : ld_brkreg Lg = Some (r_base r, r_len r)) by (apply (ir_brkreg _ _ _ IR); exists rid, r; auto).
rewrite E. left. reflexivity.
+ cbn [fst snd]. unfold PGSZ. lia.
-  right. exists (r_base r, round_up_pg (r_len r)). split.
+ unfold doranges. apply in_or_app. left.
pose proof (ir_metas _ _ _ IR) as PM.
assert (Hm : In (r_base r, r_len r, frontier st rid r / PGSZ - 1) (ld_metas Lg)).
{ eapply Permutation_in; [apply Permutation_sym; exact PM|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [exact Hel| cbn [snd]; rewrite K; reflexivity]. }
apply in_map_iff. exists (r_base r, r_len r, frontier st rid r / PGSZ - 1). split; [reflexivity| exact Hm].
+ cbn [fst snd]. lia.
-  left. exists (r_base r), (r_len r).
pose proof (ir_groups _ _ _ IR) as PG.
assert (Hg : In (r_base r, r_len r) (ld_groups Lg)).
{ eapply Permutation_in; [apply Permutation_sym; exact PG|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [exact Hel| cbn [snd]; rewrite K; reflexivity]. }
split; [exact Hg|]. pose proof (HPG _ _ Hg) as Hmod.
assert (E : round_up_pg (r_len r) = r_len r).
{ unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
rewrite (Z.mod_opp_l_z (r_len r) 4096) by lia. lia. }
rewrite E in Ha. lia.
Qed.

Lemma aju_agree : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aju_rstat a \/ mng_dyn Lg a -> m' (wa a) = m (wa a)) -> RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aju_rstat -> lo <= a < hi -> in_ivs aju_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
eapply rmrep_transport_agree'; [exact MR|]. intros a Ha HF. apply AG; [exact Ha|].
destruct HF as [[C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C].
- left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
- left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
- left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
- left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
- left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
- right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
- right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
- right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
- left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
- left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- right. destruct C as (rid & r & Hr & K & Hin). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
Qed.

Lemma rrepfoot_not_block : forall st LB0 m b a, rmrep st m -> AREACH_from ref_reserved rc_secret st LB0 -> In b LB0 ->
blk_addr b <= a < blk_addr b + blk_size b -> ~ rrepfoot st a.
Proof.
intros st LB0 m b a MR AR INb Hab RF.
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4'. lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
- destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
+ rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
+ pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
- destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
- unfold RGOT_SSP in R8. lia.
- unfold RSSP_GUARD in R9. lia.
Qed.

Lemma aju_agree_blk : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aju_rstat a \/ mng_dyn Lg a -> ~ in_block LB a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None) ->
RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG WV.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aju_rstat -> lo <= a < hi -> in_ivs aju_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
eapply rmrep_transport_agree; [exact MR| |].
- intros a Ha HF.
assert (NB : ~ in_block LB a).
{ intros (b & Hb & Hr). apply (rrepfoot_not_block st LB0 m b a MR (proj2 HI)); [| exact Hr| exact HF].
eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]. }
apply AG; [exact Ha| | exact NB].
destruct HF as [C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
+ left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
+ left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
+ left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
+ left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
+ right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
+ right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
+ right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
+ left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
+ left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- intros a Ha (rid & r & Hr & K & Hin). apply (WV a Ha). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
Qed.

Lemma rmrep_transport_rt : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) -> ~ (RGOT_SSP <= a < RGOT_SSP + 8) -> ~ (RSSP_GUARD <= a < RSSP_GUARD + 8) -> m' (wa a) = m (wa a)) ->
bytes_at usegs m' RPAGE_SIZE (cells_bytes [C8 (wz 4096)]) ->
bytes_at usegs m' RGOT_SSP (cells_bytes [C8 (wz RSSP_GUARD)]) ->
bytes_at usegs m' RSSP_GUARD (cells_bytes [C8 rc_canary]) ->
wr_at usegs m' RPAGE_SIZE 8 -> wr_at usegs m' RGOT_SSP 8 -> wr_at usegs m' RSSP_GUARD 8 ->
(forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None) ->
rmrep st m'.
Proof.
intros st m m' (WF & CX & GL & AR & GR & SH) AG B3 B4 B5 W3 W4 W5 WG.
pose proof WF as (Hres & WR & DJ & WA & WGr).
assert (TC : forall A cs, rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)) ->
rw_cells usegs m' A cs).
{ intros A cs H HP HN. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha.
destruct (HN a Ha) as (N1 & N2 & N3). apply AG; [lia| apply HP; exact Ha| exact N1| exact N2| exact N3]. }
assert (RT : forall A cs, rw_cells usegs m A cs -> bytes_at usegs m' A (cells_bytes cs) -> wr_at usegs m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs).
{ intros A cs [[Wf _] _] Hb Hw. split; [split; [exact Wf| exact Hb]| exact Hw]. }
assert (AG' : forall a, 0 <= a < 2^64 -> rrepfoot st a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8) -> m' (wa a) = m (wa a)).
{ intros a Ha Hf (N1 & N2 & N3). exact (AG a Ha Hf N1 N2 N3). }
assert (OFFIMG : forall a, a < 0x10000 \/ 0x647000 <= a ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Ha. unfold RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. lia. }
assert (INCTX : forall a, RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RNEED_LOCKS <= a < RNEED_LOCKS + 1 \/ RVMLOCK <= a < RVMLOCK + 4 ->
~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Ha. unfold RCTX, RMLOCK, RNEED_LOCKS, RVMLOCK, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. lia. }

assert (DYNOFF : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> a < 0x10000 \/ 0x647000 <= a).
{ intros rid r a Hr Ha. destruct (WR rid r Hr) as (R0 & _ & _ & _ & RF). pose proof (rreserved_disjoint1 _ _ RF) as D.
pose proof (lr_lo_ge r). lia. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
pose proof (u64arr_bound usegs m _ _ C2) as Bd2. pose proof (u64arr_bound usegs m _ _ C3) as Bd3.
pose proof (u8arr_bound usegs m _ _ C4) as Bd4. pose proof (u8arr_bound usegs m _ _ C5) as Bd5.
rewrite actives_length in Bd2. rewrite usages_length in Bd3. rewrite unmap_seqs_length in Bd4. rewrite bouncess_length in Bd5.
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ apply TC; [exact C1 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_ctx| apply INCTX; left]; unfold RCTX in *; lia.
+ eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG'; [unfold RCTX in *; lia| apply rrepfoot_ctx; unfold RCTX in *; lia| apply INCTX; left; unfold RCTX in *; lia].
+ apply TC; [exact C6 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_ctx| apply INCTX; left]; unfold RCTX in *; lia.
+ exact C7.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_mlock| apply INCTX; right; left]; unfold RMLOCK in *; lia.
+ apply TC; [exact G2 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_nl| apply INCTX; right; right; left]; unfold RNEED_LOCKS in *; lia.
+ exact (RT _ _ G3 B3 W3).
+ exact (RT _ _ G4 B4 W4).
+ exact (RT _ _ G5 B5 W5).
+ apply TC; [exact G6 | |]; intros a Ha; cbn in Ha; [apply rrepfoot_vmlock| apply INCTX; right; right; right]; unfold RVMLOCK in *; lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3). destruct (WA ak ar Ha) as (ra & Hra & _).
assert (OFF : forall a, conc st ak <= a < conc st ak + 4096 -> ~ (RPAGE_SIZE <= a < RPAGE_SIZE + 8) /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) /\ ~ (RSSP_GUARD <= a < RSSP_GUARD + 8)).
{ intros a Hr. apply OFFIMG. exact (DYNOFF (fst ak) ra a Hra (rarea_in_live st ak ar ra a WF Ha Hra Hr)). }
split; [|split].
+ apply TC; [exact A1 | |]; intros a H; cbn in H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk | |]; unfold meta_cells; cbn [cells_size csize Nat.add length];
unfold AREA_HDR, META_SIZE, NSLOTS in *; intros a H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
+ apply TC; [exact A3 | |]; intros a H; cbn in H; [eapply rrepfoot_area; [exact Ha|lia]| apply OFF; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. destruct (WGr b gh Hb) as (rb & Hrb & _).
apply TC; [exact R | |]; intros a H; cbn in H; [eapply rrepfoot_group; [exact Hb|lia]|].
apply OFFIMG. apply (DYNOFF (fst b) rb a Hrb). apply (rgroup_in_live st b gh rb a WF Hb Hrb). lia.
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
split.
+ destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG'; [lia| |].
* eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
* apply OFFIMG. apply (DYNOFF rid r a Hr). rewrite (lr_lo_group r Hk). lia.
Qed.

Lemma aju_agree_rt : forall s Lg LB m m', RHEAP s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs aju_rstat a \/ mng_dyn Lg a -> ~ in_block LB a ->
~ (exists c, In c (mg_rtc S_AJU) /\ fst c <= a < fst c + Z.of_nat (length (snd c))) -> m' (wa a) = m (wa a)) ->
Forall (fun c => bytes_at usegs m' (fst c) (snd c) /\ wr_at usegs m' (fst c) (Z.of_nat (length (snd c)))) (mg_rtc S_AJU) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None) ->
RHEAP s LB m'.
Proof.
intros s Lg LB m m' (st & LB0 & HP & Es & MR & HI) (st' & BL & LS & LB1 & _ & Es' & INV' & _) HPG AG RTC WM.
exists st, LB0. split; [exact HP|]. split; [exact Es|]. split; [| exact HI].
assert (ER : s_regions st = s_regions st').
{ change (s_regions (strip st) = s_regions (strip st')). rewrite Es, Es'. reflexivity. }
pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & WG).
assert (DYN : forall rid r a, (s_regions st) !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) -> mng_dyn Lg a).
{ intros rid r a Hr Ha. rewrite ER in Hr. exact (region_dyn st' Lg BL LS rid r a INV' HPG Hr Ha). }
assert (ST : forall a lo hi, In (lo, hi) aju_rstat -> lo <= a < hi -> in_ivs aju_rstat a).
{ intros a lo hi Hin Hr. exists (lo, hi). split; [exact Hin| exact Hr]. }
cbn [S_AJU mg_rtc] in RTC, AG. inversion RTC as [|c1 l1 [B3 W3] RTC1]; subst. inversion RTC1 as [|c2 l2 [B4 W4] RTC2]; subst. inversion RTC2 as [|c3 l3 [B5 W5] _]; subst.
cbn [fst snd] in B3, B4, B5, W3, W4, W5.
eapply rmrep_transport_rt; [exact MR| | exact B3| exact B4| exact B5| exact W3| exact W4| exact W5|].
2: { intros a Ha (rid & r & Hr & K & Hin). apply (WM a Ha). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin. }
intros a Ha HF N1 N2 N3.
assert (NB : ~ in_block LB a).
{ intros (b & Hb & Hr). apply (rrepfoot_not_block st LB0 m b a MR (proj2 HI)); [| exact Hr| exact HF].
eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]. }
apply AG; [exact Ha| | exact NB|].
- destruct HF as [C|[[C|C]|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ left. apply (ST a RCTX (RCTX + 928)); [cbn; auto| exact C].
+ left. apply (ST a RMLOCK (RMLOCK + 4)); [cbn; auto| exact C].
+ left. apply (ST a RVMLOCK (RVMLOCK + 4)); [cbn; auto 6| unfold RVMLOCK; exact C].
+ left. apply (ST a RNEED_LOCKS (RNEED_LOCKS + 1)); [cbn; auto 6| exact C].
+ left. apply (ST a RPAGE_SIZE (RPAGE_SIZE + 8)); [cbn; auto 8| exact C].
+ right. destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (r & Hr & _).
exact (DYN (fst ak) r a Hr (rarea_in_live st ak ar r a WF Hak Hr Hin)).
+ right. destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (r & Hr & _).
exact (DYN (fst b) r a Hr (rgroup_in_live st b gh r a WF Hb Hr Hin)).
+ right. destruct C as (rid & r & v & Hr & K & Hin & _). apply (DYN rid r a Hr). rewrite (lr_lo_group r K). exact Hin.
+ left. apply (ST a RGOT_SSP (RGOT_SSP + 8)); [cbn; auto 10| exact C].
+ left. apply (ST a RSSP_GUARD (RSSP_GUARD + 8)); [cbn; auto 10| exact C].
- intros (c & [<-|[<-|[<-|[]]]] & Hr); cbn [fst snd] in Hr; change (Z.of_nat (length (cells_bytes [C8 ?w]))) with 8 in Hr.
+ apply N1. cbn in Hr. exact Hr.
+ apply N2. cbn in Hr. exact Hr.
+ apply N3. cbn in Hr. exact Hr.
Qed.

Lemma wr_at_sub_aj : forall segs m A N a n, wr_at segs m A N -> A <= a -> a + n <= A + N -> wr_at segs m a n.
Proof.
intros segs m A N a n (W0 & W1 & HW) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
replace (a + i) with (A + (a - A + i)) by lia. apply HW. lia.
Qed.

Lemma aju_slack : forall s LB m b, RHEAP s LB m -> In b LB ->
exists junk, bytes_at usegs m (blk_addr b + blk_size b) junk /\ Z.of_nat (length junk) = (16 - blk_size b mod 16) mod 16.
Proof.
intros s LB m b0 RH Hin0.
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hin0) as (R1 & R2 & R3 & R4 & R5).
destruct RH as (st & LBp & HPp & Hst & MR & [_ AR]).
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (INp : In b0 LBp) by (eapply Permutation_in; [apply Permutation_sym; exact HPp| exact Hin0]).
destruct (rblock_inside st LBp m b0 MF MR INp) as (r & g & idx & Hr & Hk & _ & LO & HI & _ & _ & _ & IMG).
destruct MR as (WF & _ & _ & _ & _ & SH). destruct (SH _ _ Hr Hk) as [W _].
destruct WF as (_ & WF2 & _). pose proof (WF2 _ _ Hr) as (_ & AL & _).
pose proof (QoCS.round_up_pg_mod (r_len r)) as RM. unfold PGSZ in RM.
set (k := (16 - blk_size b0 mod 16) mod 16).
assert (Hk16 : 0 <= k < 16) by (subst k; apply Z.mod_pos_bound; lia).
assert (FIT : blk_addr b0 + blk_size b0 + k <= r_base r + round_up_pg (r_len r)).
{ subst k. pose proof (Z_div_mod_eq_full (blk_addr b0) 16). pose proof (Z_div_mod_eq_full (blk_size b0) 16). pose proof (Z.mod_pos_bound (blk_size b0) 16 ltac:(lia)).
pose proof (Z_div_mod_eq_full (r_base r) 4096). pose proof (Z_div_mod_eq_full (round_up_pg (r_len r)) 4096).
destruct (Z.eq_dec (blk_size b0 mod 16) 0) as [E|NE].
- rewrite E. change ((16 - 0) mod 16) with 0. lia.
- rewrite Z.mod_small by lia. nia. }
destruct (rwr_at_bytes_exist m (blk_addr b0 + blk_size b0) k) as (bs & Hlen & Hbs).
- eapply wr_at_sub_aj; [exact W| lia| lia].
- lia.
- lia.
- exists bs. split; [exact Hbs|]. rewrite Hlen. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Theorem aju_laws : mng_laws usegs S_AJU.
Proof.
constructor.
- exact aju_malloc.
- exact aju_free.
- exact aju_hinv.
- exact aju_agree.
- exact aju_agree_blk.
- exact aju_agree_rt.
- exact RHEAP_blocks_nodup_proof.
- exact RHEAP_blocks_disjoint_proof.
- intros s LB m a RH Ha. exact (aju_ctx_wr s LB m a RH Ha).
- intros m m' B [_ HB] _. split; [exact (rauxv_ok_I _ _ I)| exact HB].
- intros m B [_ HB]. exact HB.
- intros m m' B [_ HB]. split; [exact (rauxv_ok_I _ _ I)| exact HB].
- cbn. unfold AJU_DATA_LO, AJU_IMG_HI. lia.
- unfold mg_wstat. cbn [S_AJU mg_rstat mg_ctx mg_tp mg_data_lo mg_img_hi aju_rstat app].
unfold RCTX, RMLOCK, RVMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RATP, AJU_DATA_LO, AJU_IMG_HI.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- cbn. lia.
- exact aju_slack.
Qed.
End RC__1.
