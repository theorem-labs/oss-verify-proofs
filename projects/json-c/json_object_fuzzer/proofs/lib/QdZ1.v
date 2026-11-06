(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QTp6 Q2qa QytA Q4J3 QJE4 QZAi QUZl Q7S0 QCwx QFqQ Q98Z QkLq Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rbytes_at_zeros_sub m A n off k :
bytes_at rsegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at rsegs m (A + off) (zeros k).
Proof.
intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

#[using="Type"] Lemma rrw_cells_of_zeros m A n off cs :
bytes_at rsegs m A (zeros n) -> wr_at rsegs m A (Z.of_nat n) ->
cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
rw_cells rsegs m (A + off) cs.
Proof.
intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
- rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
- eapply wr_at_sub; [exact HW| lia| lia].
Qed.

#[using="Type"] Lemma rmrep_set_area_next : forall st m m' a ar p,
rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono rsegs m m' ->
rw_cells rsegs m' (conc st a) [C8 (wz (a_check ar)); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof.
intros st m m' a ar p MR Ha Hp MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
assert (AG : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
split; [|split; [|split; [|split; [|split]]]].
-  split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
-  destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
change (ctx_tail_cells st') with (ctx_tail_cells st).
split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [apply AG; [exact C6| cbn; unfold RCTX; lia]|]. exact C7.
-  destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. split; [apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia]|]. apply AG; [exact G6| cbn; unfold RVMLOCK; lia].
-  intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
* apply AG; [exact A3| cbn; lia].
+ rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
- rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. lia.
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
change (pw st' (a_next ar')) with (pw st (a_next ar')).
split; [apply AG; [exact A1| cbn; lia]|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
* apply AG; [exact A3| cbn; lia].
-  intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
-  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
+ eapply wr_at_transport; [exact HWr| exact WM].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); unfold alloc_ceiling in RC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

#[using="Type"] Lemma rmrep_new_area : forall st m (p : aptr) r chk,
rmrep st m -> (s_areas st) !! p = None ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
rw_cells rsegs m (conc st p) [C8 (wz chk); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
(forall k, 0 <= k < NSLOTS -> rw_cells rsegs m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
rw_cells rsegs m (conc st p + 4064) [CB 32 (zeros 32)] ->
rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof.
intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
+ exists r. repeat split; assumption.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
- exact CX.
- exact GL.
- intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
destruct (decide (a' = p)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
split; [exact HDR|]. split; [| exact PAD].
intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
- exact GR.
- exact SH.
Qed.

#[using="Type"] Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None ->
conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof.
intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
+ rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
assert (NEo : snd ak <> snd p).
{ intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
Z.div_mod_to_equations. lia.
+ pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Qy5Y QlQE QPjm QFkE Ql2m QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq4 QlQE Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QFkE.
Export QJE4.Mq2.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
- right; left. exact H.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
exists rid, r, w. auto.
Qed.

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [|split; [|split]].
+ intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
+ intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
+ intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
+ intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
- unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
- exact GL.
- intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
- intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
- intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

#[using="Type"] Lemma rptrs_in_norid st2 LB c rid r m :
KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
(s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
(forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
ci_mptrs st2 ->
ptrs_in (fun x => x <> rid) st2.
Proof.
intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
{ intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
{ intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
- apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
- apply NGr. exact M1.
- apply NGr. exact M2.
- apply NGr. exact M3.
- apply NGr. exact M4.
- intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
- destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
- intros g. split; [| split].
+ apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
+ apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
+ destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
- intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b gh Hb. split; [exact (NOG b gh Hb)|].
destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End RC__1.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl rsegs mX) as WMq end.

Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
rmrep st' m -> mem_inv rsegs m ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono rsegs m0 m ->
ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce328) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rntf_frame in *. subst s1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
finish.
Qed.

#[using="Type"] Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
s1 = Z_to_bv 64 RSSP_GUARD ->
0 <= m_freed (get_meta_rec st g) < 2^32 ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce300) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
unfold alloc_ceiling, NSLOTS in *.
assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
set (mr := get_meta_rec st g) in *.
pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
{ apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
subst a1.
st1. rewrite sx32_wz_sxv by lia. st1.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep (aor_st st g i) mX) end.
{ unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
- reflexivity.
- cbn. tauto. }
clear MUg MM.

st1. st1.
eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.

#[using="Type"] Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
rw_cells rsegs m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
rw_cells rsegs m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof.
intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
eapply rw_cells_congr; [| | | exact H].
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
- reflexivity.
- split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

#[using="Type"] Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce264) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.
rmeta_chunk MR MSL CH.

pose proof MR as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRf : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.

rmeta_open (conc st g) MUg WMg.
st1. st1.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
assert (CH' : rw_cells rsegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
clear CH; rename CH' into CH
end end.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
assert (CH' : rw_cells rsegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear CH; rename CH' into CH
end end.
rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
set (st0 := put_meta g meta0 st) in MR0.
assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).

rmeta_chunk MR0 MSL0 CH0.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
clear CH0 K1 K2.

st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
-
destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).

rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1.
clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH.
st1.
rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).

munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
st1. clear CH.

rmeta_open (conc st head) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
rewrite get_meta_rec_put_same.
rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
-
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1. st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.

clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1. rewrite FMH in C1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
{ eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
Qed.

End RC__2.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq.
Export QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QCwx.Mq1 QFqQ.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_wr32 : forall st m p v r,
rmrep st m -> ticks_ok st ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 4 <= round_up_pg (r_len r) ->
(forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 4 <= snd b \/ snd b + 9 <= snd p) ->
0 <= v < 2^32 ->
rmrep (wr32 p v st) (write_to_mem m (wa (r_base r + snd p)) (le4 (wz v)))
/\ ticks_ok (wr32 p v st).
Proof.
intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
rewrite le4_bytes by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
(wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
(wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
rewrite !wa_succ.
unfold wr32.
assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
{ split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S1 as [M1 T1].
assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
/\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
{ split; [|apply ticks_ok_wr8; exact T1].
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S2 as [M2 T2].
assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
(write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
/\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
{ split; [|apply ticks_ok_wr8; exact T2].
replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S3 as [M3 T3].
split; [|apply ticks_ok_wr8; exact T3].
replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

#[using="Type"] Lemma rrdv_mem : forall st stx m (q : aptr) r (x : byte),
rmrep st m -> get_shadow stx (fst q) = get_shadow st (fst q) -> (forall q', conc stx q' = conc st q') ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
bytes_at rsegs m (r_base r + snd q) [x] ->
rdv pans_mem m stx q = bv_unsigned x.
Proof.
intros st stx m q r x MR Hsh Hconc Hr Hk Ho Hb.
unfold rdv. rewrite Hsh. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs m _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite Hconc, (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *.
destruct (m (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rauxv_ok_pres : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

#[using="Type"] Lemma rpres_write : forall (C : Z -> Prop) m0 m a bs,
rpres_except C m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall x, a <= x < a + Z.of_nat (length bs) -> C x) ->
rpres_except C m0 (write_to_mem m (wa a) bs).
Proof.
intros C m0 m a bs HP Ha Hl HC x Hx HCx.
destruct (HP x Hx HCx) as [E W].
assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
{ rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply HCx, HC. lia. }
split.
- rewrite NE. exact E.
- intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

#[using="Type"] Lemma rpres_except_munch_frame : forall C m0 m m' W,
rpres_except C m0 m -> munch W m m' -> wmono rsegs m m' ->
(forall x, 0 <= x < 2^64 -> ~ C x -> outside W x) -> rpres_except C m0 m'.
Proof.
intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q4J3.Mq3 QPjm.Mq4.
Import QW7x.Mq0 QCwx.Mq1 QFqQ.Mq0 QkLq.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
impl rsegs (at_node rsegs) (QlEo_c1.Mq0.bind _ t f) Q ms ->
impl rsegs (at_node rsegs) t (fun r ms' => impl rsegs (at_node rsegs) (f r) Q ms') ms.
Proof.
induction t as [r|n k IH]; intros f Q ms H; cbn [QlEo_c1.Mq0.bind] in H.
- cbn. apply evt_done. exact H.
- rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
impl rsegs (at_node rsegs) (ebind t f) (epost Q) ms ->
impl rsegs (at_node rsegs) t (fun r ms' => match r with
| Ok a => impl rsegs (at_node rsegs) (f a) (epost Q) ms'
| Unr => True end) ms.
Proof.
intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_bind_inv : forall {St A B} (m : @M St A) (f : A -> @M St B) s Q ms,
implM rsegs (mbind m f) s Q ms ->
implM rsegs m s (fun a s' ms' => implM rsegs (f a) s' Q ms') ms.
Proof.
intros St A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_ret_inv : forall {St A} (a : A) (s : St) Q ms,
implM rsegs (mret a) s Q ms -> evt rsegs (Q a s) ms.
Proof. intros St A a s Q ms H. exact H. Qed.

#[using="Type"] Lemma implM_upd_inv : forall {St} (f : St -> St) s Q ms,
implM rsegs (mupd f) s Q ms -> evt rsegs (Q tt (f s)) ms.
Proof. intros St f s Q ms H. exact H. Qed.

Definition rmalloc_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM rsegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).

Definition rfree_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma rmalloc_stmt_of_impl : rmalloc_impl_stmt -> rmalloc_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
{ unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

#[using="Type"] Lemma rfree_stmt_of_impl : rfree_impl_stmt -> rfree_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
{ unfold RFREE_SYM. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

Definition cm_conv (st' : mstate) (n : Z) (p : option cptr) : option bptr :=
match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.

#[using="Type"] Lemma rmalloc_membed : rmalloc_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM rsegs (membed (cmalloc (ps_m s) n)) s
(fun x s' ms' => evt rsegs (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m
(cm_conv (fst x) n (snd x)) (set_m (fst x) s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
HEAP AUXB SB ST CLO LO ERR MI TP HA N) as X.
unfold raw_malloc in X. apply implM_bind_inv in X.

unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [exact X1|]. cbv beta.
intros [st' p] s' ms' X2. apply implM_bind_inv in X2. apply implM_upd_inv in X2.
eapply evt_cut; [exact X2|]. cbv beta. intros ms2 X3. apply implM_ret_inv in X3. exact X3.
Qed.

#[using="Type"] Lemma rfree_membed : rfree_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (membed (cfree (ps_m s) (Some (fst p)))) s
(fun st' s' ms' => evt rsegs (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m
tt (set_m st' s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0) as X.
unfold raw_free in X. apply implM_bind_inv in X.
unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [exact X1|]. cbv beta.
intros st' s' ms' X2. apply implM_upd_inv in X2. exact X2.
Qed.

End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rbytes_at_zeros_sub m A n off k :
bytes_at usegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at usegs m (A + off) (zeros k).
Proof.
intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

#[using="Type"] Lemma rrw_cells_of_zeros m A n off cs :
bytes_at usegs m A (zeros n) -> wr_at usegs m A (Z.of_nat n) ->
cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
rw_cells usegs m (A + off) cs.
Proof.
intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
- rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
- eapply wr_at_sub; [exact HW| lia| lia].
Qed.

#[using="Type"] Lemma rmrep_set_area_next : forall st m m' a ar p,
rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono usegs m m' ->
rw_cells usegs m' (conc st a) [C8 (wz (a_check ar)); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof.
intros st m m' a ar p MR Ha Hp MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
assert (AG : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells usegs m' A cs).
{ intros A cs H HD. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
split; [|split; [|split; [|split; [|split]]]].
-  split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
-  destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
change (ctx_tail_cells st') with (ctx_tail_cells st).
split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [apply AG; [exact C6| cbn; unfold RCTX; lia]|]. exact C7.
-  destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. split; [apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia]|]. apply AG; [exact G6| cbn; unfold RVMLOCK; lia].
-  intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
* apply AG; [exact A3| cbn; lia].
+ rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
- rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. lia.
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
change (pw st' (a_next ar')) with (pw st (a_next ar')).
split; [apply AG; [exact A1| cbn; lia]|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
* apply AG; [exact A3| cbn; lia].
-  intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
-  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
+ eapply wr_at_transport; [exact HWr| exact WM].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); unfold alloc_ceiling in RC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

#[using="Type"] Lemma rmrep_new_area : forall st m (p : aptr) r chk,
rmrep st m -> (s_areas st) !! p = None ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
rw_cells usegs m (conc st p) [C8 (wz chk); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
(forall k, 0 <= k < NSLOTS -> rw_cells usegs m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
rw_cells usegs m (conc st p + 4064) [CB 32 (zeros 32)] ->
rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof.
intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
+ exists r. repeat split; assumption.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
- exact CX.
- exact GL.
- intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
destruct (decide (a' = p)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
split; [exact HDR|]. split; [| exact PAD].
intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
- exact GR.
- exact SH.
Qed.

#[using="Type"] Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None ->
conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof.
intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
+ rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
assert (NEo : snd ak <> snd p).
{ intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
Z.div_mod_to_equations. lia.
+ pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq4 QlQE Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QFkE.
Export QJE4.Mq2.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
- right; left. exact H.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
exists rid, r, w. auto.
Qed.

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [|split; [|split]].
+ intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
+ intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
+ intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
+ intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
- unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
- exact GL.
- intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
- intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
- intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

#[using="Type"] Lemma rptrs_in_norid st2 LB c rid r m :
KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
(s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
(forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
ci_mptrs st2 ->
ptrs_in (fun x => x <> rid) st2.
Proof.
intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
{ intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
{ intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
- apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
- apply NGr. exact M1.
- apply NGr. exact M2.
- apply NGr. exact M3.
- apply NGr. exact M4.
- intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
- destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
- intros g. split; [| split].
+ apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
+ apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
+ destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
- intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b gh Hb. split; [exact (NOG b gh Hb)|].
destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End RC__1.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl usegs mX) as WMq end.

Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
rmrep st' m -> mem_inv usegs m ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono usegs m0 m ->
ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd09ec) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rntf_frame in *. subst s1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
finish.
Qed.

#[using="Type"] Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
s1 = Z_to_bv 64 RSSP_GUARD ->
0 <= m_freed (get_meta_rec st g) < 2^32 ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd09c4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
unfold alloc_ceiling, NSLOTS in *.
assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
set (mr := get_meta_rec st g) in *.
pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
{ apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
subst a1.
st1. rewrite sx32_wz_sxv by lia. st1.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep (aor_st st g i) mX) end.
{ unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
- reflexivity.
- cbn. tauto. }
clear MUg MM.

st1. st1.
eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.

#[using="Type"] Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
rw_cells usegs m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
rw_cells usegs m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof.
intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
eapply rw_cells_congr; [| | | exact H].
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
- reflexivity.
- split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

#[using="Type"] Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0928) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.
rmeta_chunk MR MSL CH.

pose proof MR as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRf : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.

rmeta_open (conc st g) MUg WMg.
st1. st1.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
assert (CH' : rw_cells usegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
clear CH; rename CH' into CH
end end.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
assert (CH' : rw_cells usegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear CH; rename CH' into CH
end end.
rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
set (st0 := put_meta g meta0 st) in MR0.
assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).

rmeta_chunk MR0 MSL0 CH0.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
clear CH0 K1 K2.

st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
-
destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).

rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1.
clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH.
st1.
rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).

munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
st1. clear CH.

rmeta_open (conc st head) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
rewrite get_meta_rec_put_same.
rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
-
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1. st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.

clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1. rewrite FMH in C1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
{ eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
Qed.

End RC__2.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXEH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q4J3.Mq3 QPjm.Mq4.
Import QXEH QCwx.Mq3 QFqQ.Mq1 QkLq.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
impl usegs (at_node usegs) (QlEo_c1.Mq0.bind _ t f) Q ms ->
impl usegs (at_node usegs) t (fun r ms' => impl usegs (at_node usegs) (f r) Q ms') ms.
Proof.
induction t as [r|n k IH]; intros f Q ms H; cbn [QlEo_c1.Mq0.bind] in H.
- cbn. apply evt_done. exact H.
- rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
impl usegs (at_node usegs) (ebind t f) (epost Q) ms ->
impl usegs (at_node usegs) t (fun r ms' => match r with
| Ok a => impl usegs (at_node usegs) (f a) (epost Q) ms'
| Unr => True end) ms.
Proof.
intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_bind_inv : forall {St A B} (m : @M St A) (f : A -> @M St B) s Q ms,
implM usegs (mbind m f) s Q ms ->
implM usegs m s (fun a s' ms' => implM usegs (f a) s' Q ms') ms.
Proof.
intros St A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_ret_inv : forall {St A} (a : A) (s : St) Q ms,
implM usegs (mret a) s Q ms -> evt usegs (Q a s) ms.
Proof. intros St A a s Q ms H. exact H. Qed.

#[using="Type"] Lemma implM_upd_inv : forall {St} (f : St -> St) s Q ms,
implM usegs (mupd f) s Q ms -> evt usegs (Q tt (f s)) ms.
Proof. intros St f s Q ms H. exact H. Qed.

Definition rmalloc_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM usegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).

Definition rfree_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM usegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).

#[using="Type"] Lemma rmalloc_stmt_of_impl : rmalloc_impl_stmt -> rmalloc_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))).
{ unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

#[using="Type"] Lemma rfree_stmt_of_impl : rfree_impl_stmt -> rfree_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
{ unfold RFREE_SYM. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

Definition cm_conv (st' : mstate) (n : Z) (p : option cptr) : option bptr :=
match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.

#[using="Type"] Lemma rmalloc_membed : rmalloc_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM usegs (membed (cmalloc (ps_m s) n)) s
(fun x s' ms' => evt usegs (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m
(cm_conv (fst x) n (snd x)) (set_m (fst x) s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
HEAP AUXB SB ST CLO LO ERR MI TP HA N) as X.
unfold raw_malloc in X. apply implM_bind_inv in X.

unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [exact X1|]. cbv beta.
intros [st' p] s' ms' X2. apply implM_bind_inv in X2. apply implM_upd_inv in X2.
eapply evt_cut; [exact X2|]. cbv beta. intros ms2 X3. apply implM_ret_inv in X3. exact X3.
Qed.

#[using="Type"] Lemma rfree_membed : rfree_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM usegs (membed (cfree (ps_m s) (Some (fst p)))) s
(fun st' s' ms' => evt usegs (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m
tt (set_m st' s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0) as X.
unfold raw_free in X. apply implM_bind_inv in X.
unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [exact X1|]. cbv beta.
intros st' s' ms' X2. apply implM_upd_inv in X2. exact X2.
Qed.

End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_wr32 : forall st m p v r,
rmrep st m -> ticks_ok st ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 4 <= round_up_pg (r_len r) ->
(forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 4 <= snd b \/ snd b + 9 <= snd p) ->
0 <= v < 2^32 ->
rmrep (wr32 p v st) (write_to_mem m (wa (r_base r + snd p)) (le4 (wz v)))
/\ ticks_ok (wr32 p v st).
Proof.
intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
rewrite le4_bytes by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
(wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
(wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
rewrite !wa_succ.
unfold wr32.
assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
{ split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S1 as [M1 T1].
assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
/\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
{ split; [|apply ticks_ok_wr8; exact T1].
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S2 as [M2 T2].
assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
(write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
/\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
{ split; [|apply ticks_ok_wr8; exact T2].
replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S3 as [M3 T3].
split; [|apply ticks_ok_wr8; exact T3].
replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

#[using="Type"] Lemma rrdv_mem : forall st stx m (q : aptr) r (x : byte),
rmrep st m -> get_shadow stx (fst q) = get_shadow st (fst q) -> (forall q', conc stx q' = conc st q') ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
bytes_at usegs m (r_base r + snd q) [x] ->
rdv pans_mem m stx q = bv_unsigned x.
Proof.
intros st stx m q r x MR Hsh Hconc Hr Hk Ho Hb.
unfold rdv. rewrite Hsh. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read usegs m _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite Hconc, (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *.
destruct (m (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rauxv_ok_pres : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

#[using="Type"] Lemma rpres_write : forall (C : Z -> Prop) m0 m a bs,
rpres_except C m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall x, a <= x < a + Z.of_nat (length bs) -> C x) ->
rpres_except C m0 (write_to_mem m (wa a) bs).
Proof.
intros C m0 m a bs HP Ha Hl HC x Hx HCx.
destruct (HP x Hx HCx) as [E W].
assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
{ rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply HCx, HC. lia. }
split.
- rewrite NE. exact E.
- intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

#[using="Type"] Lemma rpres_except_munch_frame : forall C m0 m m' W,
rpres_except C m0 m -> munch W m m' -> wmono usegs m m' ->
(forall x, 0 <= x < 2^64 -> ~ C x -> outside W x) -> rpres_except C m0 m'.
Proof.
intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.

End RC__1.
