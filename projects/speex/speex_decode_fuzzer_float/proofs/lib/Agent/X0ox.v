(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qe.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0qi X0qj X0pm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Module A2 := X0qe.

Lemma mrep_agree_but_ctx {RCEIL : RunCeiling} : forall st st' m m',
mrep st m ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
A2.agree_on m m' MLOCK 4 -> A2.agree_on m m' LIBC 0x68 ->
(forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
mrep_ctx st' m' ->
mrep st' m'.
Proof.
intros st st' m m' sfH_; first [ sf_destruct 6%nat sfH_ as WF CX GL AR GR SH | sf_fb; destruct sfH_ as (WF & CX & GL & AR & GR & SH) ]; intros ER EM EA EG ES ERs AGL AGC AGA AGG AGR CX'.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [exact CX'|split; [|split; [|split]]]].
- first [ sf_destruct 5%nat WF as RS WR DJ WA WG | sf_fb; destruct WF as (RS & WR & DJ & WA & WG) ]. unfold regions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
- destruct GL as (G1 & G2 & G3). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A, LIBC in *.
split; [|split].
+ eapply A2.rw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply A2.rw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply A2.rw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
- intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
unfold area_rep. rewrite !Hconc.
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
rewrite PW. split; [|split].
+ eapply A2.rw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. rewrite MC, GM. eapply A2.rw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
+ eapply A2.rw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
eapply A2.rw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
unfold shadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
+ eapply A2.wr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply A2.bytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

Lemma mrep_ctx_mid_agree {RCEIL : RunCeiling} : forall st st' m m',
mrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
/\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
s_regions st' = s_regions st ->
A2.agree_on m m' (CTX + 80) 832 ->
u64arr asegs m' (CTX + 80) (actives st') /\ u64arr asegs m' (CTX + 464) (usages st')
/\ u8arr asegs m' (CTX + 848) (unmap_seqs st') /\ u8arr asegs m' (CTX + 880) (bouncess st').
Proof.
intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
assert (E3 : usages st' = usages st).
{ unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st).
{ unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
assert (E5 : bouncess st' = bouncess st).
{ unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
rewrite E2, E3, E4, E5.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold CTX in *.
split; [|split; [|split]].
- eapply A2.u64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply A2.u64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply A2.u8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply A2.u8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

Lemma area_in_live {RCEIL : RunCeiling} : forall st a ar r x, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st a ar r x WF Ha Hr Hx. first [ pose proof (area_conc st a ar WF Ha) as sfP_; sf_destruct 6%nat sfP_ as ra Hra Ca Sa0 Sa1 _ | sf_fb; destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _) ].
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (area_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma group_in_live {RCEIL : RunCeiling} : forall st b gh r x, regions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st b gh r x WF Hb Hr Hx. first [ pose proof (group_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 _ | sf_fb; destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _) ].
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

Definition clear_range (st : mstate) (lo n : Z) : Prop :=
forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma image_clear_of_ranges_free st lo n x : s_reserved st = agent_reserved -> ranges_free (live_ranges st) lo n = true ->
0x10000 <= x < 0x1b000 -> ~ (lo <= x < lo + n).
Proof.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.

Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="Hr"] Lemma gr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma gr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma gr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
rewrite gr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="Type"] Lemma gr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite gr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma gr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite gr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="Hr"] Lemma gr_conc q : conc st' q = conc st q.
Proof.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, gr_lookup_new, Hr. reflexivity.
- rewrite gr_lookup_old by exact NE. reflexivity.
Qed.
#[using="RCEIL OFF OAL"] Lemma gr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

#[using="m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma gr_regions_wf : regions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as RS WR DJ WA WG | sf_fb; destruct sfP_ as (RS & WR & DJ & WA & WG) ].
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 RBAL RL0 RBC RFr | sf_fb; destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr) ].
assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
split; [exact RS|]. split; [|split; [|split]].
- intros q rq Hq. destruct (gr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
cbn [r_base r_len r_kind r']. rewrite gr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
apply ranges_free_intro. intros b n HI.
pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
destruct HI as [E|[E|[]]]; inversion E; subst; lia.
- intros q1 r1 q2 r2 H1 H2 NE.
assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
{ intros q rq Hq NEq. cbn [r_base r_len r']. rewrite gr_ru, RU.
replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
- left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
- right. exact D. }
destruct (gr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (gr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ exact (OLD q2 r2 H2' NE2).
+ destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. first [ pose proof (WA a ar Ha) as sfP_; sf_destruct 7%nat sfP_ as ra Hra A0 A1 AAL NKa LO | sf_fb; destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO) ].
destruct (decide (fst a = rid)) as [E|NE].
+ exists r'. rewrite E in Hra |- *. rewrite gr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
cbn [r_base r_len r_kind r']. rewrite gr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
rewrite LEN in A1. repeat split; try assumption; lia.
+ exists ra. rewrite gr_lookup_old by exact NE. repeat split; assumption.
- intros b gh Hb. first [ pose proof (WG b gh Hb) as sfP_; sf_destruct 4%nat sfP_ as rb Hrb Kb REST | sf_fb; destruct (WG b gh Hb) as (rb & Hrb & Kb & REST) ].
assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
exists rb. rewrite gr_lookup_old by exact NE. auto.
Qed.

#[using="MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma mrep_grow_region : mrep st' m.
Proof.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ].
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite gr_conc|]; reflexivity).
assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
split; [exact gr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
- first [ sf_destruct 6%nat CX as C1 C2 C3 C4 C5 C6 | sf_fb; destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]. unfold mrep_ctx.
replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
replace (ctx_tail_cells st') with (ctx_tail_cells st).
2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?gr_conc; reflexivity. }
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
- intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
unfold area_rep. rewrite !gr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
- intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
exists w8. rewrite gr_conc, PW. split; assumption.
- intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
destruct (gr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
+ exfalso. apply NK. exact Hk.
+ exact (SH q rq H Hk).
Qed.

#[using="Type"] Lemma ptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

Lemma impl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl asegs (at_node asegs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl asegs (at_node asegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
intros H HD. unfold enode in *. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.
