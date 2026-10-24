(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0s YO0u YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac o_get := match goal with |- OK4 ?P (bind get ?k ?s0) => change (OK4 P (k s0 s0)); cbv beta end.
Ltac o_put := match goal with |- OK4 ?P (bind (put ?s1) ?k ?s0) => change (OK4 P (k tt s1)); cbv beta end.
Ltac o_modify := match goal with |- OK4 ?P (bind (modify ?f) ?k ?s0) => change (OK4 P (k tt (f s0))); cbv beta end.
Ltac o_ret := match goal with |- OK4 ?P (bind (ret ?a) ?k ?s0) => change (OK4 P (k a s0)); cbv beta end.
Ltac rq_get H := match type of H with reqs_ok (bind get ?k ?s0) => change (reqs_ok (k s0 s0)) in H; cbv beta in H end.
Ltac rq_ret H := match type of H with reqs_ok (bind (ret ?a) ?k ?s0) => change (reqs_ok (k a s0)) in H; cbv beta in H end.
Ltac rq_bind H Hm Hf := pose proof (reqs_ok_mbind_inv _ _ _ H) as [Hm Hf]; clear H.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation amc s := (st_avail_meta_count s).
Lemma OK4_eq {A B} (m : M A) (K : A -> M B) s a s' P : m s = IRet (a, s') -> OK4 P (K a s') -> OK4 P (bind m K s).
Proof. intros E H. unfold bind. rewrite E. exact H. Qed.
Lemma rq_eq {A B} (m : M A) (K : A -> M B) s a s' : m s = IRet (a, s') -> reqs_ok (bind m K s) -> reqs_ok (K a s').
Proof. intros E H. unfold bind in H. rewrite E in H. exact H. Qed.
Lemma yields_eq {A} (m : M A) s a s' : m s = IRet (a, s') -> yields (m s) [] (a, s').
Proof. intros E. rewrite E. reflexivity. Qed.
Lemma find_frame_eq p s x : find_frame_in (st_metas s) p = Some x -> find_frame p s = IRet (x, s).
Proof. intros H. unfold find_frame, bind, get, ret. cbn [ibind]. rewrite H. reflexivity. Qed.
Lemma getm_eq p s am : MT s p = Some (MUsed am) -> getm p s = IRet (am, s).
Proof. intros H. unfold getm, bind, get, ret. cbn [ibind]. unfold MT in H. rewrite H. reflexivity. Qed.
Lemma setm_eq p am s : setm p am s = IRet (tt, upd_meta p (MUsed am) s).
Proof. reflexivity. Qed.
Lemma release_slot_eq g i s am fr : MT s g = Some (MUsed am) -> ss_fr (nth_slot am i) = Some fr ->
exists x, ss_fr x = None /\ release_slot g i s = IRet (tt, upd_meta g (MUsed (upd_slot am i x)) s).
Proof.
intros H Hfr. unfold release_slot, bind. rewrite (getm_eq g s am H). cbn [ibind]. cbv zeta. rewrite Hfr.
destruct (fr_off fr =? 0); (eexists; split; [|rewrite setm_eq; reflexivity]); reflexivity.
Qed.
Lemma meas_upd_meta g x s : meas (upd_meta g x s) = meas s.
Proof. reflexivity. Qed.
Lemma page_round_le_multiple x k : x <= k * PGSZ -> page_round x <= k * PGSZ.
Proof.
intros H. unfold page_round, PGSZ in *.
assert ((x + 4096 - 1) / 4096 <= k); [|nia].
apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma OK4_nf63 f g am s Q :
MT s g = Some (MUsed am) -> am_sc am = 63 -> am_last am = 0 -> am_avail am = 0 -> am_freed am = 0 ->
am_next am = None -> 1 <= am_maplen am ->
(forall s', meas s' = meas s -> Q (Some (prid (am_mem am), am_maplen am * 4096), s')) ->
OK4 Q (nontrivial_free (S f) g 0 s).
Proof.
intros Hm Hsc Hl Hav Hfr Hnx Hml HQ. cbn [nontrivial_free].
eapply OK4_eq; [apply getm_eq; exact Hm|]. o_get. cbv zeta.
match goal with |- OK4 _ ((if ?c then _ else _) _) => replace c with true end.
2:{ symmetry. rewrite Hfr, Hav, Hl. unfold okay_to_free. rewrite Hsc. cbn. reflexivity. }
rewrite Hnx. o_ret.
eapply OK4_eq; [apply getm_eq; exact Hm|]. rewrite Hsc. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont]. o_ret.
replace (negb (am_maplen am =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; lia). cbv iota.
eapply OK4_bind_y.
{ eapply OK4_bind_y; [apply (OK4_frame_meas step_seq s); auto with presK presC|].
intros u1 s1 tr1 _ E1. cbn [snd] in E1.
eapply OK4_bind_y; [apply (OK4_frame_meas (record_seq 63) s1); auto with presK presC|].
intros u2 s2 tr2 _ E2. cbn [snd] in E2. apply (OK4_ret _ _ (fun x => fst x = Some (prid (am_mem am), am_maplen am * 4096) /\ meas (snd x) = meas s)).
cbn [fst snd]. split; [reflexivity | rewrite E2; exact E1]. }
intros mi s3 tr3 _ [Hmi E3]. cbn [fst snd] in Hmi, E3. subst mi.
eapply OK4_bind_y; [apply (OK4_frame_meas (free_meta g) s3); auto with presK presC|].
intros u4 s4 tr4 _ E4. cbn [snd] in E4. apply OK4_ret. apply HQ. rewrite E4. exact E3.
Qed.
Theorem free_credit s p n : WF s -> II s -> In (p, n) (user_blocks s) -> MMAP_THRESHOLD < n ->
OK4 (fun x => map_bytes (snd x) <= map_bytes s - page_round (n + IB + UNIT) /\ map_count (snd x) <= map_count s - 1)
(free (Some p) s).
Proof.
intros HW HII Hin Hn. pose proof (free_reqs_ok s p n HW Hin) as RQ.
destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & Hnn & ->).
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
pose proof (inv_groups HW g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & Hfo & _).
destruct Hfo as (Fn & Foff & Fle & _).
pose proof (class_size_bound (am_sc am)) as Hcs.
assert (C63 : am_sc am = 63 /\ am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0).
{ destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & _) | (Csc & _ & _ & _)]; [repeat split; assumption|]. exfalso.
unfold stride_of in Fle. destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1.
assert (Hml : 0 < am_maplen am) by (destruct (am_maplen am =? 0) eqn:E3; [discriminate|]; apply Z.eqb_neq in E3; lia).
destruct (Gmp Hml) as (r & rg & _ & _ & _ & _ & _ & _ & Hsmall). specialize (Hsmall E1 ltac:(lia)).
pose proof (page_round_le_multiple (class_size (am_sc am) + UNIT) 32 ltac:(unfold UNIT, PGSZ; lia)).
unfold MMAP_THRESHOLD, UNIT, IB, PGSZ in *. lia.
- unfold MMAP_THRESHOLD, UNIT, IB in *. lia. }
destruct C63 as (Csc & Cl0 & Cml & Cav & Cfr). assert (idx = 0) as -> by lia.
destruct (Gmp ltac:(lia)) as (r & rg & Hmem & Hrg & Hkd & Hlv & Hlen & Hfit & _).
destruct (inv_rings HW) as (_ & _ & D). destruct (D g am Hu Csc) as [_ Hnx].
assert (Hcov : page_round (n + IB + UNIT) <= am_maplen am * PGSZ).
{ apply page_round_le_multiple. unfold stride_of in Fle. rewrite Cl0 in Fle.
replace (negb (am_maplen am =? 0)) with true in Fle by (symmetry; apply negb_true_iff; apply Z.eqb_neq; lia).
cbn in Fle. unfold UNIT, IB, PGSZ in *. lia. }
unfold free in RQ |- *.
pose proof (find_frame_eq _ s _ (find_frame_in_spec [] None U0 s HW g am 0 fr Hu Hi Hfr)) as FF.
eapply OK4_eq; [exact FF|]. apply (rq_eq _ _ _ _ _ FF) in RQ. cbn [fst snd] in RQ |- *. cbv zeta in RQ. cbv zeta.
eapply OK4_eq; [apply getm_eq; exact Mg|]. apply (rq_eq _ _ _ _ _ (getm_eq g s am Mg)) in RQ. cbv zeta in RQ. cbv zeta.
destruct (release_slot_eq g 0 s am fr Mg Hfr) as (x & Hx & RS).
eapply OK4_eq; [exact RS|]. apply (rq_eq _ _ _ _ _ RS) in RQ.
set (s1 := upd_meta g (MUsed (upd_slot am 0 x)) s) in *.
rewrite Cfr, Cav. cbn [Z.lor Z.eqb negb andb Z.land].
unfold massert. rewrite Cfr, Cav in RQ. cbn [Z.lor Z.eqb negb andb Z.land massert] in RQ.
unfold massert in RQ. replace (Z.land (Z.lor 0 0) (bit 0) =? 0) with true in RQ |- * by reflexivity. cbv iota in RQ. cbv iota. o_ret. rq_ret RQ.
set (am1 := upd_slot am 0 x) in *.
assert (F1 : am_sc am1 = 63) by (subst am1; destruct am; exact Csc).
assert (F2 : am_last am1 = 0) by (subst am1; destruct am; exact Cl0).
assert (F3 : am_avail am1 = 0) by (subst am1; destruct am; exact Cav).
assert (F4 : am_freed am1 = 0) by (subst am1; destruct am; exact Cfr).
assert (F5 : am_next am1 = None) by (subst am1; destruct am; exact Hnx).
assert (F6 : am_maplen am1 = am_maplen am) by (subst am1; destruct am; reflexivity).
assert (F7 : am_mem am1 = am_mem am) by (subst am1; destruct am; reflexivity).
assert (M1 : MT s1 g = Some (MUsed am1)) by (subst s1; apply MT_upd_same).
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y.
{ apply (OK4_nf63 _ g am1 s1 (fun x => fst x = Some (prid (am_mem am1), am_maplen am1 * 4096) /\ meas (snd x) = meas s1));
[exact M1 | exact F1 | exact F2 | exact F3 | exact F4 | exact F5 | rewrite F6; exact Cml |].
intros s' E'. cbn [fst snd]. split; [reflexivity | exact E']. }
intros mi s5 tr5 Hy5 [Hmi E5]. cbn [fst snd] in Hmi, E5. specialize (RQ2 tr5 mi s5 Hy5). clear RQ1 Hy5. subst mi.
rewrite F6, F7, Hmem in RQ2 |- *. cbn [prid] in RQ2 |- *.
rq_bind RQ2 RQ3 RQ4. pose proof (reqs_ok_ask_inv _ _ RQ3) as RK.
assert (E50 : meas s5 = meas s) by (rewrite E5; subst s1; apply meas_upd_meta).
pose proof (meas_eq_II _ _ E50 HII) as II5. pose proof (meas_eq_all _ _ E50) as (Y1 & Y2 & _).
eapply OK4_bind_y.
{ apply (OK4_ask_free (KMunmap r (am_maplen am * 4096)) s5 (fun q => snd q = s5)); [reflexivity | intros q; discriminate | intros b; reflexivity]. }
intros b6 s6 tr6 _ E6. cbn [snd] in E6. subst s6.
eapply OK4_mono; [|apply OK4_kill; [exact RK | exact II5]].
intros [u7 s7] HK. unfold KillPost in HK. cbn [snd] in HK. destruct HK as (_ & K1 & K2 & _).
cbn [snd]. rewrite K1, K2, Y1, Y2. change 4096 with PGSZ. rewrite page_round_multiple by lia. lia.
Qed.
End d.
