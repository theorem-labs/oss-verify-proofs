(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0l.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
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
Ltac rq_put H := match type of H with reqs_ok (bind (put ?s1) ?k ?s0) => change (reqs_ok (k tt s1)) in H; cbv beta in H end.
Ltac rq_modify H := match type of H with reqs_ok (bind (modify ?f) ?k ?s0) => change (reqs_ok (k tt (f s0))) in H; cbv beta in H end.
Ltac rq_ret H := match type of H with reqs_ok (bind (ret ?a) ?k ?s0) => change (reqs_ok (k a s0)) in H; cbv beta in H end.
Ltac rq_bind H Hm Hf := pose proof (reqs_ok_mbind_inv _ _ _ H) as [Hm Hf]; clear H.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation amc s := (st_avail_meta_count s).
Definition PRE4 (f : nat) (s : astate) : Prop :=
II s /\
((LIVE_UB s + 3 * PGSZ + area s + MMAX <= MG_LIVE /\ SLOT_UB s + 5 <= MG_SLOTS /\ area s <= MG_REQ)
\/ (Z.of_nat f <= amc s /\ LIVE_UB s + MMAX <= MG_LIVE /\ SLOT_UB s + 1 <= MG_SLOTS)).
Definition POST4 (f : nat) (s : astate) {A} (r : A * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' <= map_bytes s + MMAX /\ map_count s' <= map_count s + 1 /\
hand s' <= hand s + Z.of_nat f /\ shift s <= shift s' <= shift s + 1 /\
brk_bytes s' <= brk_bytes s + 2 * PGSZ /\
LIVE_UB s' <= LIVE_UB s + 2 * PGSZ + area s + MMAX /\ SLOT_UB s' <= SLOT_UB s + 5 /\
(Z.of_nat f <= amc s -> shift s' = shift s /\ brk_bytes s' = brk_bytes s /\ LIVE_UB s' <= LIVE_UB s + MMAX /\ SLOT_UB s' <= SLOT_UB s + 1).
Lemma MMAX_le_REQ : MMAX <= MG_REQ.
Proof. unfold MMAX, MG_REQ. apply Z.pow_le_mono_r; lia. Qed.
Lemma area_nonneg s : II s -> 0 <= area s.
Proof. intros (_ & Hsh & _). unfold area, PGSZ. pose proof (Z.pow_nonneg 2 (shift s)). lia. Qed.
Lemma PRE4_meas f s s' : meas s' = meas s -> PRE4 f s -> PRE4 f s'.
Proof.
intros E [HII H]. pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
split; [eapply meas_eq_II; eauto|]. unfold area. rewrite E4, E6, E9, E10. exact H.
Qed.
Lemma POST4_meas f s s' {A B} (a : A) (b : B) s1 :
II s -> meas s' = meas s -> POST4 f s (a, s1) = POST4 f s (a, s1).
Proof. reflexivity. Qed.
Lemma POST4_after f s {A B} (a : A) s1 (b : B) s2 : POST4 f s (a, s1) -> meas s2 = meas s1 -> POST4 f s (b, s2).
Proof.
unfold POST4. cbn [snd]. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) E.
pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
rewrite E1, E2, E3, E4, E5, E9, E10. split; [eapply meas_eq_II; eauto|]. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
Qed.
Lemma POST4_refl f s {A} (a : A) s1 : II s -> meas s1 = meas s -> POST4 f s (a, s1).
Proof.
intros HII E. pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
pose proof (area_nonneg s HII). unfold POST4. cbn [snd]. rewrite E1, E2, E3, E4, E5, E9, E10.
split; [eapply meas_eq_II; eauto|]. unfold MMAX, PGSZ in *. repeat match goal with |- _ /\ _ => split end; try lia.
all: intros _; repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma PRE4_weaken f g s : (g <= f)%nat -> PRE4 f s -> PRE4 g s.
Proof. intros Hle [HII [H|H]]; split; [exact HII| left; exact H | exact HII | right]. lia. Qed.
Theorem OK4_alloc_both : forall f, (f <= 100)%nat ->
(forall sc req s, reqs_ok (alloc_slot f sc req s) -> PRE4 f s -> 0 <= req < 2 ^ 17 ->
OK4 (POST4 f s) (alloc_slot f sc req s))
/\ (forall sc req s, reqs_ok (alloc_group f sc req s) -> PRE4 f s -> 0 <= req < 2 ^ 17 ->
OK4 (POST4 f s) (alloc_group f sc req s)).
Proof.
induction f as [|f IH]; intros Hf.
- split; intros sc req s RQ HP Hr; cbn; apply OK4_fail.
- assert (Hf' : (f <= 100)%nat) by lia. destruct (IH Hf') as [IHs IHg]. clear IH.
split; intros sc req s RQ HP Hr; pose proof HP as [HII HB].
+
rewrite alloc_slot_S in RQ |- *. rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y; [apply (OK4_frame_meas (try_avail sc) s); auto with presK presC|].
intros first s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 first s1 Hy1). clear RQ1 Hy1.
destruct (negb (first =? 0)).
* apply OK4_ret. apply POST4_refl; [exact HII | exact E1].
* rq_bind RQ2 RQ3 RQ4.
eapply OK4_bind_y.
{ apply IHg; [exact RQ3 | | exact Hr]. apply (PRE4_meas _ s); [exact E1|]. apply (PRE4_weaken (S f)); [lia | exact HP]. }
intros og s2 tr2 Hy2 HP2.
assert (HP2' : POST4 (S f) s (og, s2)).
{ pose proof (meas_eq_all _ _ E1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold POST4 in HP2 |- *. cbn [snd] in HP2 |- *. unfold area in *. rewrite Q1, Q2, Q3, Q4, Q5, Q9, Q10 in HP2.
destruct HP2 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). rewrite Q6 in G9.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: intros Hamc; destruct (G9 ltac:(lia)) as (K1 & K2 & K3 & K4); repeat match goal with |- _ /\ _ => split end; lia. }
destruct og; apply OK4_ret; exact HP2'.
+
pose proof (area_nonneg s HII) as HA. pose proof MMAX_le_REQ as HMR.
cbn [alloc_group] in RQ |- *. rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y.
{ apply OK4_alloc_meta; [exact RQ1 | exact HII |]. intros Hz. destruct HB as [(R1 & R2 & R3)|(N1 & N2 & N3)]; [|exfalso; lia].
unfold ROOMm. unfold area, MMAX in *. unfold PGSZ in *. lia. }
intros om s1 tr1 Hy1 HP1. specialize (RQ2 tr1 om s1 Hy1). clear RQ1 Hy1.
unfold MetaPost in HP1. cbn [fst snd] in HP1. destruct HP1 as (II1 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
destruct om as [m|].
2:{ apply OK4_ret. unfold POST4. cbn [snd]. unfold MMAX, PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: intros Hamc; destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4); repeat match goal with |- _ /\ _ => split end; lia. }
assert (HX : (LIVE_UB s1 <= LIVE_UB s /\ SLOT_UB s1 <= SLOT_UB s /\ shift s1 = shift s /\ brk_bytes s1 = brk_bytes s) \/ amc s1 = 100)
by (apply M8; discriminate).
o_get. rq_get RQ2.
pose proof (initial_cnt_bound sc (usage_of s1 sc)) as Hcnt.
set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Enest.
*
pose proof (mmap_plan_len_bound s1 sc req cnt0 (usage_of s1 sc) Hr Hcnt) as Hlen.
set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)) in *.
rq_bind RQ2 RQ3 RQ4.
eapply OK4_bind_y; [apply (OK4_frame_meas (account_bounce sc) s1); auto with presK presC|].
intros u2 s2 tr2 Hy2 E2. specialize (RQ4 tr2 u2 s2 Hy2). clear RQ3 Hy2. cbn [snd] in E2.
rq_bind RQ4 RQ5 RQ6.
eapply OK4_bind_y; [apply (OK4_frame_meas step_seq s2); auto with presK presC|].
intros u3 s3 tr3 Hy3 E3. specialize (RQ6 tr3 u3 s3 Hy3). clear RQ5 Hy3. cbn [snd] in E3.
assert (E31 : meas s3 = meas s1) by (rewrite E3; exact E2).
pose proof (meas_eq_all _ _ E31) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E31 II1) as II3. pose proof II3 as (NN3 & _).
rq_bind RQ6 RQ7 RQ8.
eapply OK4_bind_y.
{ apply (OK4_ask_room (KMmapRW (snd plan)) s3 (fun x => snd x = s3)); [ | intros q; discriminate | intros b; reflexivity].
cbn [mgrant req_len]. pose proof (LIVE_UB_ok s3 NN3). pose proof (SLOT_UB_ok s3 NN3). pose proof (page_round_ge (snd plan)).
rewrite Q9, Q10 in *.
destruct HB as [(R1 & R2 & R3)|(N1 & N2 & N3)].
- unfold MMAX, MG_REQ, area in *. unfold PGSZ in *. lia.
- destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4). unfold MMAX, MG_REQ in *. unfold PGSZ in *. lia. }
intros ok s4 tr4 Hy4 E4. cbn [snd] in E4. subst s4. specialize (RQ8 tr4 ok s3 Hy4). clear RQ7 Hy4.
destruct ok; cbn [negb] in RQ8 |- *.
--
apply OK4_bind_new_region. o_get. o_put.
match goal with |- OK4 _ (bind _ _ ?sx) => set (s5 := sx) end.
destruct (app_measures s3 s5 (mkRegion RkMap (page_round (snd plan)) [] true) eq_refl eq_refl eq_refl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof (app_regs_nn s3 s5 (mkRegion RkMap (page_round (snd plan)) [] true) eq_refl NN3 ltac:(cbn [rg_len]; pose proof (page_round_ge (snd plan)); lia)) as NN5.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in A1, A2, A3, A4, A5.
assert (A8 : shift s5 = shift s3) by reflexivity. assert (A9 : acnt s5 = acnt s3) by reflexivity. assert (A10 : amc s5 = amc s3) by reflexivity.
eapply OK4_bind_y; [apply (OK4_frame_meas (install_group m sc _ _ _ _ _) s5); auto with presK presC|].
intros u6 s6 tr6 Hy6 E6. cbn [snd] in E6. apply OK4_ret.
apply (POST4_after (S f) s tt s5 (Some m) s6); [|exact E6].
unfold POST4. cbn [snd].
assert (II5 : II s5).
{ pose proof II3 as (_ & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). unfold II.
unfold hand in *. rewrite A3, A4, A5, A6, A8, A9, A10. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
unfold LIVE_UB, SLOT_UB in *. unfold hand in *.
rewrite A1, A2, A3, A4, A5, A6, A8, A10 || idtac. rewrite !Z.add_0_r.
rewrite Q1, Q2, Q4, Q5 in *. rewrite Q6, Q8.
assert (ERt : resv_total s3 = resv_total s1) by (unfold resv_total; unfold meas in E31; congruence).
assert (ERc : resv_count s3 = resv_count s1) by (unfold resv_count; unfold meas in E31; congruence).
rewrite ERt, ERc in *.
split; [exact II5|]. unfold MMAX, area in *. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia.
all: try (intros Hamc; destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4); repeat match goal with |- _ /\ _ => split end; lia).
--
eapply OK4_bind_y; [apply (OK4_frame_meas (free_meta m) s3); auto with presK presC|].
intros u5 s5 tr5 Hy5 E5. cbn [snd] in E5. apply OK4_ret.
apply (POST4_after (S f) s tt s3 None s5); [|exact E5].
apply (POST4_after (S f) s tt s1 tt s3); [|exact E31].
unfold POST4. cbn [snd]. unfold MMAX, PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: intros Hamc; destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4); repeat match goal with |- _ /\ _ => split end; lia.
*
pose proof (class_size_bound sc) as Hsz.
assert (Htot : 0 <= UNIT + cnt0 * class_size sc - IB < 2 ^ 17).
{ apply Z.ltb_ge in Enest. unfold UNIT, IB, PGSZ in *. nia. }
assert (COMP : forall (A B : Type) (a : A) (b : B) s7 s8, POST4 f s1 (a, s7) -> meas s8 = meas s7 -> POST4 (S f) s (b, s8)).
{ intros A B a b s7 s8 HP7 E8. apply (POST4_after (S f) s a s7 b s8); [|exact E8].
unfold POST4 in HP7 |- *. cbn [snd] in HP7 |- *. destruct HP7 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold area in *. unfold MMAX, PGSZ in *.
destruct HX as [(X1 & X2 & X3 & X4) | Hamc100].
- rewrite X3 in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: intros Hamc; destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4);
assert (Hf1 : Z.of_nat f <= amc s1) by (pose proof (M6 ltac:(discriminate)); lia);
destruct (G9 Hf1) as (L1 & L2 & L3 & L4); repeat match goal with |- _ /\ _ => split end; lia.
- assert (Hf1 : Z.of_nat f <= amc s1) by (rewrite Hamc100; lia).
destruct (G9 Hf1) as (L1 & L2 & L3 & L4).
assert (HP2 : 2 ^ shift s1 <= 2 * 2 ^ shift s).
{ destruct M4 as [M4a M4b]. destruct (Z.eq_dec (shift s1) (shift s)) as [E|NE]; [rewrite E; pose proof (Z.pow_nonneg 2 (shift s)); lia|].
replace (shift s1) with (shift s + 1) by lia. rewrite pow2_succ; [lia|]. destruct HII as (_ & Hsh & _); exact Hsh. }
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: intros Hamc; destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4); repeat match goal with |- _ /\ _ => split end; lia. }
rq_bind RQ2 RQ3 RQ4.
eapply OK4_bind_y.
{ apply IHs; [exact RQ3 | | exact Htot].
split; [exact II1|].
destruct HX as [(X1 & X2 & X3 & X4) | Hamc100].
- destruct HB as [(R1 & R2 & R3)|(N1 & N2 & N3)].
+ left. unfold area in *. rewrite X3. lia.
+ right. pose proof (M6 ltac:(discriminate)) as Hmin. split; [lia|]. lia.
- right. split; [rewrite Hamc100; lia|]. destruct HB as [(R1 & R2 & R3)|(N1 & N2 & N3)]; unfold MMAX, area in *; unfold PGSZ in *; [lia|].
destruct (M7 ltac:(lia)) as (K1 & K2 & K3 & K4). lia. }
intros idx s7 tr7 Hy7 HP7. specialize (RQ4 tr7 idx s7 Hy7). clear RQ3 Hy7.
match goal with |- OK4 _ ((if ?c then ?mA else ?mB) s7) =>
assert (PKA : presK mA) by kgo; assert (PCA : presC mA) by cgo;
assert (PKB : presK mB) by kgo; assert (PCB : presC mB) by cgo;
destruct c end.
-- eapply OK4_mono; [| apply OK4_frame_meas; [exact PKA | exact PCA]]. intros [b s8] E8. cbn [snd] in E8. eapply COMP; [exact HP7 | exact E8].
-- eapply OK4_mono; [| apply OK4_frame_meas; [exact PKB | exact PCB]]. intros [b s8] E8. cbn [snd] in E8. eapply COMP; [exact HP7 | exact E8].
Qed.
End d.
