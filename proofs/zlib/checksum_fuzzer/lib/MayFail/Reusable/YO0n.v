(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0n.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: removed the forced-success allocator trace lemmas and selected the may-fail runtime modules; changed module paths to the MayFail runtime. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
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
Definition mdelta (n : Z) : Z := if MMAP_THRESHOLD <=? n then page_round (n + IB + UNIT) else MMAX.
Lemma mdelta_nonneg n : 0 <= n -> 0 <= mdelta n.
Proof. intros Hn. unfold mdelta. destruct (MMAP_THRESHOLD <=? n); [|unfold MMAX; lia]. pose proof (page_round_bounds (n + IB + UNIT)). unfold IB, UNIT in *. lia. Qed.
Definition ROOM4 (s : astate) (n : Z) : Prop :=
LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= MG_LIVE /\
SLOT_UB s + 5 <= MG_SLOTS /\ area s <= MG_REQ /\ page_round (n + IB + UNIT) <= MG_REQ.
Definition MPost (s : astate) (n : Z) (r : option sptr * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' <= map_bytes s + mdelta n /\ map_count s' <= map_count s + 1 /\
hand s' <= hand s + 65 /\ shift s <= shift s' <= shift s + 1 /\ brk_bytes s' <= brk_bytes s + 2 * PGSZ.
Lemma MPost_meas s n {A} (a : A) s1 (b : option sptr) s2 :
II s1 /\ map_bytes s1 <= map_bytes s + mdelta n /\ map_count s1 <= map_count s + 1 /\
hand s1 <= hand s + 65 /\ shift s <= shift s1 <= shift s + 1 /\ brk_bytes s1 <= brk_bytes s + 2 * PGSZ ->
meas s2 = meas s1 -> MPost s n (b, s2).
Proof.
intros (H1 & H2 & H3 & H4 & H5 & H6) E. pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & _).
unfold MPost. cbn [snd]. rewrite E1, E2, E3, E4, E5. split; [eapply meas_eq_II; eauto|]. repeat split; assumption || lia.
Qed.
Lemma meas_set_mmap_counter v s : meas (set_mmap_counter v s) = meas s.
Proof. reflexivity. Qed.
Ltac rq_new_region H :=
match type of H with reqs_ok (bind (new_region ?k ?len) ?K ?s0) =>
change (reqs_ok (K (length (st_regions s0)) (set_regions (st_regions s0 ++ [mkRegion k len [] true]) s0))) in H end.
Definition KillPost (s : astate) (len : Z) (x : unit * astate) : Prop :=
let s' := snd x in
II s' /\ map_bytes s' = map_bytes s - page_round len /\ map_count s' = map_count s - 1 /\ brk_bytes s' = brk_bytes s /\
resv_total s' = resv_total s /\ resv_count s' = resv_count s /\ hand s' = hand s /\ shift s' = shift s /\
acnt s' = acnt s /\ amc s' = amc s /\ nareas s' = nareas s.
Lemma OK4_kill r len s : req_ok s (KMunmap r len) -> II s ->
OK4 (KillPost s len) (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) s).
Proof.
intros RK HII. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
cbn [req_ok] in RK. destruct RK as (rg & Hrg & Hkind & Hlive & Hlen & Hlen0 & _).
unfold upd_region. apply OK4_modify.
match goal with |- KillPost _ _ (_, ?sx) => set (s2 := sx) end.
assert (Hnn : 0 <= rg_len rg) by (apply NN; eapply nth_error_In; exact Hrg).
destruct (upd_measures s s2 r (fun g => mkRegion RkMap (rg_len g) [] false) rg eq_refl Hrg eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
pose proof (upd_regs_nn s s2 r (fun g => mkRegion RkMap (rg_len g) [] false) rg eq_refl Hrg NN ltac:(cbn; lia)) as NN2.
unfold f_mapb, f_mapc, f_brkb, f_resvb, f_resvc, is_map, is_brk, is_resv in M1, M2, M3, M4, M5.
cbn [rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5.
rewrite ?Hkind, ?Hlive in M1. rewrite ?Hkind, ?Hlive in M2. rewrite ?Hkind, ?Hlive in M3. rewrite ?Hkind in M4. rewrite ?Hkind in M5. cbn [andb] in M1, M2, M3, M4, M5.
assert (M8 : shift s2 = shift s) by reflexivity. assert (EA : acnt s2 = acnt s) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
unfold KillPost, II. cbn [snd]. unfold hand in *. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M8, !EA, !EM. rewrite Hlen.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2.
Qed.
Theorem OK4_malloc n s : reqs_ok (malloc n s) -> II s -> 0 <= n -> ROOM4 s n -> OK4 (MPost s n) (malloc n s).
Proof.
intros RQ HII Hn (R1 & R2 & R3 & R4). pose proof HII as (NN & Hsh & _).
pose proof (area_nonneg s HII) as HA. pose proof (mdelta_nonneg n Hn) as HD.
assert (P0 : forall (b : option sptr) s', meas s' = meas s -> MPost s n (b, s')).
{ intros b s' E. apply (MPost_meas s n tt s b s'); [|exact E]. split; [exact HII|]. unfold PGSZ. repeat split; lia. }
unfold malloc in RQ |- *.
destruct (size_overflows n) eqn:Eo; [apply OK4_ret; apply P0; reflexivity|].
destruct (MMAP_THRESHOLD <=? n) eqn:Em.
-
assert (Hmd : mdelta n = page_round (n + IB + UNIT)) by (unfold mdelta; rewrite Em; reflexivity).
pose proof (page_round_bounds (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as PB.
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y.
{ apply (OK4_ask_room (KMmapRW (n + IB + UNIT)) s (fun x => snd x = s)); [ | intros q; discriminate | intros b; reflexivity].
cbn [mgrant req_len]. pose proof (LIVE_UB_ok s NN). pose proof (SLOT_UB_ok s NN). unfold IB, UNIT in *. unfold PGSZ in *. lia. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. specialize (RQ2 tr1 ok s Hy1). clear RQ1 Hy1.
destruct ok; cbn [negb] in RQ2 |- *; [|apply OK4_ret; apply P0; reflexivity].
apply OK4_bind_new_region. rq_new_region RQ2.
match goal with |- OK4 _ (bind _ _ ?sx) => set (s1 := sx) in * end.
destruct (app_measures s s1 (mkRegion RkMap (page_round (n + IB + UNIT)) [] true) eq_refl eq_refl eq_refl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof (app_regs_nn s s1 (mkRegion RkMap (page_round (n + IB + UNIT)) [] true) eq_refl NN ltac:(cbn [rg_len]; lia)) as NN1.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in A1, A2, A3, A4, A5.
assert (A8 : shift s1 = shift s) by reflexivity. assert (A9 : acnt s1 = acnt s) by reflexivity. assert (A10 : amc s1 = amc s) by reflexivity.
assert (II1 : II s1).
{ pose proof HII as (_ & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). unfold II.
unfold hand in *. rewrite A3, A4, A5, A6, A8, A9, A10. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
assert (L1 : LIVE_UB s1 = LIVE_UB s + page_round (n + IB + UNIT)) by (unfold LIVE_UB; lia).
assert (L2 : SLOT_UB s1 = SLOT_UB s + 1) by (unfold SLOT_UB; rewrite A2, A3, A5, !Z.add_0_r; lia).
assert (L3 : area s1 = area s) by (unfold area; rewrite A8; reflexivity).
rq_bind RQ2 RQ3 RQ4.
eapply OK4_bind_y; [apply (OK4_frame_meas step_seq s1); auto with presK presC|].
intros u2 s2 tr2 Hy2 E2. cbn [snd] in E2. specialize (RQ4 tr2 u2 s2 Hy2). clear RQ3 Hy2.
pose proof (meas_eq_all _ _ E2) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E2 II1) as II2.
rq_bind RQ4 RQ5 RQ6.
eapply OK4_bind_y.
{ apply OK4_alloc_meta; [exact RQ5 | exact II2 |]. intros _. unfold ROOMm. fold (area s2). unfold area in *. rewrite Q9, Q10, Q4. unfold PGSZ in *. lia. }
intros og s3 tr3 Hy3 HP3. specialize (RQ6 tr3 og s3 Hy3). clear RQ5 Hy3.
unfold MetaPost in HP3. cbn [fst snd] in HP3. destruct HP3 as (II3 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
assert (P3 : forall (b : option sptr) s', meas s' = meas s3 -> MPost s n (b, s')).
{ intros b s' E. apply (MPost_meas s n tt s3 b s'); [|exact E]. split; [exact II3|]. rewrite Hmd. unfold PGSZ in *. repeat split; lia. }
destruct og as [g|].
+ eapply OK4_bind_y; [apply (OK4_frame_meas (setm g _) s3); auto with presK presC|].
intros u4 s4 tr4 Hy4 E4. cbn [snd] in E4. clear Hy4.
o_get. o_put.
eapply OK4_bind_y; [apply (OK4_frame_meas (enframe g 0 n _ FUser) (set_mmap_counter _ s4)); auto with presK presC|].
intros p s5 tr5 Hy5 E5. cbn [snd] in E5. clear Hy5. apply OK4_ret. apply P3. rewrite E5, meas_set_mmap_counter. exact E4.
+ rq_bind RQ6 RQ7 RQ8. pose proof (reqs_ok_ask_inv _ _ RQ7) as RK.
eapply OK4_bind_y.
{ apply (OK4_ask_free (KMunmap (length (st_regions s)) (n + IB + UNIT)) s3 (fun x => snd x = s3)); [reflexivity | intros q; discriminate | intros b; reflexivity]. }
intros b4 s4 tr4 Hy4 E4. cbn [snd] in E4. subst s4. clear Hy4.
eapply OK4_bind_y; [apply OK4_kill; [exact RK | exact II3]|].
intros u5 s5 tr5 Hy5 HK5. clear Hy5. apply OK4_ret.
unfold KillPost in HK5. cbn [snd] in HK5. destruct HK5 as (II5 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10).
unfold MPost. cbn [snd]. split; [exact II5|]. rewrite Hmd. unfold PGSZ in *. repeat split; lia.
-
assert (Hmd : mdelta n = MMAX) by (unfold mdelta; rewrite Em; reflexivity).
apply Z.leb_gt in Em. unfold MMAP_THRESHOLD in Em.
o_get. rq_get RQ.
match goal with |- OK4 _ (bind _ (fun r => bind (match r with Some gi => ret (Some gi) | None => bind (alloc_slot _ ?sc _) _ end) _) _) =>
set (scz := sc) in * end.
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y; [apply OK4_frame_meas; [kgo | cgo]|].
intros r s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 r s1 Hy1). clear RQ1 Hy1.
pose proof (meas_eq_all _ _ E1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E1 HII) as II1.
rq_bind RQ2 RQ3 RQ4.
eapply (OK4_bind_y (fun x => MPost s n (None, snd x))).
{ destruct r as [gi|]; [apply OK4_ret; apply P0; exact E1|].
rq_bind RQ3 RQ5 RQ6.
eapply OK4_bind_y.
{ apply (proj1 (OK4_alloc_both NEST_FUEL ltac:(unfold NEST_FUEL; lia)) scz n s1); [exact RQ5 | | lia].
split; [exact II1|]. left. unfold area in *. rewrite Q9, Q10, Q4. lia. }
intros idx s2 tr2 Hy2 HP2. specialize (RQ6 tr2 idx s2 Hy2). clear RQ5 Hy2.
unfold POST4 in HP2. cbn [snd] in HP2. destruct HP2 as (II2 & G1 & G2 & G3 & G4 & G5 & _).
assert (P2 : forall (b : option (sptr * Z)) s', meas s' = meas s2 -> MPost s n (None, s')).
{ intros b s' E. apply (MPost_meas s n tt s2 None s'); [|exact E]. split; [exact II2|]. rewrite Hmd. unfold NEST_FUEL in G3. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G3.
rewrite Q1, Q2, Q3, Q4, Q5 in *. repeat split; lia. }
apply OK4_if; [apply OK4_ret; apply (P2 None); reflexivity|].
eapply OK4_bind_y; [apply (OK4_frame_meas (get_head (HActive scz)) s2); auto with presK presC|].
intros hd s3 tr3 Hy3 E3. cbn [snd] in E3. destruct hd as [gm|]; [apply OK4_ret; apply (P2 None); exact E3 | apply OK4_fail]. }
intros gi s4 tr4 Hy4 HP4. clear Hy4.
destruct gi as [[gm idx]|]; [|apply OK4_ret; exact HP4].
o_get. eapply OK4_bind_y; [apply (OK4_frame_meas (enframe gm idx n _ FUser) s4); auto with presK presC|].
intros p s5 tr5 Hy5 E5. cbn [snd] in E5. apply OK4_ret. revert HP4 E5. unfold MPost. cbn [snd]. intros HP4 E5.
pose proof (meas_eq_all _ _ E5) as (Y1 & Y2 & Y3 & Y4 & Y5 & _). rewrite Y1, Y2, Y3, Y4, Y5.
split; [eapply meas_eq_II; [exact E5 | exact (proj1 HP4)] | exact (proj2 HP4)].
Qed.
(** Success-only path lemmas from the restricted environment do not apply
    here. The general resource bounds above cover successful and failed calls. *)
Lemma k_nontrivial_free f : forall g i, presK (nontrivial_free f g i).
Proof. induction f as [|f IH]; intros g i; cbn [nontrivial_free]; kgo. Qed.
Lemma c_nontrivial_free f : forall g i, presC (nontrivial_free f g i).
Proof. induction f as [|f IH]; intros g i; cbn [nontrivial_free]; cgo. Qed.
Definition FPost (s : astate) (x : unit * astate) : Prop :=
let s' := snd x in
II s' /\ map_bytes s' <= map_bytes s /\ map_count s' <= map_count s /\ hand s' = hand s /\ shift s' = shift s /\
brk_bytes s' = brk_bytes s /\ LIVE_UB s' <= LIVE_UB s /\ SLOT_UB s' <= SLOT_UB s.
Lemma FPost_meas s s1 s2 (a b : unit) : FPost s (a, s1) -> meas s2 = meas s1 -> FPost s (b, s2).
Proof.
unfold FPost. cbn [snd]. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) E.
pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
rewrite E1, E2, E3, E4, E5, E9, E10. split; [eapply meas_eq_II; eauto|]. repeat split; assumption.
Qed.
Lemma FPost_refl s s1 (b : unit) : II s -> meas s1 = meas s -> FPost s (b, s1).
Proof. intros HII E. apply (FPost_meas s s s1 tt b); [|exact E]. unfold FPost. cbn [snd]. split; [exact HII|]. repeat split; lia. Qed.
Theorem OK4_free p s : reqs_ok (free p s) -> II s -> OK4 (FPost s) (free p s).
Proof.
intros RQ HII. unfold free in RQ |- *. destruct p as [p|]; [|apply OK4_ret; apply FPost_refl; [exact HII | reflexivity]].
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y; [apply (OK4_frame_meas (find_frame p) s); auto with presK presC|].
intros gi s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 gi s1 Hy1). clear RQ1 Hy1. cbv zeta in RQ2 |- *.
rq_bind RQ2 RQ3 RQ4.
eapply OK4_bind_y; [apply (OK4_frame_meas (getm (fst gi)) s1); auto with presK presC|].
intros am s2 tr2 Hy2 E2. cbn [snd] in E2. specialize (RQ4 tr2 am s2 Hy2). clear RQ3 Hy2. cbv zeta in RQ4 |- *.
rq_bind RQ4 RQ5 RQ6.
eapply OK4_bind_y; [apply (OK4_frame_meas (release_slot (fst gi) (snd gi)) s2); auto with presK presC|].
intros u3 s3 tr3 Hy3 E3. cbn [snd] in E3. specialize (RQ6 tr3 u3 s3 Hy3). clear RQ5 Hy3.
rq_bind RQ6 RQ7 RQ8.
eapply OK4_bind_y; [apply (OK4_frame_meas (massert _ 7) s3); auto with presK presC|].
intros u4 s4 tr4 Hy4 E4. cbn [snd] in E4. specialize (RQ8 tr4 u4 s4 Hy4). clear RQ7 Hy4.
assert (E40 : meas s4 = meas s) by (rewrite E4, E3, E2; exact E1).
match goal with |- OK4 _ ((if ?c then _ else _) _) => destruct c end.
- eapply OK4_mono; [|apply OK4_frame_meas; [kgo | cgo]]. intros [u5 s5] E5. cbn [snd] in E5.
apply FPost_refl; [exact HII | rewrite E5; exact E40].
- rq_bind RQ8 RQ9 RQ10.
eapply OK4_bind_y; [apply (OK4_frame_meas (nontrivial_free NEST_FUEL (fst gi) (snd gi)) s4); [apply k_nontrivial_free | apply c_nontrivial_free]|].
intros mi s5 tr5 Hy5 E5. cbn [snd] in E5. specialize (RQ10 tr5 mi s5 Hy5). clear RQ9 Hy5.
assert (E50 : meas s5 = meas s) by (rewrite E5; exact E40). pose proof (meas_eq_II _ _ E50 HII) as II5.
destruct mi as [[r len]|]; [|apply OK4_ret; apply FPost_refl; [exact HII | exact E50]].
rq_bind RQ10 RQ11 RQ12. pose proof (reqs_ok_ask_inv _ _ RQ11) as RK.
eapply OK4_bind_y.
{ apply (OK4_ask_free (KMunmap r len) s5 (fun x => snd x = s5)); [reflexivity | intros q; discriminate | intros b; reflexivity]. }
intros b6 s6 tr6 Hy6 E6. cbn [snd] in E6. subst s6. clear Hy6.
eapply OK4_mono; [|apply OK4_kill; [exact RK | exact II5]].
intros [u7 s7] HK. unfold KillPost in HK. cbn [snd] in HK. destruct HK as (II7 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10).
pose proof (meas_eq_all _ _ E50) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
cbn [req_ok] in RK. destruct RK as (rg & _ & _ & _ & _ & Hlen0 & _). pose proof (page_round_bounds len Hlen0).
unfold FPost. cbn [snd]. unfold LIVE_UB, SLOT_UB in *. rewrite K1, K2, K3, K4, K5, K6, K7, Y1, Y2, Y3, Y4, Y5.
assert (ERt : resv_total s5 = resv_total s) by (unfold resv_total; unfold meas in E50; congruence).
assert (ERc : resv_count s5 = resv_count s) by (unfold resv_count; unfold meas in E50; congruence).
rewrite ERt, ERc. split; [exact II7|]. repeat split; try lia.
Qed.
End d.
