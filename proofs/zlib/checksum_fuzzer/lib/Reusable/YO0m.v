(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation amc s := (st_avail_meta_count s).
Definition acnt (s : astate) : Z := st_avail_meta_area_count s.
Definition nareas (s : astate) : Z := Z.of_nat (length (st_areas s)).
Definition hand (s : astate) : Z := METAS_PER_AREA * nareas s - amc s.
Definition II (s : astate) : Prop :=
regs_nn s /\ 0 <= shift s /\ 0 <= acnt s /\ 0 <= amc s <= METAS_PER_AREA /\
resv_total s = 2 * PGSZ * (2 ^ shift s - 1) /\
resv_count s <= 2 ^ shift s /\
2 ^ (shift s + 1) - 2 - shift s <= nareas s + acnt s /\
brk_bytes s <= 2 * PGSZ * (nareas s + acnt s) /\
METAS_PER_AREA * (2 ^ shift s - 1 - shift s) <= hand s.
Definition LIVE_UB (s : astate) : Z := map_bytes s + brk_bytes s + resv_total s.
Definition SLOT_UB (s : astate) : Z := map_count s + brk_bytes s / PGSZ + resv_count s.
Lemma LIVE_UB_ok s : regs_nn s -> live_bytes s <= LIVE_UB s.
Proof. intros NN. apply live_bytes_decomp. exact NN. Qed.
Lemma SLOT_UB_ok s : regs_nn s -> nslots s <= SLOT_UB s.
Proof. intros NN. apply nslots_decomp. exact NN. Qed.
Definition area (s : astate) : Z := 2 * PGSZ * 2 ^ shift s.
Definition ROOMm (s : astate) : Prop :=
LIVE_UB s + 2 * PGSZ + 2 * PGSZ * 2 ^ shift s + PGSZ <= MG_LIVE /\
SLOT_UB s + 4 <= MG_SLOTS /\
2 * PGSZ * 2 ^ shift s <= MG_REQ.
Definition MetaPost (s0 : astate) (r : option sptr * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' <= map_bytes s0 /\ map_count s' <= map_count s0 /\
hand s' <= hand s0 + 1 /\ shift s0 <= shift s' <= shift s0 + 1 /\
brk_bytes s' <= brk_bytes s0 + 2 * PGSZ /\
(fst r <> None -> Z.min (amc s0 - 1) 100 <= amc s') /\
(0 < amc s0 -> LIVE_UB s' <= LIVE_UB s0 /\ SLOT_UB s' <= SLOT_UB s0 /\ shift s' = shift s0 /\ brk_bytes s' = brk_bytes s0) /\
(fst r <> None -> (LIVE_UB s' <= LIVE_UB s0 /\ SLOT_UB s' <= SLOT_UB s0 /\ shift s' = shift s0 /\ brk_bytes s' = brk_bytes s0) \/ amc s' = 100) /\
LIVE_UB s' <= LIVE_UB s0 + 2 * PGSZ + area s0 /\ SLOT_UB s' <= SLOT_UB s0 + 4.
Definition meas (s : astate) :=
(st_regions s, st_areas s, st_meta_alloc_shift s, st_avail_meta_area_count s, amc s).
Lemma meas_eq_II s s' : meas s' = meas s -> II s -> II s'.
Proof.
destruct s, s'. unfold meas. cbn. intros E. injection E as E1 E2 E3 E4 E5. subst.
exact (fun H => H).
Qed.
Lemma meas_eq_all s s' : meas s' = meas s ->
map_bytes s' = map_bytes s /\ map_count s' = map_count s /\ hand s' = hand s /\ shift s' = shift s /\
brk_bytes s' = brk_bytes s /\ amc s' = amc s /\ acnt s' = acnt s /\ nareas s' = nareas s /\
LIVE_UB s' = LIVE_UB s /\ SLOT_UB s' = SLOT_UB s.
Proof.
destruct s, s'. unfold meas. cbn. intros E. injection E as E1 E2 E3 E4 E5. subst. repeat split; reflexivity.
Qed.
Definition msr (s : astate) :=
(map_bytes s, map_count s, brk_bytes s, resv_total s, resv_count s, nareas s, hand s, shift s, acnt s, amc s).
Lemma II_msr s s' : msr s' = msr s -> regs_nn s' -> II s -> II s'.
Proof.
unfold msr, II. intros E NN' H. injection E as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
rewrite E3, E4, E5, E6, E7, E8, E9, E10. split; [exact NN' | exact (proj2 H)].
Qed.
Lemma KEEP_KEEPC_meas s {A} (r : A * astate) : KEEP s r -> KEEPC s r -> meas (snd r) = meas s.
Proof. destruct r as [a s']. unfold KEEP, KEEPC, cres, meas. cbn. intros [R C] E. injection E as E1 E2 E3 E4. rewrite R, C, E1, E2, E3. reflexivity. Qed.
Lemma leaves_and {A} (P Q : A -> Prop) (t : itree astate A) : leaves P t -> leaves Q t -> leaves (fun a => P a /\ Q a) t.
Proof. induction t as [a | q snap k IH | e]; cbn; intros HP HQ; [split; assumption | | exact I]. intros z Hz. apply IH; auto. Qed.
Lemma OK4_frame {A} (m : M A) s : presK m -> presC m -> OK4 (fun r => meas (snd r) = meas s) (m s).
Proof.
intros HK HC. destruct (HK s) as [Hg Hl]. destruct (HC s) as [_ Hl'].
split; [apply gtree_ok04; exact Hg|].
eapply leaves_mono; [| apply (leaves_and _ _ _ Hl Hl')]. intros [a s'] [H1 H2]. apply (KEEP_KEEPC_meas s (a, s')); assumption.
Qed.
Lemma rsum_regions_app f s rg : rsum f (st_regions s ++ [rg]) = rsum f (st_regions s) + f rg.
Proof. rewrite rsum_app. cbn. unfold rsum. cbn. lia. Qed.
Lemma region_of_lt s r rg : region_of s r = Some rg -> (r < length (st_regions s))%nat /\ nth r (st_regions s) (mkRegion RkMap 0 [] false) = rg.
Proof.
unfold region_of. intros H. split.
- apply (proj1 (nth_error_Some (st_regions s) r)). rewrite H. discriminate.
- apply nth_error_nth. exact H.
Qed.
Ltac o_get := match goal with |- OK4 ?P (bind get ?k ?s0) => change (OK4 P (k s0 s0)); cbv beta end.
Ltac o_put := match goal with |- OK4 ?P (bind (put ?s1) ?k ?s0) => change (OK4 P (k tt s1)); cbv beta end.
Ltac o_modify := match goal with |- OK4 ?P (bind (modify ?f) ?k ?s0) => change (OK4 P (k tt (f s0))); cbv beta end.
Ltac rq_get H := match type of H with reqs_ok (bind get ?k ?s0) => change (reqs_ok (k s0 s0)) in H; cbv beta in H end.
Ltac rq_put H := match type of H with reqs_ok (bind (put ?s1) ?k ?s0) => change (reqs_ok (k tt s1)) in H; cbv beta in H end.
Ltac rq_modify H := match type of H with reqs_ok (bind (modify ?f) ?k ?s0) => change (reqs_ok (k tt (f s0))) in H; cbv beta in H end.
Ltac rq_bind H Hm Hf := pose proof (reqs_ok_mbind_inv _ _ _ H) as [Hm Hf]; clear H.
Definition BrkPost (s : astate) (r : bool * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' = map_bytes s /\ map_count s' = map_count s /\ hand s' = hand s /\ shift s' = shift s /\
nareas s' = nareas s /\ amc s' = amc s /\ resv_count s' = resv_count s /\ resv_total s' = resv_total s /\
brk_bytes s <= brk_bytes s' <= brk_bytes s + 2 * PGSZ /\ acnt s <= acnt s' /\
(fst r = false -> 0 < acnt s').
Lemma app_measures s s' rg :
st_regions s' = st_regions s ++ [rg] -> st_areas s' = st_areas s -> amc s' = amc s ->
map_bytes s' = map_bytes s + f_mapb rg /\ map_count s' = map_count s + f_mapc rg /\
brk_bytes s' = brk_bytes s + f_brkb rg /\ resv_total s' = resv_total s + f_resvb rg /\
resv_count s' = resv_count s + f_resvc rg /\ nareas s' = nareas s /\ hand s' = hand s.
Proof.
intros ER EA EC. unfold map_bytes, map_count, brk_bytes, resv_count, hand, nareas. rewrite !resv_total_rsum, ER, EA, EC.
rewrite !rsum_regions_app. repeat split; reflexivity.
Qed.
Lemma app_regs_nn s s' rg :
st_regions s' = st_regions s ++ [rg] -> regs_nn s -> 0 <= rg_len rg -> regs_nn s'.
Proof.
intros ER NN Hl r Hr. rewrite ER in Hr. apply in_app_iff in Hr as [Hr|[<-|[]]]; [apply NN; exact Hr | exact Hl].
Qed.
Lemma In_lupd {X} (l : list X) i v x : In x (lupd l i v) -> In x l \/ x = v.
Proof.
revert i. induction l as [|h t IH]; intros i Hx; [destruct i; destruct Hx|].
destruct i; cbn in Hx; destruct Hx as [<-|Hx].
- right; reflexivity. - left; right; exact Hx. - left; left; reflexivity.
- destruct (IH _ Hx) as [H| ->]; [left; right; exact H | right; reflexivity].
Qed.
Lemma upd_measures s s' k (g : region -> region) rg :
st_regions s' = lupd (st_regions s) k (g (nth k (st_regions s) (mkRegion RkMap 0 [] false))) ->
region_of s k = Some rg ->
st_areas s' = st_areas s -> amc s' = amc s ->
map_bytes s' = map_bytes s - f_mapb rg + f_mapb (g rg) /\ map_count s' = map_count s - f_mapc rg + f_mapc (g rg) /\
brk_bytes s' = brk_bytes s - f_brkb rg + f_brkb (g rg) /\ resv_total s' = resv_total s - f_resvb rg + f_resvb (g rg) /\
resv_count s' = resv_count s - f_resvc rg + f_resvc (g rg) /\ nareas s' = nareas s /\ hand s' = hand s.
Proof.
intros ER Hk EA EC. destruct (region_of_lt _ _ _ Hk) as [Hlt Hnth]. rewrite Hnth in ER.
unfold map_bytes, map_count, brk_bytes, resv_count, hand, nareas. rewrite !resv_total_rsum, ER, EA, EC.
rewrite !(rsum_lupd _ _ _ _ (mkRegion RkMap 0 [] false) Hlt), !Hnth. repeat split; reflexivity.
Qed.
Lemma upd_regs_nn s s' k (g : region -> region) rg :
st_regions s' = lupd (st_regions s) k (g (nth k (st_regions s) (mkRegion RkMap 0 [] false))) ->
region_of s k = Some rg -> regs_nn s -> 0 <= rg_len (g rg) -> regs_nn s'.
Proof.
intros ER Hk NN Hl r Hr. destruct (region_of_lt _ _ _ Hk) as [Hlt Hnth]. rewrite Hnth in ER. rewrite ER in Hr.
destruct (In_lupd _ _ _ _ Hr) as [H| ->]; [apply NN; exact H | exact Hl].
Qed.
Lemma OK4_bind_new_region {B} k len s (K : nat -> M B) Q :
OK4 Q (K (length (st_regions s)) (set_regions (st_regions s ++ [mkRegion k len [] true]) s)) ->
OK4 Q (bind (new_region k len) K s).
Proof. intros H. exact H. Qed.
Lemma BrkPost_meas s b s' : II s -> meas s' = meas s -> (b = false -> 0 < acnt s') -> BrkPost s (b, s').
Proof.
intros HII E Hb. pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
unfold BrkPost. cbn [fst snd]. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb2 & Hd & He).
split; [eapply meas_eq_II; eauto|].
assert (ERc : resv_count s' = resv_count s) by (unfold resv_count; unfold meas in E; congruence).
assert (ERt : resv_total s' = resv_total s) by (unfold resv_total; unfold meas in E; congruence).
unfold PGSZ in *. repeat split; try lia; auto.
Qed.
Lemma OK4_area_from_brk s : reqs_ok (area_from_brk s) -> II s -> OK4 (BrkPost s) (area_from_brk s).
Proof.
intros RQ HII. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
unfold area_from_brk in RQ |- *. o_get. rq_get RQ.
match goal with |- OK4 _ ((if ?c then _ else _) _) => destruct c eqn:Ec end.
2:{ apply OK4_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate]. }
apply andb_prop in Ec as [Ec1 Ec2]. apply Z.eqb_eq in Ec1.
destruct (st_brk s) as [ | | r pages] eqn:Eb.
-
rq_bind RQ RQ1 RQ2. eapply OK4_bind_y.
{ apply (OK4_ask_free KBrkQuery s (fun r => snd r = s)); [reflexivity | intros p; discriminate | intros b; reflexivity]. }
intros b1 s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear RQ1 RQ2 Hy1.
eapply OK4_bind_y.
{ apply (OK4_ask_free (KBrkGrow 2) s (fun r => snd r = s)); [reflexivity | intros p; discriminate | intros b; reflexivity]. }
intros ok s1 tr2 Hy2 E2. cbn [snd] in E2. subst s1. clear Hy2.
destruct ok.
+
apply OK4_bind_new_region. o_modify.
match goal with |- OK4 _ (bind _ _ ?sx) => set (s2 := sx) end.
eapply OK4_bind_y.
{ apply (OK4_ask_free KGuard s2 (fun r => snd r = s2)); [reflexivity | intros p; discriminate | intros b; reflexivity]. }
intros b3 s3 tr3 Hy3 E3. cbn [snd] in E3. subst s3. apply OK4_ret.
destruct (app_measures s s2 (mkRegion RkBrk (2 * PGSZ) [] true) eq_refl eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
assert (M8 : shift s2 = shift s) by reflexivity.
pose proof (app_regs_nn s s2 (mkRegion RkBrk (2 * PGSZ) [] true) eq_refl NN ltac:(cbn; unfold PGSZ; lia)) as NN2.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5.
assert (EA : acnt s2 = 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
unfold BrkPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
unfold acnt in *. rewrite Ec1 in *. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2.
+ o_modify. apply OK4_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
-   apply OK4_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
-
rq_bind RQ RQ1 RQ2. pose proof (reqs_ok_ask_inv _ _ RQ1) as RK. cbn [req_ok] in RK.
destruct RK as [(E & _) | (_ & r' & p' & rg & Ebrk & Hrg & Hkind & Hlive & Hlen)]; [discriminate|].
rewrite Eb in Ebrk. injection Ebrk as <- <-.
eapply OK4_bind_y.
{ apply (OK4_ask_free (KBrkGrow 1) s (fun x => snd x = s)); [reflexivity | intros p; discriminate | intros b; reflexivity]. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear Hy1 RQ2.
destruct ok.
+ unfold upd_region. o_modify. o_modify. apply OK4_ret.
match goal with |- BrkPost _ (_, ?sx) => set (s2 := sx) end.
assert (Hnn : 0 <= rg_len rg) by (apply NN; eapply nth_error_In; exact Hrg).
destruct (upd_measures s s2 r (fun g => mkRegion RkBrk (rg_len g + PGSZ) [] true) rg eq_refl Hrg eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
assert (M8 : shift s2 = shift s) by reflexivity.
pose proof (upd_regs_nn s s2 r (fun g => mkRegion RkBrk (rg_len g + PGSZ) [] true) rg eq_refl Hrg NN ltac:(cbn; unfold PGSZ; lia)) as NN2.
unfold f_mapb, f_mapc, f_brkb, f_resvb, f_resvc, is_map, is_brk, is_resv in M1, M2, M3, M4, M5.
cbn [rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5. rewrite ?Hkind, ?Hlive in M1, M2, M3, M4, M5. rewrite ?Hkind, ?Hlive in M1. rewrite ?Hkind, ?Hlive in M2. rewrite ?Hkind, ?Hlive in M3. rewrite ?Hkind in M4. rewrite ?Hkind in M5. cbn [andb] in M1, M2, M3, M4, M5.
assert (EA : acnt s2 = 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
unfold BrkPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
unfold acnt in *. rewrite Ec1 in *. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2.
+ o_modify. apply OK4_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
Qed.
Lemma page_round_multiple k : 0 <= k -> page_round (k * PGSZ) = k * PGSZ.
Proof.
intros Hk. unfold page_round, PGSZ.
replace (k * 4096 + 4096 - 1) with (4095 + k * 4096) by lia.
rewrite Z.div_add by lia. cbn. lia.
Qed.
Lemma pow2_succ k : 0 <= k -> 2 ^ (k + 1) = 2 * 2 ^ k.
Proof. intros Hk. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. Qed.
Lemma shiftl2 k : 0 <= k -> Z.shiftl 2 k = 2 * 2 ^ k.
Proof. intros Hk. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Definition ROOMr (s : astate) : Prop :=
LIVE_UB s + area s + PGSZ <= MG_LIVE /\ SLOT_UB s + 2 <= MG_SLOTS /\ area s <= MG_REQ.
Definition MmapPost (s : astate) (r : bool * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' = map_bytes s /\ map_count s' = map_count s /\ hand s' = hand s /\ nareas s' = nareas s /\
amc s' = amc s /\ brk_bytes s' = brk_bytes s /\ shift s <= shift s' <= shift s + 1 /\
resv_total s' <= resv_total s + area s /\ resv_count s' <= resv_count s + 1 /\ acnt s <= acnt s' /\
(fst r = true -> 0 < acnt s').
Lemma MmapPost_meas s b s' : II s -> meas s' = meas s -> (b = true -> 0 < acnt s') -> MmapPost s (b, s').
Proof.
intros HII E Hb. pose proof (meas_eq_all _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
unfold MmapPost. cbn [fst snd]. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb2 & Hd & He).
split; [eapply meas_eq_II; eauto|].
assert (ERc : resv_count s' = resv_count s) by (unfold resv_count; unfold meas in E; congruence).
assert (ERt : resv_total s' = resv_total s) by (unfold resv_total; unfold meas in E; congruence).
assert (HA : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s)); lia).
unfold PGSZ in *. repeat split; try lia; auto.
Qed.
Lemma OK4_area_from_mmap s : reqs_ok (area_from_mmap s) -> II s -> amc s = 0 -> ROOMr s -> OK4 (MmapPost s) (area_from_mmap s).
Proof.
intros RQ HII Hamc0 (R1 & R2 & R3). pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
unfold area_from_mmap in RQ |- *. o_get. rq_get RQ.
match goal with |- OK4 _ ((if ?c then _ else _) _) => destruct c eqn:Ec end.
2:{ apply OK4_ret. apply MmapPost_meas; [exact HII | reflexivity |]. intros _. apply Z.eqb_neq in Ec. unfold acnt in *. lia. }
apply Z.eqb_eq in Ec. cbv zeta in RQ |- *.
assert (Hn : Z.shiftl 2 (st_meta_alloc_shift s) = 2 * 2 ^ shift s) by (apply shiftl2; exact Hsh).
assert (Hpos : 0 < 2 ^ shift s) by (apply Z.pow_pos_nonneg; lia).
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y.
{ apply (OK4_ask_room (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) s (fun x => snd x = s)); [ | intros p; discriminate | intros b; reflexivity].
cbn [mgrant req_len]. rewrite Hn. rewrite page_round_multiple by lia.
pose proof (LIVE_UB_ok s NN). pose proof (SLOT_UB_ok s NN). unfold area in *. unfold PGSZ in *. lia. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear Hy1 RQ2.
destruct ok.
- apply OK4_bind_new_region. o_modify. apply OK4_ret.
match goal with |- MmapPost _ (_, ?sx) => set (s2 := sx) end.
destruct (app_measures s s2 (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true) eq_refl eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
pose proof (app_regs_nn s s2 (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true) eq_refl NN ltac:(cbn [rg_len]; unfold PGSZ; lia)) as NN2.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5.
assert (M8 : shift s2 = shift s + 1) by reflexivity.
assert (EA : acnt s2 = Z.shiftl 2 (st_meta_alloc_shift s) - 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
rewrite ?Hn in M4. rewrite ?Hn in EA.
unfold MmapPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
rewrite !(pow2_succ (shift s + 1)) by lia. rewrite !(pow2_succ (shift s)) in * by lia.
unfold acnt, area in *. rewrite Ec in *. rewrite Hamc0 in *. unfold hand in *. rewrite Hamc0 in *.
unfold PGSZ, METAS_PER_AREA in *.
set (X := 2 ^ shift s) in *. clearbody X.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2.
- apply OK4_ret. apply MmapPost_meas; [exact HII | reflexivity | intros; discriminate].
Qed.
Lemma open_measures s1 s2 p :
st_regions s2 = st_regions s1 -> st_areas s2 = st_areas s1 ++ [p] -> amc s2 = METAS_PER_AREA ->
map_bytes s2 = map_bytes s1 /\ map_count s2 = map_count s1 /\ brk_bytes s2 = brk_bytes s1 /\
resv_total s2 = resv_total s1 /\ resv_count s2 = resv_count s1 /\ nareas s2 = nareas s1 + 1 /\
hand s2 = hand s1 + amc s1 /\ (regs_nn s1 -> regs_nn s2).
Proof.
intros ER EA EC. unfold map_bytes, map_count, brk_bytes, resv_count, resv_total, hand, nareas, regs_nn. rewrite ER, EA, EC, length_app.
cbn [length]. rewrite Nat2Z.inj_add. cbn. repeat split; try reflexivity; try lia. auto.
Qed.
Definition OpenPost (s : astate) (r : bool * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' = map_bytes s /\ map_count s' = map_count s /\ hand s' = hand s /\
brk_bytes s' = brk_bytes s /\ shift s' = shift s /\ resv_total s' = resv_total s /\ resv_count s' = resv_count s /\
(fst r = true -> amc s' = METAS_PER_AREA) /\ (fst r = false -> amc s' = amc s).
Lemma OK4_open_area nu s : reqs_ok (open_area nu s) -> II s -> amc s = 0 -> 0 < acnt s ->
LIVE_UB s + PGSZ <= MG_LIVE -> SLOT_UB s <= MG_SLOTS ->
OK4 (OpenPost s) (open_area nu s).
Proof.
intros RQ HII Hamc0 Hac0 RL RS. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
unfold open_area in RQ |- *. o_get. rq_get RQ. cbv zeta in RQ |- *.
rq_bind RQ RQ1 RQ2.
eapply (OK4_bind_y (fun x => snd x = s /\ (nu = true -> exists rg, region_of s (prid (st_avail_meta_areas s)) = Some rg /\ rg_kind rg = RkMetaRes /\ rg_live rg = true))).
{ destruct nu.
- pose proof (reqs_ok_ask_inv _ _ RQ1) as RK. cbn [req_ok] in RK. destruct RK as (_ & _ & rg & Hrg & Hk & Hl & _).
apply OK4_ask_room; [ | intros p; discriminate | intros b; split; [reflexivity | intros _; exists rg; auto]].
cbn [mgrant req_len]. pose proof (LIVE_UB_ok s NN). pose proof (SLOT_UB_ok s NN). unfold MG_REQ, PGSZ in *. lia.
- apply OK4_ret. split; [reflexivity | intros; discriminate]. }
intros ok s1 tr1 Hy1 [E1 Hreg]. cbn [snd] in E1. subst s1.
destruct ok; cbn [negb].
2:{ apply OK4_ret. unfold OpenPost. cbn [fst snd]. repeat split; auto; try lia. }
match goal with |- OK4 _ (bind ?m (fun _ => bind (modify ?F) _) s) =>
eapply (OK4_bind_y (fun x => msr (snd x) = msr s /\ regs_nn (snd x) /\ st_areas (snd x) = st_areas s /\ st_avail_meta_area_count (snd x) = st_avail_meta_area_count s)) end.
{ destruct nu.
- destruct (Hreg eq_refl) as (rg & Hrg & Hk & Hl).
unfold upd_region. apply OK4_modify. cbn [snd].
match goal with |- msr ?sx = _ /\ _ => set (s1 := sx) end.
destruct (upd_measures s s1 (prid (st_avail_meta_areas s)) (fun g => mkRegion (rg_kind g) (rg_len g) (rg_rw g ++ [poff (st_avail_meta_areas s)]) (rg_live g)) rg eq_refl Hrg eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
unfold f_mapb, f_mapc, f_brkb, f_resvb, f_resvc, is_map, is_brk, is_resv in M1, M2, M3, M4, M5. cbn [rg_kind rg_len rg_live] in M1, M2, M3, M4, M5.
split; [|split; [|split; reflexivity]].
+ unfold msr. rewrite M1, M2, M3, M4, M5, M6, M7. unfold shift, acnt. cbn. repeat (f_equal || reflexivity); lia.
+ apply (upd_regs_nn s s1 (prid (st_avail_meta_areas s)) (fun g => mkRegion (rg_kind g) (rg_len g) (rg_rw g ++ [poff (st_avail_meta_areas s)]) (rg_live g)) rg eq_refl Hrg NN). cbn [rg_len]. apply NN. eapply nth_error_In. exact Hrg.
- apply OK4_ret. cbn [snd]. repeat split; try reflexivity. exact NN. }
intros u s1 tr2 Hy2 (Em & NN1 & Ea1 & Ec1). cbn [snd] in Em, NN1, Ea1, Ec1.
o_modify. apply OK4_ret.
match goal with |- OpenPost _ (_, ?sx) => set (s2 := sx) end.
destruct (open_measures s1 s2 (st_avail_meta_areas s) eq_refl eq_refl eq_refl) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
assert (Esh : shift s2 = shift s1) by reflexivity. assert (Eac : acnt s2 = acnt s1 - 1) by (unfold acnt; cbn; rewrite Ec1; reflexivity).
assert (Eam : amc s2 = METAS_PER_AREA) by reflexivity.
unfold msr in Em. injection Em as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
unfold OpenPost, II. cbn [fst snd].
rewrite !N1, !N2, !N3, !N4, !N5, !N6, !N7, !Esh, !Eac, !Eam, !E1, !E2, !E3, !E4, !E5, !E6, !E7, !E8, !E9, !E10.
rewrite Hamc0. unfold acnt in *. unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto; try (intros; discriminate).
Qed.
Ltac o_ret := match goal with |- OK4 ?P (bind (ret ?a) ?k ?s0) => change (OK4 P (k a s0)); cbv beta end.
Ltac rq_ret H := match type of H with reqs_ok (bind (ret ?a) ?k ?s0) => change (reqs_ok (k a s0)) in H; cbv beta in H end.
Lemma divP_le a b k : a <= b + k * PGSZ -> a / PGSZ <= b / PGSZ + k.
Proof.
intros H. apply Z.le_trans with ((b + k * PGSZ) / PGSZ).
- apply Z.div_le_mono; [unfold PGSZ; lia | exact H].
- rewrite Z_div_plus; [lia | unfold PGSZ; lia].
Qed.
Definition area_route : M bool :=
nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false.
Definition RoutePost (s : astate) (r : bool * astate) : Prop :=
let s' := snd r in
II s' /\ map_bytes s' = map_bytes s /\ map_count s' = map_count s /\ hand s' = hand s /\
shift s <= shift s' <= shift s + 1 /\ brk_bytes s' <= brk_bytes s + 2 * PGSZ /\
(fst r = true -> amc s' = METAS_PER_AREA) /\ (fst r = false -> amc s' = amc s) /\
LIVE_UB s' <= LIVE_UB s + 2 * PGSZ + area s /\ SLOT_UB s' <= SLOT_UB s + 3.
Lemma OK4_area_route s : reqs_ok (area_route s) -> II s -> amc s = 0 -> ROOMm s -> OK4 (RoutePost s) (area_route s).
Proof.
intros RQ HII Hamc0 (R1 & R2 & R3). pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
unfold area_route in RQ |- *. rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y; [apply OK4_area_from_brk; [exact RQ1 | exact HII]|].
intros nu s1 tr1 Hy1 HP1. specialize (RQ2 tr1 nu s1 Hy1). clear RQ1 Hy1.
unfold BrkPost in HP1. cbn [fst snd] in HP1. destruct HP1 as (II1 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof II1 as (NN1 & _).
rq_bind RQ2 RQ3 RQ4.
assert (HL1 : LIVE_UB s1 <= LIVE_UB s + 2 * PGSZ) by (unfold LIVE_UB; lia).
assert (HS1 : SLOT_UB s1 <= SLOT_UB s + 2).
{ unfold SLOT_UB. pose proof (divP_le (brk_bytes s1) (brk_bytes s) 2 ltac:(lia)). lia. }
assert (EA1 : area s1 = area s) by (unfold area; rewrite B4; reflexivity).
eapply OK4_bind_y; [apply OK4_area_from_mmap; [exact RQ3 | exact II1 | lia | ]|].
{ unfold ROOMr. rewrite EA1. unfold area in *. lia. }
intros rs s2 tr2 Hy2 HP2. specialize (RQ4 tr2 rs s2 Hy2). clear RQ3 Hy2.
unfold MmapPost in HP2. cbn [fst snd] in HP2. destruct HP2 as (II2 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
pose proof II2 as (NN2 & _).
assert (HL2 : LIVE_UB s2 <= LIVE_UB s1 + area s1) by (unfold LIVE_UB; lia).
assert (HS2 : SLOT_UB s2 <= SLOT_UB s1 + 1) by (unfold SLOT_UB; rewrite C6; lia).
assert (HA : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s)); lia).
destruct rs.
-
eapply OK4_mono; [| apply OK4_open_area; [exact RQ4 | exact II2 | lia | apply C11; reflexivity | rewrite EA1 in HL2; unfold area in *; lia | lia]].
intros [ok s3] HP3. unfold OpenPost in HP3. cbn [fst snd] in HP3. destruct HP3 as (II3 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
assert (HL3 : LIVE_UB s3 = LIVE_UB s2) by (unfold LIVE_UB; rewrite D1, D4, D6; reflexivity).
assert (HS3 : SLOT_UB s3 = SLOT_UB s2) by (unfold SLOT_UB; rewrite D2, D4, D7; reflexivity).
rewrite EA1 in HL2.
unfold RoutePost. cbn [fst snd]. unfold PGSZ in *. repeat match goal with |- _ /\ _ => split end; try lia; auto.
all: intros Hf; first [rewrite (D9 Hf) | rewrite (D8 Hf)]; lia.
- rewrite EA1 in HL2. apply OK4_ret. unfold RoutePost. cbn [fst snd]. unfold PGSZ in *. repeat match goal with |- _ /\ _ => split end; try lia; auto.
all: intros; try discriminate; lia.
Qed.
Lemma OK4_frame_meas {A} (m : M A) s : presK m -> presC m -> OK4 (fun r => meas (snd r) = meas s) (m s).
Proof. apply OK4_frame. Qed.
Theorem OK4_alloc_meta s : reqs_ok (alloc_meta s) -> II s -> (amc s = 0 -> ROOMm s) -> OK4 (MetaPost s) (alloc_meta s).
Proof.
intros RQ HII HR. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He).
assert (HA0 : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s)); lia).
unfold alloc_meta in RQ |- *. o_modify. rq_modify RQ.
set (s0 := set_init_done true s) in *.
assert (E0 : meas s0 = meas s) by reflexivity.
rq_bind RQ RQ1 RQ2.
eapply OK4_bind_y; [apply (OK4_frame_meas (dequeue_head HFreeMeta) s0); auto with presK presC|].
intros fm s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 fm s1 Hy1). clear RQ1 Hy1.
assert (E1' : meas s1 = meas s) by (rewrite E1; exact E0).
pose proof (meas_eq_all _ _ E1') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E1' HII) as II1.
destruct fm as [m|].
{
apply OK4_ret. unfold MetaPost. cbn [fst snd]. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q9, Q10. unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto. }
o_get. rq_get RQ2. rq_bind RQ2 RQ3 RQ4.
assert (TAIL : forall s2, II s2 -> map_bytes s2 = map_bytes s -> map_count s2 = map_count s -> hand s2 = hand s ->
shift s <= shift s2 <= shift s + 1 -> brk_bytes s2 <= brk_bytes s + 2 * PGSZ -> 0 < amc s2 ->
(amc s2 = amc s \/ amc s2 = METAS_PER_AREA) ->
(0 < amc s -> LIVE_UB s2 <= LIVE_UB s /\ SLOT_UB s2 <= SLOT_UB s /\ shift s2 = shift s /\ brk_bytes s2 = brk_bytes s) ->
((LIVE_UB s2 <= LIVE_UB s /\ SLOT_UB s2 <= SLOT_UB s /\ shift s2 = shift s /\ brk_bytes s2 = brk_bytes s) \/ amc s2 = METAS_PER_AREA) ->
LIVE_UB s2 <= LIVE_UB s + 2 * PGSZ + area s -> SLOT_UB s2 <= SLOT_UB s + 4 ->
OK4 (MetaPost s)
((s3 <- get ;;
put (set_avail_meta (padd (st_avail_meta s3) META_SIZE) (set_avail_meta_count (st_avail_meta_count s3 - 1) s3)) ;;
setslot (st_avail_meta s3) MRaw ;; ret (Some (st_avail_meta s3))) s2)).
{ intros s2 II2 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11. o_get. o_put.
match goal with |- OK4 _ (bind _ _ ?sx) => set (s3 := sx) end.
eapply OK4_bind_y; [apply (OK4_frame_meas (setslot (st_avail_meta s2) MRaw) s3); auto with presK presC|].
intros u s4 tr4 Hy4 E4. cbn [snd] in E4. apply OK4_ret.
pose proof II2 as (NN2 & Hsh2 & Hac2 & Hamc2 & Hrt2 & Hrc2 & Hb2 & Hd2 & He2).
assert (F1 : map_bytes s3 = map_bytes s2) by reflexivity. assert (F2 : map_count s3 = map_count s2) by reflexivity.
assert (F3 : brk_bytes s3 = brk_bytes s2) by reflexivity. assert (F4 : resv_total s3 = resv_total s2) by reflexivity.
assert (F5 : resv_count s3 = resv_count s2) by reflexivity. assert (F6 : nareas s3 = nareas s2) by reflexivity.
assert (F7 : hand s3 = hand s2 + 1) by (unfold hand, nareas; cbn -[Z.mul Z.sub Z.add METAS_PER_AREA]; lia).
assert (F8 : shift s3 = shift s2) by reflexivity. assert (F9 : acnt s3 = acnt s2) by reflexivity.
assert (F10 : amc s3 = amc s2 - 1) by reflexivity.
assert (F11 : LIVE_UB s3 = LIVE_UB s2) by reflexivity. assert (F12 : SLOT_UB s3 = SLOT_UB s2) by reflexivity.
pose proof (meas_eq_all _ _ E4) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
assert (ERc : resv_count s4 = resv_count s3) by (unfold resv_count; unfold meas in E4; congruence).
assert (ERt : resv_total s4 = resv_total s3) by (unfold resv_total; unfold meas in E4; congruence).
assert (NN4 : regs_nn s4).
{ unfold regs_nn. unfold meas in E4. assert (R : st_regions s4 = st_regions s3) by congruence. rewrite R. exact NN2. }
unfold MetaPost, II. cbn [fst snd].
rewrite !P1, !P2, !P3, !P4, !P5, !P6, !P7, !P8, !P9, !P10, !ERc, !ERt, !F1, !F2, !F3, !F4, !F5, !F6, !F7, !F8, !F9, !F10, !F11, !F12.
unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto. }
destruct (0 <? amc s1) eqn:Eamc.
-
o_ret. cbn [negb]. apply Z.ltb_lt in Eamc.
apply TAIL; try assumption; try (unfold PGSZ in *; lia).
-
apply Z.ltb_ge in Eamc. assert (Hamc0 : amc s1 = 0) by lia.
change (OK4 (MetaPost s) (bind area_route (fun ok => if negb ok then ret None else
(s3 <- get ;; put (set_avail_meta (padd (st_avail_meta s3) META_SIZE) (set_avail_meta_count (st_avail_meta_count s3 - 1) s3)) ;;
setslot (st_avail_meta s3) MRaw ;; ret (Some (st_avail_meta s3)))) s1)).
change (reqs_ok (area_route s1)) in RQ3.
assert (HR1 : ROOMm s1) by (unfold ROOMm in *; rewrite Q4, Q9, Q10; apply HR; rewrite <- Q6; exact Hamc0).
eapply OK4_bind_y; [apply OK4_area_route; [exact RQ3 | exact II1 | exact Hamc0 | exact HR1]|].
intros ok s2 tr2 Hy2 HP2. unfold RoutePost in HP2. cbn [fst snd] in HP2. destruct HP2 as (II2 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
rewrite Q9 in G8. rewrite Q10 in G9. unfold area in G8. rewrite Q4 in G8. fold (area s) in G8.
destruct ok; cbn [negb].
+ apply TAIL; try assumption; try (unfold PGSZ in *; lia); try (rewrite (G6 eq_refl); unfold METAS_PER_AREA; lia); try (right; apply G6; reflexivity).
all: try (intros Hpos; exfalso; rewrite <- Q6 in Hpos; lia).
+ apply OK4_ret. unfold MetaPost. cbn [fst snd]. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto; try (intros H; exfalso; apply H; reflexivity).
all: try (intros Hpos; exfalso; rewrite <- Q6 in Hpos; lia).
Qed.
End d.
