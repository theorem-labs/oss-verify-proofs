(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0m.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import
YO0i YO0f YO0g YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0d_cf YO03_cf YO0j_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import PlaceCapW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require AgreeLim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation amc s := (st_avail_meta_count s).
Definition ROOMmX (X : Z) (s : astate) : Prop := LIVE_UB s + 2 * PGSZ + 2 * PGSZ * 2 ^ shift s + PGSZ <= X /\
(X <= AgreeLim.LIM_AG -> SLOT_UB s + 4 + KRES <= slot_capW (2 * PGSZ * 2 ^ shift s) /\ 2 * PGSZ * 2 ^ shift s <= MG_REQ).
Definition ROOMrX (X : Z) (s : astate) : Prop :=
X <= AgreeLim.LIM_AG -> LIVE_UB s <= X /\ SLOT_UB s + 2 + KRES <= slot_capW (area s) /\ area s <= MG_REQ.
Lemma OKC_frame_meas {A} X (m : M A) s : presK m -> presC m -> presR m -> OKC X (fun r => meas (snd r) = meas s) (m s).
Proof using. intros HK HC HR. split; [exact (HR X s) | exact (proj2 (OK4_frame m s HK HC))]. Qed.
Lemma OKC_bind_new_region {B} X k len s (K : nat -> M B) Q :
OKC X Q (K (length (st_regions s)) (set_regions (st_regions s ++ [mkRegion k len [] true]) s)) ->
OKC X Q (bind (new_region k len) K s).
Proof using. intros H. exact H. Qed.
Lemma OKC_area_from_brk X s : reqs_ok (area_from_brk s) -> II s -> LIVE_UB s + 2 * PGSZ <= X -> OKC X (BrkPost s) (area_from_brk s).
Proof using.
intros RQ HII RX. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He & ML).
pose proof (LIVE_UB_ok s NN) as HLv.
unfold area_from_brk in RQ |- *. x_get. rq_get RQ.
match goal with |- OKC _ _ ((if ?c then _ else _) _) => destruct c eqn:Ec end.
2:{ apply OKC_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate]. }
apply andb_prop in Ec as [Ec1 Ec2]. apply Z.eqb_eq in Ec1.
destruct (st_brk s) as [ | | r pages] eqn:Eb.
-
rq_bind RQ RQ1 RQ2. eapply OKC_bind_y.
{ apply (OKC_ask_free X KBrkQuery s (fun r => snd r = s)); [reflexivity | reflexivity | intros b; reflexivity]. }
intros b1 s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear RQ1 RQ2 Hy1.
eapply OKC_bind_y.
{ apply (OKC_ask_room X (KBrkGrow 2) s (fun r => snd r = s)); [ | intros E; discriminate E | intros b; reflexivity].
intros _. cbn [req_len]. unfold PGSZ in *. lia. }
intros ok s1 tr2 Hy2 E2. cbn [snd] in E2. subst s1. clear Hy2.
destruct ok.
+
apply OKC_bind_new_region. x_modify.
match goal with |- OKC _ _ (bind _ _ ?sx) => set (s2 := sx) end.
eapply OKC_bind_y.
{ apply (OKC_ask_free X KGuard s2 (fun r => snd r = s2)); [reflexivity | reflexivity | intros b; reflexivity]. }
intros b3 s3 tr3 Hy3 E3. cbn [snd] in E3. subst s3. apply OKC_ret.
destruct (app_measures s s2 (mkRegion RkBrk (2 * PGSZ) [] true) eq_refl eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
assert (M8 : shift s2 = shift s) by reflexivity.
pose proof (app_regs_nn s s2 (mkRegion RkBrk (2 * PGSZ) [] true) eq_refl NN ltac:(cbn; unfold PGSZ; lia)) as NN2.
pose proof (maps_le_app s s2 (mkRegion RkBrk (2 * PGSZ) [] true) eq_refl ML ltac:(unfold f_mapb, is_map, MG_REQ; cbn; lia)) as ML2.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5.
assert (EA : acnt s2 = 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
unfold BrkPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
unfold acnt in *. rewrite Ec1 in *. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2; try exact ML2.
+ x_modify. apply OKC_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
-   apply OKC_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
-
rq_bind RQ RQ1 RQ2. pose proof (reqs_ok_ask_inv _ _ RQ1) as RK. cbn [req_ok] in RK.
destruct RK as [(E & _) | (_ & r' & p' & rg & Ebrk & Hrg & Hkind & Hlive & Hlen)]; [discriminate|].
rewrite Eb in Ebrk. injection Ebrk as <- <-.
eapply OKC_bind_y.
{ apply (OKC_ask_room X (KBrkGrow 1) s (fun x => snd x = s)); [ | intros E; discriminate E | intros b; reflexivity].
intros _. cbn [req_len]. unfold PGSZ in *. lia. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear Hy1 RQ2.
destruct ok.
+ unfold upd_region. x_modify. x_modify. apply OKC_ret.
match goal with |- BrkPost _ (_, ?sx) => set (s2 := sx) end.
assert (Hnn : 0 <= rg_len rg) by (apply NN; eapply nth_error_In; exact Hrg).
destruct (upd_measures s s2 r (fun g => mkRegion RkBrk (rg_len g + PGSZ) [] true) rg eq_refl Hrg eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
assert (M8 : shift s2 = shift s) by reflexivity.
pose proof (upd_regs_nn s s2 r (fun g => mkRegion RkBrk (rg_len g + PGSZ) [] true) rg eq_refl Hrg NN ltac:(cbn; unfold PGSZ; lia)) as NN2.
pose proof (maps_le_upd s s2 r (fun g => mkRegion RkBrk (rg_len g + PGSZ) [] true) rg eq_refl Hrg ML ltac:(unfold f_mapb, is_map, MG_REQ; cbn; lia)) as ML2.
unfold f_mapb, f_mapc, f_brkb, f_resvb, f_resvc, is_map, is_brk, is_resv in M1, M2, M3, M4, M5.
cbn [rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5. rewrite ?Hkind, ?Hlive in M1, M2, M3, M4, M5. rewrite ?Hkind, ?Hlive in M1. rewrite ?Hkind, ?Hlive in M2. rewrite ?Hkind, ?Hlive in M3. rewrite ?Hkind in M4. rewrite ?Hkind in M5. cbn [andb] in M1, M2, M3, M4, M5.
assert (EA : acnt s2 = 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
unfold BrkPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
unfold acnt in *. rewrite Ec1 in *. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2; try exact ML2.
+ x_modify. apply OKC_ret. apply BrkPost_meas; [exact HII | reflexivity | intros; discriminate].
Qed.
Lemma OKC_area_from_mmap X s : reqs_ok (area_from_mmap s) -> II s -> amc s = 0 -> ROOMrX X s -> OKC X (MmapPost s) (area_from_mmap s).
Proof using.
intros RQ HII Hamc0 RR. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He & ML).
unfold area_from_mmap in RQ |- *. x_get. rq_get RQ.
match goal with |- OKC _ _ ((if ?c then _ else _) _) => destruct c eqn:Ec end.
2:{ apply OKC_ret. apply MmapPost_meas; [exact HII | reflexivity |]. intros _. apply Z.eqb_neq in Ec. unfold acnt in *. lia. }
apply Z.eqb_eq in Ec. cbv zeta in RQ |- *.
assert (Hn : Z.shiftl 2 (st_meta_alloc_shift s) = 2 * 2 ^ shift s) by (apply shiftl2; exact Hsh).
assert (Hpos : 0 < 2 ^ shift s) by (apply Z.pow_pos_nonneg; lia).
rq_bind RQ RQ1 RQ2.
eapply OKC_bind_y.
{ apply (OKC_ask_room X (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) s (fun x => snd x = s)); [intros E; discriminate E | | intros b; reflexivity].
intros _ HXl. destruct (RR HXl) as (R1 & R2 & R3). unfold slot_room. cbn [req_len]. rewrite Hn. rewrite page_round_multiple by lia.
pose proof (LIVE_UB_ok s NN). pose proof (SLOT_UB_ok s NN).
assert (HC : slot_capW (area s) <= slot_capW (2 * 2 ^ shift s * PGSZ)) by (apply slot_capW_anti; unfold area, PGSZ; lia).
unfold area in *. unfold PGSZ in *. lia. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. clear Hy1 RQ2.
destruct ok.
- apply OKC_bind_new_region. x_modify. apply OKC_ret.
match goal with |- MmapPost _ (_, ?sx) => set (s2 := sx) end.
destruct (app_measures s s2 (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true) eq_refl eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
pose proof (app_regs_nn s s2 (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true) eq_refl NN ltac:(cbn [rg_len]; unfold PGSZ; lia)) as NN2.
pose proof (maps_le_app s s2 (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true) eq_refl ML ltac:(unfold f_mapb, is_map, MG_REQ; cbn; lia)) as ML2.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in M1, M2, M3, M4, M5.
assert (M8 : shift s2 = shift s + 1) by reflexivity.
assert (EA : acnt s2 = Z.shiftl 2 (st_meta_alloc_shift s) - 1) by reflexivity. assert (EM : amc s2 = amc s) by reflexivity.
rewrite ?Hn in M4. rewrite ?Hn in EA.
unfold MmapPost, II. cbn [fst snd]. rewrite !M1, !M2, !M3, !M4, !M5, !M6, !M7, !M8, !EA, !EM.
rewrite !(pow2_succ (shift s + 1)) by lia. rewrite !(pow2_succ (shift s)) in * by lia.
unfold acnt, area in *. rewrite Ec in *. rewrite Hamc0 in *. unfold hand in *. rewrite Hamc0 in *.
unfold PGSZ, METAS_PER_AREA in *.
set (W := 2 ^ shift s) in *. clearbody W.
repeat match goal with |- _ /\ _ => split end; try lia; try exact NN2; try exact ML2.
- apply OKC_ret. apply MmapPost_meas; [exact HII | reflexivity | intros; discriminate].
Qed.
Lemma OKC_open_area X nu s : reqs_ok (open_area nu s) -> II s -> amc s = 0 -> 0 < acnt s ->
LIVE_UB s + PGSZ <= X -> OKC X (OpenPost s) (open_area nu s).
Proof using.
intros RQ HII Hamc0 Hac0 RL. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He & ML).
unfold open_area in RQ |- *. x_get. rq_get RQ. cbv zeta in RQ |- *.
rq_bind RQ RQ1 RQ2.
eapply (OKC_bind_y X (fun x => snd x = s /\ (nu = true -> exists rg, region_of s (prid (st_avail_meta_areas s)) = Some rg /\ rg_kind rg = RkMetaRes /\ rg_live rg = true))).
{ destruct nu.
- pose proof (reqs_ok_ask_inv _ _ RQ1) as RK. cbn [req_ok] in RK. destruct RK as (_ & _ & rg & Hrg & Hk & Hl & _).
apply OKC_ask_room; [ | intros E; discriminate E | intros b; split; [reflexivity | intros _; exists rg; auto]].
intros _. cbn [req_len]. pose proof (LIVE_UB_ok s NN). lia.
- apply OKC_ret. split; [reflexivity | intros; discriminate]. }
intros ok s1 tr1 Hy1 [E1 Hreg]. cbn [snd] in E1. subst s1.
destruct ok; cbn [negb].
2:{ apply OKC_ret. unfold OpenPost. cbn [fst snd]. repeat split; auto; try lia. }
match goal with |- OKC _ _ (bind ?m (fun _ => bind (modify ?F) _) s) =>
eapply (OKC_bind_y X (fun x => msr (snd x) = msr s /\ regs_nn (snd x) /\ maps_le (snd x) /\ st_areas (snd x) = st_areas s /\ st_avail_meta_area_count (snd x) = st_avail_meta_area_count s)) end.
{ destruct nu.
- destruct (Hreg eq_refl) as (rg & Hrg & Hk & Hl).
unfold upd_region. apply OKC_modify. cbn [snd].
match goal with |- msr ?sx = _ /\ _ => set (s1 := sx) end.
destruct (upd_measures s s1 (prid (st_avail_meta_areas s)) (fun g => mkRegion (rg_kind g) (rg_len g) (rg_rw g ++ [poff (st_avail_meta_areas s)]) (rg_live g)) rg eq_refl Hrg eq_refl eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
unfold f_mapb, f_mapc, f_brkb, f_resvb, f_resvc, is_map, is_brk, is_resv in M1, M2, M3, M4, M5. cbn [rg_kind rg_len rg_live] in M1, M2, M3, M4, M5.
split; [|split; [|split; [|split; reflexivity]]].
+ unfold msr. rewrite M1, M2, M3, M4, M5, M6, M7. unfold shift, acnt. cbn. repeat (f_equal || reflexivity); lia.
+ apply (upd_regs_nn s s1 (prid (st_avail_meta_areas s)) (fun g => mkRegion (rg_kind g) (rg_len g) (rg_rw g ++ [poff (st_avail_meta_areas s)]) (rg_live g)) rg eq_refl Hrg NN). cbn [rg_len]. apply NN. eapply nth_error_In. exact Hrg.
+ apply (maps_le_upd s s1 (prid (st_avail_meta_areas s)) (fun g => mkRegion (rg_kind g) (rg_len g) (rg_rw g ++ [poff (st_avail_meta_areas s)]) (rg_live g)) rg eq_refl Hrg ML). exact (ML rg (nth_error_In _ _ Hrg)).
- apply OKC_ret. cbn [snd]. repeat split; try reflexivity. exact NN. exact ML. }
intros u s1 tr2 Hy2 (Em & NN1 & ML1 & Ea1 & Ec1). cbn [snd] in Em, NN1, ML1, Ea1, Ec1.
x_modify. apply OKC_ret.
match goal with |- OpenPost _ (_, ?sx) => set (s2 := sx) end.
destruct (open_measures s1 s2 (st_avail_meta_areas s) eq_refl eq_refl eq_refl) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
assert (ML2 : maps_le s2) by exact ML1.
assert (Esh : shift s2 = shift s1) by reflexivity. assert (Eac : acnt s2 = acnt s1 - 1) by (unfold acnt; cbn; rewrite Ec1; reflexivity).
assert (Eam : amc s2 = METAS_PER_AREA) by reflexivity.
unfold msr in Em. injection Em as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
unfold OpenPost, II. cbn [fst snd].
rewrite !N1, !N2, !N3, !N4, !N5, !N6, !N7, !Esh, !Eac, !Eam, !E1, !E2, !E3, !E4, !E5, !E6, !E7, !E8, !E9, !E10.
rewrite Hamc0. unfold acnt in *. unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto; try (intros; discriminate).
Qed.
Lemma OKC_area_route X s : reqs_ok (area_route s) -> II s -> amc s = 0 -> ROOMmX X s -> OKC X (RoutePost s) (area_route s).
Proof using.
intros RQ HII Hamc0 [R1 RS]. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He & ML).
assert (HA : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s)); lia).
unfold area_route in RQ |- *. rq_bind RQ RQ1 RQ2.
eapply OKC_bind_y; [apply OKC_area_from_brk; [exact RQ1 | exact HII | unfold area, PGSZ in *; lia]|].
intros nu s1 tr1 Hy1 HP1. specialize (RQ2 tr1 nu s1 Hy1). clear RQ1 Hy1.
unfold BrkPost in HP1. cbn [fst snd] in HP1. destruct HP1 as (II1 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof II1 as (NN1 & _).
rq_bind RQ2 RQ3 RQ4.
assert (HL1 : LIVE_UB s1 <= LIVE_UB s + 2 * PGSZ) by (unfold LIVE_UB; lia).
assert (HS1 : SLOT_UB s1 <= SLOT_UB s + 2).
{ unfold SLOT_UB. pose proof (divP_le (brk_bytes s1) (brk_bytes s) 2 ltac:(lia)). lia. }
assert (EA1 : area s1 = area s) by (unfold area; rewrite B4; reflexivity).
eapply OKC_bind_y; [apply OKC_area_from_mmap; [exact RQ3 | exact II1 | lia | ]|].
{ intros HXl. destruct (RS HXl) as (RS1 & RS2). rewrite EA1. unfold area in *. unfold PGSZ in *. lia. }
intros rs s2 tr2 Hy2 HP2. specialize (RQ4 tr2 rs s2 Hy2). clear RQ3 Hy2.
unfold MmapPost in HP2. cbn [fst snd] in HP2. destruct HP2 as (II2 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
pose proof II2 as (NN2 & _).
assert (HL2 : LIVE_UB s2 <= LIVE_UB s1 + area s1) by (unfold LIVE_UB; lia).
assert (HS2 : SLOT_UB s2 <= SLOT_UB s1 + 1) by (unfold SLOT_UB; rewrite C6; lia).
destruct rs.
-
eapply OKC_mono; [| apply OKC_open_area; [exact RQ4 | exact II2 | lia | apply C11; reflexivity | rewrite EA1 in HL2; unfold area, PGSZ in *; lia]].
intros [ok s3] HP3. unfold OpenPost in HP3. cbn [fst snd] in HP3. destruct HP3 as (II3 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
assert (HL3 : LIVE_UB s3 = LIVE_UB s2) by (unfold LIVE_UB; rewrite D1, D4, D6; reflexivity).
assert (HS3 : SLOT_UB s3 = SLOT_UB s2) by (unfold SLOT_UB; rewrite D2, D4, D7; reflexivity).
rewrite EA1 in HL2.
unfold RoutePost. cbn [fst snd]. unfold PGSZ in *. repeat match goal with |- _ /\ _ => split end; try lia; auto.
all: intros Hf; first [rewrite (D9 Hf) | rewrite (D8 Hf)]; lia.
- rewrite EA1 in HL2. apply OKC_ret. unfold RoutePost. cbn [fst snd]. unfold PGSZ in *. repeat match goal with |- _ /\ _ => split end; try lia; auto.
all: intros; try discriminate; lia.
Qed.
Theorem OKC_alloc_meta X s : reqs_ok (alloc_meta s) -> II s -> (amc s = 0 -> ROOMmX X s) -> OKC X (MetaPost s) (alloc_meta s).
Proof using.
intros RQ HII HR. pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & Hb & Hd & He & ML).
assert (HA0 : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s)); lia).
unfold alloc_meta in RQ |- *. x_modify. rq_modify RQ.
set (s0 := set_init_done true s) in *.
assert (E0 : meas s0 = meas s) by reflexivity.
rq_bind RQ RQ1 RQ2.
eapply OKC_bind_y; [apply (OKC_frame_meas X (dequeue_head HFreeMeta) s0); auto with presK presC presR|].
intros fm s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 fm s1 Hy1). clear RQ1 Hy1.
assert (E1' : meas s1 = meas s) by (rewrite E1; exact E0).
pose proof (meas_eq_all _ _ E1') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E1' HII) as II1.
destruct fm as [m|].
{
apply OKC_ret. unfold MetaPost. cbn [fst snd]. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q9, Q10. unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto. }
x_get. rq_get RQ2. rq_bind RQ2 RQ3 RQ4.
assert (TAIL : forall s2, II s2 -> map_bytes s2 = map_bytes s -> map_count s2 = map_count s -> hand s2 = hand s ->
shift s <= shift s2 <= shift s + 1 -> brk_bytes s2 <= brk_bytes s + 2 * PGSZ -> 0 < amc s2 ->
(amc s2 = amc s \/ amc s2 = METAS_PER_AREA) ->
(0 < amc s -> LIVE_UB s2 <= LIVE_UB s /\ SLOT_UB s2 <= SLOT_UB s /\ shift s2 = shift s /\ brk_bytes s2 = brk_bytes s) ->
((LIVE_UB s2 <= LIVE_UB s /\ SLOT_UB s2 <= SLOT_UB s /\ shift s2 = shift s /\ brk_bytes s2 = brk_bytes s) \/ amc s2 = METAS_PER_AREA) ->
LIVE_UB s2 <= LIVE_UB s + 2 * PGSZ + area s -> SLOT_UB s2 <= SLOT_UB s + 4 ->
OKC X (MetaPost s)
((s3 <- get ;;
put (set_avail_meta (padd (st_avail_meta s3) META_SIZE) (set_avail_meta_count (st_avail_meta_count s3 - 1) s3)) ;;
setslot (st_avail_meta s3) MRaw ;; ret (Some (st_avail_meta s3))) s2)).
{ intros s2 II2 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11. x_get. x_put.
match goal with |- OKC _ _ (bind _ _ ?sx) => set (s3 := sx) end.
eapply OKC_bind_y; [apply (OKC_frame_meas X (setslot (st_avail_meta s2) MRaw) s3); auto with presK presC presR|].
intros u s4 tr4 Hy4 E4. cbn [snd] in E4. apply OKC_ret.
pose proof II2 as (NN2 & Hsh2 & Hac2 & Hamc2 & Hrt2 & Hrc2 & Hb2 & Hd2 & He2 & ML2).
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
assert (ML4 : maps_le s4).
{ unfold maps_le. unfold meas in E4. assert (R : st_regions s4 = st_regions s3) by congruence. rewrite R. exact ML2. }
unfold MetaPost, II. cbn [fst snd].
rewrite !P1, !P2, !P3, !P4, !P5, !P6, !P7, !P8, !P9, !P10, !ERc, !ERt, !F1, !F2, !F3, !F4, !F5, !F6, !F7, !F8, !F9, !F10, !F11, !F12.
unfold PGSZ, METAS_PER_AREA in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto. }
destruct (0 <? amc s1) eqn:Eamc.
-
x_ret. cbn [negb]. apply Z.ltb_lt in Eamc.
apply TAIL; try assumption; try (unfold PGSZ in *; lia).
-
apply Z.ltb_ge in Eamc. assert (Hamc0 : amc s1 = 0) by lia.
change (OKC X (MetaPost s) (bind area_route (fun ok => if negb ok then ret None else
(s3 <- get ;; put (set_avail_meta (padd (st_avail_meta s3) META_SIZE) (set_avail_meta_count (st_avail_meta_count s3 - 1) s3)) ;;
setslot (st_avail_meta s3) MRaw ;; ret (Some (st_avail_meta s3)))) s1)).
change (reqs_ok (area_route s1)) in RQ3.
assert (HR1 : ROOMmX X s1) by (unfold ROOMmX in *; rewrite Q4, Q9, Q10; apply HR; rewrite <- Q6; exact Hamc0).
eapply OKC_bind_y; [apply OKC_area_route; [exact RQ3 | exact II1 | exact Hamc0 | exact HR1]|].
intros ok s2 tr2 Hy2 HP2. unfold RoutePost in HP2. cbn [fst snd] in HP2. destruct HP2 as (II2 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
rewrite Q9 in G8. rewrite Q10 in G9. unfold area in G8. rewrite Q4 in G8. fold (area s) in G8.
destruct ok; cbn [negb].
+ apply TAIL; try assumption; try (unfold PGSZ in *; lia); try (rewrite (G6 eq_refl); unfold METAS_PER_AREA; lia); try (right; apply G6; reflexivity).
all: try (intros Hpos; exfalso; rewrite <- Q6 in Hpos; lia).
+ apply OKC_ret. unfold MetaPost. cbn [fst snd]. unfold PGSZ in *.
repeat match goal with |- _ /\ _ => split end; try lia; auto; try (intros H; exfalso; apply H; reflexivity).
all: try (intros Hpos; exfalso; rewrite <- Q6 in Hpos; lia).
Qed.
End d.
