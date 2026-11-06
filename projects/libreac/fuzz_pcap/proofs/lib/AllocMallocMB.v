(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YO0v.v; 1277 of its 1541 lines of code are new or changed and 706 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocMalloc.v, with its module paths and module names changed; 395 of its 504 lines of code are new or changed and 1432 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO11 YO12 YO0z YO0j YO0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import AllocMB AllocMalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition PB (s : astate) : Prop :=
(st_brk s = BrkNever -> brk_bytes s = 0) /\
(forall rb p, st_brk s = BrkCur rb p -> exists rg, region_of s rb = Some rg /\ rg_kind rg = RkBrk /\ rg_live rg = true).
Definition QB (s : astate) : Prop := PB s /\ MB s.
Definition RMk (s s' : astate) : Prop :=
forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> exists rg', region_of s' k = Some rg' /\ rg_kind rg' = RkMap.
Definition RQK (s s' : astate) : Prop := QB s -> QB s' /\ RMk s s'.

Lemma RMk_refl s : RMk s s.
Proof. intros k rg H K. exists rg. split; assumption. Qed.
Lemma RMk_eq s s' : st_regions s' = st_regions s -> RMk s s'.
Proof. intros E k rg H K. exists rg. unfold region_of in *. rewrite E. split; assumption. Qed.
Lemma QB_eq s s' : st_regions s' = st_regions s -> st_areas s' = st_areas s ->
st_meta_alloc_shift s' = st_meta_alloc_shift s -> st_brk s' = st_brk s -> QB s -> QB s'.
Proof.
intros E1 E2 E3 E4 ((Pa & Pb) & M1 & M2).
unfold QB, PB, MB, brk_bytes, resv_count, nareas, shift, region_of in *.
rewrite E1, E2, E3, E4. split; [split|split]; assumption.
Qed.
Lemma RQK_eq s s' : st_regions s' = st_regions s -> st_areas s' = st_areas s ->
st_meta_alloc_shift s' = st_meta_alloc_shift s -> st_brk s' = st_brk s -> RQK s s'.
Proof. intros E1 E2 E3 E4 H. split; [exact (QB_eq s s' E1 E2 E3 E4 H) | apply RMk_eq, E1]. Qed.
#[export] Instance RQK_pre : PreR RQK.
Proof.
split.
- intros s H. split; [exact H | apply RMk_refl].
- intros a b c A B Ha. destruct (A Ha) as [Hb R1]. destruct (B Hb) as [Hc R2]. split; [exact Hc|].
intros k rg H K. destruct (R1 k rg H K) as (rg1 & H1 & K1). exact (R2 k rg1 H1 K1).
Qed.
Lemma RQK_setm s p x : RQK s (upd_meta p x s).
Proof. apply RQK_eq; reflexivity. Qed.
Lemma RQK_head h v s : RQK s (set_head_st h v s).
Proof. destruct h; apply RQK_eq; reflexivity. Qed.
#[export] Instance RQK_sl : SLok RQK.
Proof. intros s p x pr nx _. apply RQK_setm. Qed.

Lemma fbrk_nb rg : rg_kind rg <> RkBrk -> f_brkb rg = 0.
Proof. intros H. unfold f_brkb, is_brk. destruct (rg_kind rg), (rg_live rg); try reflexivity; exfalso; exact (H eq_refl). Qed.
Lemma fres_nr rg : rg_kind rg <> RkMetaRes -> f_resvc rg = 0.
Proof. intros H. unfold f_resvc, is_resv. destruct (rg_kind rg); try reflexivity; exfalso; exact (H eq_refl). Qed.
Lemma brk_app s s' x : st_regions s' = st_regions s ++ [x] -> brk_bytes s' = brk_bytes s + f_brkb x.
Proof. intros E. unfold brk_bytes. rewrite E, rsum_app, rsum_cons, rsum_nil. lia. Qed.
Lemma resv_app s s' x : st_regions s' = st_regions s ++ [x] -> resv_count s' = resv_count s + f_resvc x.
Proof. intros E. unfold resv_count. rewrite E, rsum_app, rsum_cons, rsum_nil. lia. Qed.
Lemma rof_app s s' x k rg : st_regions s' = st_regions s ++ [x] -> region_of s k = Some rg -> region_of s' k = Some rg.
Proof. intros E H. unfold region_of in *. rewrite E. rewrite nth_error_app1; [exact H|]. exact (nth_error_Some_lt _ _ _ H). Qed.
Lemma rof_last s s' x : st_regions s' = st_regions s ++ [x] -> region_of s' (length (st_regions s)) = Some x.
Proof. intros E. unfold region_of. rewrite E, nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.
Lemma brk_lupd s s' k rg x : st_regions s' = lupd (st_regions s) k x -> region_of s k = Some rg ->
brk_bytes s' = brk_bytes s - f_brkb rg + f_brkb x.
Proof.
intros E H. unfold brk_bytes. rewrite E. unfold region_of in H.
rewrite (rsum_lupd f_brkb (st_regions s) k x rg (nth_error_Some_lt _ _ _ H)). rewrite (nth_error_nth _ _ _ H). reflexivity.
Qed.
Lemma resv_lupd s s' k rg x : st_regions s' = lupd (st_regions s) k x -> region_of s k = Some rg ->
resv_count s' = resv_count s - f_resvc rg + f_resvc x.
Proof.
intros E H. unfold resv_count. rewrite E. unfold region_of in H.
rewrite (rsum_lupd f_resvc (st_regions s) k x rg (nth_error_Some_lt _ _ _ H)). rewrite (nth_error_nth _ _ _ H). reflexivity.
Qed.
Lemma rof_lupd s s' k x k' : st_regions s' = lupd (st_regions s) k x -> (k < length (st_regions s))%nat ->
region_of s' k' = if Nat.eqb k' k then Some x else region_of s k'.
Proof.
intros E Hk. unfold region_of. rewrite E, nth_error_lupd. destruct (Nat.eqb k' k); cbn [andb]; [|reflexivity].
rewrite (proj2 (Nat.ltb_lt _ _) Hk). reflexivity.
Qed.
Lemma rsum_lupd_keep g f l i d : (forall rg, g (f rg) = g rg) -> rsum g (lupd l i (f (nth i l d))) = rsum g l.
Proof.
intros H. revert i. induction l as [|x l IH]; intros [|i]; cbn [lupd nth].
- reflexivity.
- reflexivity.
- rewrite !rsum_cons, H. reflexivity.
- rewrite !rsum_cons, IH. reflexivity.
Qed.
Lemma rof_lupd_keep s s' i f d k rg : st_regions s' = lupd (st_regions s) i (f (nth i (st_regions s) d)) ->
region_of s k = Some rg -> region_of s' k = Some rg \/ region_of s' k = Some (f rg).
Proof.
intros E H. unfold region_of in *. rewrite E, nth_error_lupd.
destruct (Nat.eqb k i && Nat.ltb i (length (st_regions s)))%bool eqn:C; [right | left; exact H].
apply andb_prop in C as [C _]. apply Nat.eqb_eq in C. subst k. rewrite (nth_error_nth _ _ _ H). reflexivity.
Qed.
Lemma PB_keep s s' i f d :
(forall rg, rg_kind (f rg) = rg_kind rg /\ rg_live (f rg) = rg_live rg /\ rg_len (f rg) = rg_len rg) ->
st_regions s' = lupd (st_regions s) i (f (nth i (st_regions s) d)) -> st_brk s' = st_brk s -> PB s ->
PB s' /\ RMk s s' /\ brk_bytes s' = brk_bytes s /\ resv_count s' = resv_count s.
Proof.
intros Hf E Eb [Pa Pb].
assert (EB : brk_bytes s' = brk_bytes s).
{ unfold brk_bytes. rewrite E. apply rsum_lupd_keep. intros rg. destruct (Hf rg) as (K & L & N).
unfold f_brkb, is_brk. rewrite K, L, N. reflexivity. }
assert (EV : resv_count s' = resv_count s).
{ unfold resv_count. rewrite E. apply rsum_lupd_keep. intros rg. destruct (Hf rg) as (K & _ & _).
unfold f_resvc, is_resv. rewrite K. reflexivity. }
split; [split|split; [|split; assumption]].
- intros H. rewrite EB. apply Pa. rewrite <- Eb. exact H.
- intros rb p H. rewrite Eb in H. destruct (Pb rb p H) as (rg & Hr & K & L).
destruct (rof_lupd_keep s s' i f d rb rg E Hr) as [H'|H'].
+ exists rg. split; [exact H' | exact (conj K L)].
+ exists (f rg). destruct (Hf rg) as (K' & L' & _). split; [exact H'|]. rewrite K', L'. exact (conj K L).
- intros k rg Hr K. destruct (rof_lupd_keep s s' i f d k rg E Hr) as [H'|H'].
+ exists rg. split; assumption.
+ exists (f rg). destruct (Hf rg) as (K' & _ & _). split; [exact H' | rewrite K'; exact K].
Qed.
Lemma RQK_newmap s len : RQK s (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s).
Proof.
intros ((Pa & Pb) & M1 & M2). set (S1 := set_regions _ s).
assert (ER : st_regions S1 = st_regions s ++ [mkRegion RkMap len [] true]) by reflexivity.
assert (EB : brk_bytes S1 = brk_bytes s) by (rewrite (brk_app s S1 _ ER), fbrk_nb by (cbn; discriminate); lia).
assert (EV : resv_count S1 = resv_count s) by (rewrite (resv_app s S1 _ ER), fres_nr by (cbn; discriminate); lia).
split; [split; [split|split]|].
- intros E. rewrite EB. exact (Pa E).
- intros rb p E. destruct (Pb rb p E) as (rg & H & K & L). exists rg. split; [exact (rof_app s S1 _ rb rg ER H) | exact (conj K L)].
- rewrite EB. exact M1.
- rewrite EV. exact M2.
- intros k rg H K. exists rg. split; [exact (rof_app s S1 _ k rg ER H) | exact K].
Qed.
Lemma QB_kill s r rg v : QB s -> region_of s r = Some rg -> rg_kind rg = RkMap -> rg_kind v = RkMap ->
QB (set_regions (lupd (st_regions s) r v) s).
Proof.
intros ((Pa & Pb) & M1 & M2) Hr K Kv. set (S1 := set_regions _ s).
assert (ER : st_regions S1 = lupd (st_regions s) r v) by reflexivity.
pose proof (YO0z.region_of_lt _ _ _ Hr) as Hlt.
assert (EB : brk_bytes S1 = brk_bytes s).
{ rewrite (brk_lupd s S1 r rg v ER Hr). rewrite (fbrk_nb rg) by (rewrite K; discriminate).
rewrite (fbrk_nb v) by (rewrite Kv; discriminate). lia. }
assert (EV : resv_count S1 = resv_count s).
{ rewrite (resv_lupd s S1 r rg v ER Hr). rewrite (fres_nr rg) by (rewrite K; discriminate).
rewrite (fres_nr v) by (rewrite Kv; discriminate). lia. }
split; [split|split].
- intros E. rewrite EB. exact (Pa E).
- intros rb p E. destruct (Pb rb p E) as (rgb & H & Kb & Lb). exists rgb.
rewrite (rof_lupd s S1 r v rb ER Hlt). destruct (Nat.eqb rb r) eqn:Eq.
+ apply Nat.eqb_eq in Eq. subst rb. rewrite Hr in H. injection H as <-. rewrite K in Kb. discriminate.
+ split; [exact H | exact (conj Kb Lb)].
- rewrite EB. exact M1.
- rewrite EV. exact M2.
Qed.

Definition brk_post (s : astate) (r : bool * astate) : Prop :=
PB (snd r) /\ RMk s (snd r) /\ st_areas (snd r) = st_areas s /\ shift (snd r) = shift s /\
resv_count (snd r) = resv_count s /\
(brk_bytes (snd r) <= PGSZ * (nareas (snd r) + 1) \/
(fst r = false /\ st_avail_meta_area_count (snd r) = 1 /\ brk_bytes (snd r) <= PGSZ * (nareas (snd r) + 2))).
Lemma brk_post_same s b s' : QB s -> st_regions s' = st_regions s -> st_areas s' = st_areas s ->
st_meta_alloc_shift s' = st_meta_alloc_shift s -> (st_brk s' = st_brk s \/ st_brk s' = BrkDead) -> brk_post s (b, s').
Proof.
intros ((Pa & Pb) & M1 & M2) E1 E2 E3 E4.
assert (EB : brk_bytes s' = brk_bytes s) by (unfold brk_bytes; rewrite E1; reflexivity).
assert (EG : forall k, region_of s' k = region_of s k) by (intros k; unfold region_of; rewrite E1; reflexivity).
unfold brk_post; cbn [fst snd].
split; [split|].
- intros H. destruct E4 as [E4|E4]; rewrite E4 in H; [rewrite EB; exact (Pa H) | discriminate].
- intros rb p H. destruct E4 as [E4|E4]; rewrite E4 in H; [rewrite EG; exact (Pb rb p H) | discriminate].
- split; [intros k rg H K; exists rg; rewrite EG; split; assumption|].
split; [exact E2|]. split; [unfold shift; exact E3|]. split; [unfold resv_count; rewrite E1; reflexivity|].
left. rewrite EB. unfold nareas in *. rewrite E2. exact M1.
Qed.
Lemma brk_lw F s : QB s -> lw F (brk_post s) (area_from_brk s).
Proof.
intros HQ. pose proof HQ as ((Pa & Pb) & M1 & M2).
unfold area_from_brk. apply lw_bind, lw_get. ms.
destruct (_ && _) eqn:Ec.
2:{ apply lw_ret. apply brk_post_same; [exact HQ | reflexivity | reflexivity | reflexivity | left; reflexivity]. }
destruct (st_brk s) as [| |rb pb] eqn:Eb.
- apply lw_bind, lw_ask. intros z1 _. ms. apply lw_bind, lw_ask. intros z2 _. ms.
destruct (z2 =? 0); cbn [negb].
+ apply lw_bind, lw_modify. ms. apply lw_ret.
apply brk_post_same; [exact HQ | reflexivity | reflexivity | reflexivity | right; reflexivity].
+ apply lw_bind. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms.
apply lw_bind, lw_modify. ms. apply lw_bind, lw_ask. intros z3 _. ms. apply lw_ret.
match goal with |- brk_post s (false, ?st) => set (S1 := st) end.
assert (ER : st_regions S1 = st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) by reflexivity.
unfold brk_post; cbn [fst snd].
split; [split|].
{ intros E. cbv [S1] in E. cbn in E. discriminate. }
{ intros rb' p' E. cbv [S1] in E. cbn in E. injection E as <- <-. exists (mkRegion RkBrk (2 * PGSZ) [] true).
split; [exact (rof_last s S1 _ ER) | split; reflexivity]. }
split; [intros k rg H K; exists rg; split; [exact (rof_app s S1 _ k rg ER H) | exact K]|].
split; [reflexivity|]. split; [reflexivity|].
split; [rewrite (resv_app s S1 _ ER), fres_nr by (cbn; discriminate); lia|].
right. split; [reflexivity|]. split; [reflexivity|].
rewrite (brk_app s S1 _ ER), (Pa eq_refl). change (nareas S1) with (nareas s).
change (f_brkb (mkRegion RkBrk (2 * PGSZ) [] true)) with (2 * PGSZ). unfold nareas, PGSZ. lia.
- rewrite andb_false_r in Ec. discriminate.
- apply lw_bind, lw_ask. intros z _. ms. destruct (z =? 0); cbn [negb].
+ apply lw_bind, lw_modify. ms. apply lw_ret.
apply brk_post_same; [exact HQ | reflexivity | reflexivity | reflexivity | right; reflexivity].
+ destruct (Pb rb pb eq_refl) as (rgb & Hrb & Kb & Lb).
pose proof (YO0z.region_of_lt _ _ _ Hrb) as Hlt.
apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_bind, lw_modify. ms. apply lw_ret.
match goal with |- brk_post s (false, ?st) => set (S1 := st) end.
assert (ER : st_regions S1 = lupd (st_regions s) rb (mkRegion RkBrk (rg_len rgb + PGSZ) [] true)).
{ cbv [S1]. cbn [st_regions set_avail_meta_area_count set_avail_meta_areas set_brk set_regions].
pose proof Hrb as H'. unfold region_of in H'. rewrite (nth_error_nth _ _ _ H'). reflexivity. }
unfold brk_post; cbn [fst snd].
split; [split|].
{ intros E. cbv [S1] in E. cbn in E. discriminate. }
{ intros rb' p' E. cbv [S1] in E. cbn in E. injection E as <- <-. exists (mkRegion RkBrk (rg_len rgb + PGSZ) [] true).
split; [rewrite (rof_lupd s S1 rb _ rb ER Hlt), Nat.eqb_refl; reflexivity | split; reflexivity]. }
split.
{ intros k rg H K. rewrite (rof_lupd s S1 rb _ k ER Hlt). destruct (Nat.eqb k rb) eqn:Ek.
- apply Nat.eqb_eq in Ek. subst k. rewrite Hrb in H. injection H as <-. rewrite Kb in K. discriminate.
- exists rg. split; assumption. }
split; [reflexivity|]. split; [reflexivity|].
split.
{ rewrite (resv_lupd s S1 rb rgb _ ER Hrb). rewrite (fres_nr rgb) by (rewrite Kb; discriminate).
rewrite fres_nr by (cbn; discriminate). lia. }
right. split; [reflexivity|]. split; [reflexivity|].
rewrite (brk_lupd s S1 rb rgb _ ER Hrb).
assert (F1 : f_brkb rgb = rg_len rgb) by (unfold f_brkb, is_brk; rewrite Kb, Lb; reflexivity).
change (f_brkb (mkRegion RkBrk (rg_len rgb + PGSZ) [] true)) with (rg_len rgb + PGSZ).
rewrite F1. change (nareas S1) with (nareas s). unfold nareas, PGSZ in *. lia.
Qed.

Definition mmap_post (s : astate) (r : bool * astate) : Prop :=
PB (snd r) /\ RMk s (snd r) /\ st_areas (snd r) = st_areas s /\ brk_bytes (snd r) = brk_bytes s /\
resv_count (snd r) - shift (snd r) = resv_count s - shift s /\
(st_avail_meta_area_count s <> 0 -> fst r = true /\ snd r = s).
Lemma mmap_lw F s : PB s -> lw F (mmap_post s) (area_from_mmap s).
Proof.
intros [Pa Pb]. unfold area_from_mmap. apply lw_bind, lw_get. ms.
assert (SAME : forall b, (st_avail_meta_area_count s <> 0 -> b = true) -> mmap_post s (b, s)).
{ intros b Hb. unfold mmap_post; cbn [fst snd]. split; [split; assumption|].
split; [apply RMk_refl|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros H. split; [exact (Hb H) | reflexivity]. }
destruct (st_avail_meta_area_count s =? 0) eqn:Ec.
- apply Z.eqb_eq in Ec.
apply lw_bind, lw_ask. intros z _. ms. destruct (z =? 0); cbn [negb].
+ apply lw_ret. apply SAME. intros H. contradiction.
+ apply lw_bind. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms.
apply lw_bind, lw_modify. ms. apply lw_ret.
match goal with |- mmap_post s (true, ?st) => set (S1 := st) end.
assert (ER : st_regions S1 = st_regions s ++ [mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true]) by reflexivity.
assert (EB : brk_bytes S1 = brk_bytes s) by (rewrite (brk_app s S1 _ ER), fbrk_nb by (cbn; discriminate); lia).
assert (ES : shift S1 = shift s + 1) by reflexivity.
unfold mmap_post; cbn [fst snd]. split; [split|].
{ intros E. rewrite EB. apply Pa. exact E. }
{ intros rb p E. destruct (Pb rb p E) as (rg & H & K & L). exists rg. split; [exact (rof_app s S1 _ rb rg ER H) | exact (conj K L)]. }
split; [intros k rg H K; exists rg; split; [exact (rof_app s S1 _ k rg ER H) | exact K]|].
split; [reflexivity|]. split; [exact EB|].
split; [|intros H; contradiction].
rewrite (resv_app s S1 _ ER), ES.
change (f_resvc (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true)) with 1. lia.
- apply lw_ret. apply SAME. intros _. reflexivity.
Qed.

Definition open_post (s : astate) (nu : bool) (s3 : astate) : Prop :=
PB s3 /\ RMk s s3 /\ brk_bytes s3 = brk_bytes s /\ resv_count s3 = resv_count s /\ shift s3 = shift s /\
nareas s <= nareas s3 /\ (nu = false -> nareas s3 = nareas s + 1).
Lemma post_of s nu s' S : PB s' -> RMk s s' -> brk_bytes s' = brk_bytes s -> resv_count s' = resv_count s ->
shift s' = shift s -> st_areas s' = st_areas s ->
st_regions S = st_regions s' -> st_brk S = st_brk s' -> st_meta_alloc_shift S = st_meta_alloc_shift s' ->
nareas S = nareas s' + 1 -> open_post s nu S.
Proof.
intros [Pa Pb] K Eb Er Es Ea R1 R2 R3 N.
assert (EB : brk_bytes S = brk_bytes s') by (unfold brk_bytes; rewrite R1; reflexivity).
assert (EG : forall k, region_of S k = region_of s' k) by (intros k; unfold region_of; rewrite R1; reflexivity).
assert (N' : nareas s' = nareas s) by (unfold nareas; rewrite Ea; reflexivity).
unfold open_post. split; [split|].
- intros E. rewrite EB. apply Pa. rewrite <- R2. exact E.
- intros rb p E. rewrite EG. apply (Pb rb p). rewrite <- R2. exact E.
- split; [intros k rg H Kk; destruct (K k rg H Kk) as (rg' & H' & K'); exists rg'; rewrite EG; split; assumption|].
split; [rewrite EB; exact Eb|]. split; [unfold resv_count in *; rewrite R1; exact Er|].
split; [unfold shift in *; rewrite R3; exact Es|]. split; [lia | intros _; lia].
Qed.
Ltac nar := unfold nareas; cbn [st_areas set_avail_meta_area_count set_avail_meta_areas set_area_tail set_area_head
set_areas set_avail_meta_count set_avail_meta set_regions]; rewrite length_app; cbn [length]; lia.
Lemma open_lw F nu s : PB s -> lw F (fun r => open_post s nu (snd r)) (open_area nu s).
Proof.
intros HP. unfold open_area. apply lw_bind, lw_get. ms.
assert (KEEP : open_post s true s).
{ split; [exact HP|]. split; [apply RMk_refl|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [lia|]. intros E; discriminate. }
destruct nu.
- apply lw_bind, lw_ask. intros z _. ms. destruct (z =? 0); cbn [negb].
+ apply lw_ret. exact KEEP.
+ apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_bind, lw_modify. ms. apply lw_ret. ms.
match goal with |- open_post s true (set_avail_meta_area_count _ (set_avail_meta_areas _ (set_area_tail _
(set_area_head _ (set_areas _ (set_avail_meta_count _ (set_avail_meta _ ?st))))))) => set (S2 := st) end.
pose proof (PB_keep s S2 (prid (st_avail_meta_areas s))
(fun rg => mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff (st_avail_meta_areas s)]) (rg_live rg))
(mkRegion RkMap 0 [] false) ltac:(intros rg; split; [reflexivity | split; reflexivity]) eq_refl eq_refl HP)
as (P2 & K2 & B2 & V2).
apply (post_of s true S2); [exact P2 | exact K2 | exact B2 | exact V2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
nar.
- apply lw_bind, lw_ret. ms. apply lw_bind, lw_ret. ms. apply lw_bind, lw_modify. ms. apply lw_ret. ms.
apply (post_of s false s); [exact HP | apply RMk_refl | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity |].
nar.
Qed.
Lemma new_area_Q F s : QB s -> lw F (fun r => QB (snd r) /\ RMk s (snd r))
((nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false) s).
Proof.
intros HQ. pose proof HQ as (_ & M1 & M2).
apply lw_bind. eapply lw_mono; [|apply (brk_lw F s HQ)]. intros [nu s1] (P1 & K1 & A1 & S1 & R1 & D1). ms. cbn [fst snd] in *.
apply lw_bind. eapply lw_mono; [|apply (mmap_lw F s1 P1)]. intros [rs s2] (P2 & K2 & A2 & B2 & R2 & G2). ms. cbn [fst snd] in *.
assert (N2 : nareas s2 = nareas s1) by (unfold nareas; rewrite A2; reflexivity).
assert (N1 : nareas s1 = nareas s) by (unfold nareas; rewrite A1; reflexivity).
destruct rs.
- eapply lw_mono; [|apply (open_lw F nu s2 P2)]. intros [ok s3] (P3 & K3 & B3 & R3 & S3 & N3 & F3). cbn [snd] in *.
split; [split; [exact P3 | split]|].
+ destruct D1 as [D1 | (Enu & Ea1 & D1)]; unfold PGSZ in *.
* lia.
* specialize (F3 Enu). lia.
+ unfold MB in M2. lia.
+ intros k rg H K. destruct (K1 k rg H K) as (rg1 & H1 & L1). destruct (K2 k rg1 H1 L1) as (rg2 & H2 & L2). exact (K3 k rg2 H2 L2).
- apply lw_ret. ms. split; [split; [exact P2 | split]|].
+ destruct D1 as [D1 | (Enu & Ea1 & D1)].
* unfold PGSZ in *. lia.
* exfalso. destruct (G2 ltac:(lia)) as [E _]. discriminate.
+ lia.
+ intros k rg H K. destruct (K1 k rg H K) as (rg1 & H1 & L1). exact (K2 k rg1 H1 L1).
Qed.
Lemma lw_imp {A} F (H : Prop) (P : A -> Prop) t : (H -> lw F P t) -> lw F (fun a => H -> P a) t.
Proof.
induction t as [a|q sn k IH|f]; cbn; intros X.
- intros h. exact (X h).
- intros z Hz. apply IH. intros h. exact (X h z Hz).
- exact I.
Qed.
Lemma alloc_meta_RQK F : RP F RQK alloc_meta.
Proof.
intros s. unfold alloc_meta.
eapply (lw_use F RQK); [apply lw_modify; apply RQK_eq; reflexivity | apply pr_refl | intros u s0 H0; ms].
eapply (lw_use F RQK); [|exact H0|intros fm s1 H1; ms].
{ unfold dequeue_head. apply lw_bind, lw_get_head. ms. destruct (st_free_meta_head s0) as [m|].
- eapply (lw_use F RQK); [apply (RP_dequeue F RQK HFreeMeta m (fun s2 v => RQK_head HFreeMeta v s2)) | apply pr_refl |].
intros u2 s2 H2. apply lw_ret. exact H2.
- apply lw_ret. apply pr_refl. }
destruct fm as [m|]; [apply lw_ret; exact H1|].
apply lw_bind, lw_get. ms.
eapply (lw_use F RQK); [|exact H1|intros ok s2 H2; ms].
{ destruct (0 <? st_avail_meta_count s1); [apply lw_ret; apply pr_refl|].
eapply lw_mono; [|apply (lw_imp F (QB s1) _ _ (new_area_Q F s1))]. intros a Ha. exact Ha. }
destruct ok; cbn [negb]; [|apply lw_ret; exact H2].
apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_bind, lw_setslot. ms. apply lw_ret. ms.
eapply pr_trans; [exact H2|]. eapply pr_trans; [|apply RQK_setm]. apply RQK_eq; reflexivity.
Qed.

Lemma decay_RQK F sc : RP F RQK (decay_bounces sc).
Proof.
unfold decay_bounces. destruct (bounce_idx sc); [|apply RP_ret].
apply RP_modify. intros s. bz.
match goal with |- context [if ?c then _ else _] => destruct c end; [apply pr_refl | apply RQK_eq; reflexivity].
Qed.
Lemma activate_RQK F m : RP F RQK (activate_group m).
Proof.
unfold activate_group. apply RP_bind; [apply RP_getm | intros am]. bz.
apply RP_bind; [apply RP_massert | intros _]. apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret].
Qed.
Lemma try_avail_RQK F sc : RP F RQK (try_avail sc).
Proof.
unfold try_avail. apply RP_bind; [apply RP_get_head | intros [m0|]; bz; [|apply RP_ret]].
apply RP_bind; [apply RP_getm | intros am0]. bz.
destruct (negb (am_avail am0 =? 0)); [apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret]|].
apply RP_bind.
{ destruct (am_freed am0 =? 0).
- apply RP_bind; [apply (RP_dequeue F RQK); intros; apply RQK_head | intros; apply RP_get_head].
- apply RP_bind; [apply RP_set_head; intros; apply RQK_head | intros; apply RP_ret]. }
intros [m1|]; bz; [|apply RP_ret].
apply RP_bind; [apply RP_getm | intros am1].
apply RP_bind.
{ destruct (am_freed am1 =? ones (am_last am1)); [|apply RP_ret].
destruct (am_next am1); [|apply RP_fail]. apply RP_bind; [apply RP_set_head; intros; apply RQK_head | intros; apply RP_ret]. }
intros m2. apply RP_bind; [apply RP_getm | intros am2]. bz.
apply RP_bind.
{ destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0); [|apply RP_ret].
destruct (negb (osptr_eqb (am_next am2) (Some m2))).
- destruct (am_next am2); [|apply RP_fail]. apply RP_bind; [apply RP_set_head; intros; apply RQK_head | intros; apply RP_ret].
- apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret]. }
intros m3. apply RP_bind; [apply activate_RQK | intros mask].
apply RP_bind; [apply RP_massert | intros _]. apply RP_bind; [apply RP_getm | intros am3].
apply RP_bind; [apply decay_RQK | intros _]. apply RP_bind; [apply RP_getm | intros am3'].
bz. apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret].
Qed.
Lemma enframe_RQK F g idx n ctr k : RP F RQK (enframe g idx n ctr k).
Proof.
unfold enframe. apply RP_bind; [apply RP_getm | intros am]. apply RP_bind; [apply RP_mcheck | intros _]. bz.
apply RP_bind.
{ destruct ((stride_of am - IB - n) / UNIT =? 0); [apply RP_ret|].
destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|]; [apply RP_ret | apply RP_bind; [apply RP_askz | intros; apply RP_ret]]. }
intros off0. bz. apply RP_bind; [apply RP_massert | intros _]. bz.
apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret].
Qed.
Lemma step_seq_RQK F : RP F RQK step_seq.
Proof. unfold step_seq. apply RP_modify. intros s. destruct (st_seq s =? 255); apply RQK_eq; reflexivity. Qed.
Lemma account_bounce_RQK F sc : RP F RQK (account_bounce sc).
Proof.
unfold account_bounce. destruct (bounce_idx sc); [|apply RP_ret]. apply RP_modify. intros s. bz.
match goal with |- context [if ?c then _ else _] => destruct c end; apply RQK_eq; reflexivity.
Qed.
Lemma install_group_RQK F m sc cnt aidx maplen mem sl : RP F RQK (install_group m sc cnt aidx maplen mem sl).
Proof.
unfold install_group. apply RP_bind; [apply RP_get | intros s0].
apply RP_bind; [unfold set_usage_of; apply RP_modify; intros; apply RQK_eq; reflexivity | intros _]. bz.
apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros _].
apply (RP_queue F RQK). intros; apply RQK_head.
Qed.
Lemma free_meta_RQK F m : RP F RQK (free_meta m).
Proof.
unfold free_meta. apply RP_bind; [apply RP_setslot; intros; apply RQK_setm | intros _].
apply (RP_queue F RQK). intros; apply RQK_head.
Qed.
Lemma new_region_RQK F len s : lw F (fun r => RQK s (snd r)) (new_region RkMap len s).
Proof. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms. apply RQK_newmap. Qed.

Theorem alloc_struct_Q F fuel :
(forall sc req, RP F RQK (alloc_slot fuel sc req)) /\ (forall sc req, RP F RQK (alloc_group fuel sc req)).
Proof.
induction fuel as [|f [IHs IHg]]; [split; intros sc req s; exact I|].
split.
- intros sc req s. cbn fix beta iota delta [alloc_slot].
eapply (lw_use F RQK); [apply try_avail_RQK | apply pr_refl | intros first s1 H1; ms].
destruct (negb (first =? 0)); [apply lw_ret; exact H1|].
eapply (lw_use F RQK); [apply IHg | exact H1 | intros og s2 H2; ms].
destruct og; apply lw_ret; exact H2.
- intros sc req s. cbn fix beta iota delta [alloc_group].
eapply (lw_use F RQK); [apply alloc_meta_RQK | apply pr_refl | intros om s1 H1; ms].
destruct om as [m|]; [|apply lw_ret; exact H1].
apply lw_bind, lw_get. ms.
destruct (PGSZ / 2 <? _).
+ eapply (lw_use F RQK); [apply account_bounce_RQK | exact H1 | intros u2 s2 H2; ms].
eapply (lw_use F RQK); [apply step_seq_RQK | exact H2 | intros u3 s3 H3; ms].
apply lw_bind, lw_ask. intros z _. ms. destruct (z =? 0); cbn [negb].
* eapply (lw_use F RQK); [apply free_meta_RQK | exact H3 | intros u4 s4 H4; ms]. apply lw_ret. exact H4.
* eapply (lw_use F RQK); [apply new_region_RQK | exact H3 | intros r4 s4 H4; ms].
apply lw_bind, lw_get. ms.
eapply (lw_use F RQK); [apply lw_put; apply RQK_eq; reflexivity | exact H4 | intros u5 s5 H5; ms].
eapply (lw_use F RQK); [apply install_group_RQK | exact H5 | intros u6 s6 H6; ms]. apply lw_ret. exact H6.
+ eapply (lw_use F RQK); [apply IHs | exact H1 | intros idx s2 H2; ms].
destruct (idx <? 0).
* eapply (lw_use F RQK); [apply free_meta_RQK | exact H2 | intros u3 s3 H3; ms]. apply lw_ret. exact H3.
* apply lw_bind, lw_get_head. ms. destruct (nth (Z.to_nat _) (st_active s2) None) as [g|]; [|exact I].
apply lw_bind, lw_getm. intros amg _. ms. apply lw_bind, lw_mcheck. intros _. ms. apply lw_bind, lw_get. ms.
eapply (lw_use F RQK); [apply enframe_RQK | exact H2 | intros p s3 H3; ms].
eapply (lw_use F RQK); [apply install_group_RQK | exact H3 | intros u4 s4 H4; ms]. apply lw_ret. exact H4.
Qed.

Theorem malloc_Q F n s : QB s -> lw F (fun r => QB (snd r)) (malloc n s).
Proof.
intros HQ. unfold malloc. destruct (size_overflows n); [apply lw_ret; exact HQ|].
destruct (MMAP_THRESHOLD <=? n).
- apply lw_bind, lw_ask. intros z _. ms. destruct (z =? 0); cbn [negb]; [apply lw_ret; exact HQ|].
apply lw_bind. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms.
pose proof (proj1 (RQK_newmap s (page_round (n + IB + UNIT)) HQ)) as Q1.
pose proof (region_of_app_new s (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)) as Hr1.
eapply (lw_use F RQK); [apply step_seq_RQK | apply pr_refl | intros u2 s2 H2; ms].
eapply (lw_use F RQK); [apply alloc_meta_RQK | exact H2 | intros og s3 H3; ms].
destruct (H3 Q1) as [Q3 K3].
destruct og as [g|].
+ apply lw_bind, lw_setm. ms. apply lw_bind, lw_get. ms.
eapply (lw_use F RQK); [apply lw_put; apply RQK_eq; reflexivity | apply (RQK_setm s3 g _) | intros u5 s5 H5; ms].
eapply (lw_use F RQK); [apply enframe_RQK | exact H5 | intros p s6 H6; ms].
apply lw_ret. exact (proj1 (H6 Q3)).
+ apply lw_bind, lw_ask. intros z' _. ms. apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_ret. ms.
destruct (K3 _ _ Hr1 eq_refl) as (rg' & Hr3 & Kr3).
apply (QB_kill s3 _ rg' _ Q3 Hr3 Kr3). reflexivity.
- apply lw_bind, lw_get. ms.
match goal with |- lw _ _ (bind ?mm _ _) => assert (FA1 : RP F RQK mm) end.
{ match goal with |- RP _ _ (match ?t with _ => _ end) => destruct t as [gm|] end; [|apply RP_ret].
apply RP_bind; [apply RP_getm | intros am].
destruct (am_avail am =? 0); [apply RP_ret|]. bz. apply RP_bind; [apply RP_setm; intros; apply RQK_setm | intros; apply RP_ret]. }
eapply (lw_use F RQK); [apply FA1 | apply pr_refl | intros r1 s1 H1; ms].
apply lw_bind.
eapply lw_mono with (P := fun r => RQK s (snd r)).
+ intros [gi s2] H2. ms. cbn [snd] in H2.
destruct gi as [[gm idx]|]; [|apply lw_ret; exact (proj1 (H2 HQ))].
apply lw_bind, lw_get. ms.
eapply (lw_use F RQK); [apply enframe_RQK | exact H2 | intros p s3 H3; ms].
apply lw_ret. exact (proj1 (H3 HQ)).
+ destruct r1 as [gi|].
* apply lw_ret. exact H1.
* eapply (lw_use F RQK); [apply (proj1 (alloc_struct_Q F NEST_FUEL)) | exact H1 | intros idx s2 H2; ms].
destruct (idx <? 0); [apply lw_ret; exact H2|].
apply lw_bind, lw_get_head. ms. destruct (nth (Z.to_nat _) (st_active s2) None) as [gm|]; [|exact I].
apply lw_ret. exact H2.
Qed.

Lemma rsum_zero_in f l : (forall r, In r l -> f r = 0) -> rsum f l = 0.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|].
rewrite rsum_cons, (H x (or_introl eq_refl)), IH; [reflexivity|]. intros r Hr. apply H. right. exact Hr.
Qed.
Lemma brk_zero s : brk_regions s = [] -> brk_bytes s = 0.
Proof.
intros H. unfold brk_bytes. apply rsum_zero_in. intros rg Hin. apply In_nth_error in Hin as [k Hk]. apply fbrk_nb. intros K.
assert (Hin : In k (brk_regions s)).
{ unfold brk_regions. apply in_flat_map. exists k. split.
- apply in_seq. pose proof (nth_error_Some_lt _ _ _ Hk). lia.
- cbv beta. unfold region_of. rewrite Hk, K. left. reflexivity. }
rewrite H in Hin. destruct Hin.
Qed.
Lemma PB_of_WF s : WF s -> PB s.
Proof.
intros HW. pose proof (inv_areas HW) as (_&_&_&_&_&_&A7&_).
split.
- intros E. rewrite E in A7. cbv beta iota in A7. apply brk_zero. exact A7.
- intros rb p E. rewrite E in A7. cbv beta iota in A7. destruct A7 as (Hbr & rg & Hrg & Hl & _).
destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
rewrite Hrg in Hrg2. injection Hrg2 as <-. exists rg. split; [exact Hrg | exact (conj Hk2 Hl)].
Qed.

Theorem malloc_MB : forall s n tr r s', WF s -> MB s -> 0 <= n -> yields (malloc n s) tr (r, s') -> MB s'.
Proof.
intros s n tr r s' HW HM _ Hy.
exact (proj2 (lw_yields _ _ _ _ (malloc_Q FA n s (conj (PB_of_WF s HW) HM)) Hy)).
Qed.
