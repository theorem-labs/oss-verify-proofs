(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12 YO0z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma In_region_of s rg : In rg (st_regions s) -> exists k, region_of s k = Some rg.
Proof. intros H. apply In_nth_error in H as [k Hk]. exists k. exact Hk. Qed.
Lemma resv_le_live s :
(forall k rg, region_of s k = Some rg -> 0 <= rg_len rg) ->
(forall k rg, region_of s k = Some rg -> rg_kind rg = RkMetaRes -> rg_live rg = true) ->
resv_total s <= live_bytes s.
Proof.
intros Hnn Hlive. unfold resv_total, live_bytes.
assert (G : forall l, (forall rg, In rg l -> 0 <= rg_len rg) -> (forall rg, In rg l -> rg_kind rg = RkMetaRes -> rg_live rg = true) ->
fold_right (fun rg acc => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end) 0 l <=
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|x t IH]; intros A B; cbn; [lia|].
assert (IH' := IH (fun rg H => A rg (or_intror H)) (fun rg H => B rg (or_intror H))).
pose proof (A x (or_introl eq_refl)) as Ax.
destruct (rg_kind x) eqn:Ek; destruct (rg_live x) eqn:El; try lia.
pose proof (B x (or_introl eq_refl) Ek). congruence. }
apply G; intros rg Hin; destruct (In_region_of s rg Hin) as [k Hk]; eauto.
Qed.
Definition page_slots (s : astate) : list (nat * Z) :=
flat_map (fun k => match region_of s k with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => []
end) (seq 0 (length (st_regions s))).
Lemma length_page_slots s :
(forall k rg, region_of s k = Some rg -> 0 <= rg_len rg) ->
Z.of_nat (length (page_slots s)) * PGSZ <= live_bytes s.
Proof.
intros Hnn. unfold page_slots, live_bytes.
assert (G : forall l base, (forall rg, In rg l -> 0 <= rg_len rg) ->
Z.of_nat (length (flat_map (fun k => match nth_error l (k - base)%nat with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq base (length l)))) * PGSZ <=
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|x t IH]; intros base A; cbn [length seq flat_map fold_right]; [cbn; lia|].
rewrite Nat.sub_diag. cbn [nth_error]. rewrite length_app.
assert (IH' : Z.of_nat (length (flat_map (fun k => match nth_error t (k - S base)%nat with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq (S base) (length t)))) * PGSZ <=
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 t).
{ apply IH. intros rg H. apply A. right. exact H. }
assert (EE : flat_map (fun k => match nth_error (x :: t) (k - base)%nat with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq (S base) (length t)) =
flat_map (fun k => match nth_error t (k - S base)%nat with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq (S base) (length t))).
{ apply flat_map_ext_In. intros k Hk. apply in_seq in Hk. replace (k - base)%nat with (S (k - S base)) by lia. reflexivity. }
rewrite EE. pose proof (A x (or_introl eq_refl)) as Ax.
destruct (rg_live x).
- rewrite length_map, length_seq. unfold PGSZ in *.
pose proof (Z.mul_div_le (rg_len x) 4096 ltac:(lia)).
assert (0 <= rg_len x / 4096) by (apply Z.div_pos; lia). nia.
- cbn [length]. lia. }
pose proof (G (st_regions s) 0%nat) as G0.
assert (EE : flat_map (fun k => match nth_error (st_regions s) (k - 0)%nat with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq 0 (length (st_regions s))) =
flat_map (fun k => match region_of s k with
| Some rg => if rg_live rg then map (fun j => (k, Z.of_nat j)) (seq 0 (Z.to_nat (rg_len rg / PGSZ))) else []
| None => [] end) (seq 0 (length (st_regions s)))).
{ apply flat_map_ext_In. intros k _. rewrite Nat.sub_0_r. reflexivity. }
rewrite <- EE. apply G0. intros rg Hin. destruct (In_region_of s rg Hin) as [k Hk]. eapply Hnn. exact Hk.
Qed.
Lemma areas_le_page_slots s :
areas_ok s -> (Z.of_nat (length (st_areas s)) <= Z.of_nat (length (page_slots s)))%Z.
Proof.
intros (A1 & A2 & _).
set (f := fun a : sptr => (prid a, poff a / PGSZ)).
assert (ND : NoDup (map f (st_areas s))).
{ apply (NoDup_map_inv (fun q : nat * Z => SP (fst q) (snd q * PGSZ))). rewrite map_map.
erewrite map_ext_in; [rewrite map_id; exact A1|]. intros a Ha. destruct (A2 a Ha) as (r & o & rg & -> & Ho & _). subst f. cbn.
f_equal. unfold PGSZ in *. pose proof (Z_div_mod_eq_full o 4096). lia. }
apply Nat2Z.inj_le. rewrite <- (length_map f). apply NoDup_incl_length; [exact ND|].
intros q Hq. apply in_map_iff in Hq as [a [<- Ha]]. destruct (A2 a Ha) as (r & o & rg & -> & Ho & Hlo & Hrg & Hl & Hhi & _). subst f. cbn.
unfold page_slots. apply in_flat_map. exists r. split; [apply in_seq; pose proof (region_of_lt _ _ _ Hrg); lia|].
rewrite Hrg, Hl. apply in_map_iff. exists (Z.to_nat (o / PGSZ)). split.
- f_equal. unfold PGSZ in *. pose proof (Z.div_pos o 4096). lia.
- apply in_seq. unfold PGSZ in *.
assert (o / 4096 + 1 <= rg_len rg / 4096).
{ replace (o / 4096 + 1) with ((o + 4096) / 4096) by (rewrite <- Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
pose proof (Z.div_pos o 4096). lia.
Qed.
Lemma keys_le_areas s : keys_ok s -> Z.of_nat (length (keys s)) <= METAS_PER_AREA * Z.of_nat (length (st_areas s)).
Proof.
intros (ND & KP & _ & _ & Hcnt).
set (F := fun a : sptr => map (fun k => padd a (AREA_HDR + META_SIZE * Z.of_nat k)) (seq 0 (Z.to_nat METAS_PER_AREA))).
assert (LE2 : forall l, Z.of_nat (length (flat_map F l)) = METAS_PER_AREA * Z.of_nat (length l)).
{ induction l as [|a t IH]; cbn [flat_map length]; [lia|]. rewrite length_app. subst F. cbn beta. rewrite length_map, length_seq.
rewrite Nat2Z.inj_add, IH. unfold METAS_PER_AREA in *. lia. }
assert (LE : (length (keys s) <= length (flat_map F (st_areas s)))%nat).
{ apply NoDup_incl_length; [exact ND|]. intros p Hp. destruct (KP p Hp) as (a & k & Ha & Hk & ->).
apply in_flat_map. exists a. split; [exact Ha|]. subst F. cbn beta. apply in_map_iff. exists (Z.to_nat k). split; [rewrite Z2Nat.id by lia; reflexivity|].
apply in_seq. unfold handed in Hk. destruct (sptr_eqb a _); unfold METAS_PER_AREA in *; lia. }
pose proof (LE2 (st_areas s)). lia.
Qed.
Lemma class_sum_le s sc : WF s -> class_sum [] s sc <= 32 * Z.of_nat (length (keys s)).
Proof.
intros HW. unfold class_sum.
assert (G : forall l, (forall g, In g l -> contrib [] s sc g <= 32) -> fold_right (fun g acc => contrib [] s sc g + acc) 0 l <= 32 * Z.of_nat (length l)).
{ induction l as [|x t IH]; intros H; cbn [fold_right length]; [lia|].
pose proof (H x (or_introl eq_refl)). assert (IH' := IH (fun g Hg => H g (or_intror Hg))). lia. }
apply G. intros g _. unfold contrib. destruct (MTX [] s g) as [[| |am]|] eqn:E; try lia.
pose proof (inv_groups HW g am E) as ((M1 & _) & _). destruct (am_sc am =? sc); lia.
Qed.
Theorem bounded_of_live : forall s, WF s -> live_bytes s <= 2 ^ 39 -> bounded s.
Proof.
intros s HW Hlive. pose proof (inv_areas HW) as HA. pose proof HA as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
pose proof (inv_ctx HW) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
pose proof (resv_le_live s A9 (fun k rg Hk Hkd => proj1 (A5 k rg Hk Hkd))) as Hresv.
pose proof (length_page_slots s A9) as Hps. pose proof (areas_le_page_slots s HA) as Har.
assert (Hareas : Z.of_nat (length (st_areas s)) <= 2 ^ 27) by (unfold PGSZ in Hps; nia).
split; [|split].
- intros sc.
assert (Hnn : forall c, 0 <= usage_of s c).
{ intros c. unfold usage_of, znth. destruct (nth_in_or_default (Z.to_nat c) (st_usage s) 0) as [H|H]; [apply C5; exact H | rewrite H; lia]. }
split; [apply Hnn|].
assert (K : forall c, 0 <= c < 48 -> usage_of s c < 2 ^ 40).
{ intros c Hc. rewrite (inv_usage HW c Hc). unfold U0. pose proof (class_sum_le s c HW). pose proof (keys_le_areas s (inv_keys HW)).
unfold METAS_PER_AREA in *. nia. }
destruct (Z_lt_dec sc 0) as [Hneg|Hnneg].
+ replace (usage_of s sc) with (usage_of s 0) by (unfold usage_of, znth; replace (Z.to_nat sc) with (Z.to_nat 0) by lia; reflexivity).
enough (usage_of s 0 < 2 ^ 40) by lia. apply K. lia.
+ destruct (Z_lt_dec sc 48) as [Hlt|Hge]; [enough (usage_of s sc < 2 ^ 40) by lia; apply K; lia|].
unfold usage_of, znth. rewrite nth_overflow; [lia|]. rewrite C2. lia.
- split; [exact C10|]. rewrite A6 in Hresv. unfold PGSZ in Hresv.
destruct (Z_le_dec (st_meta_alloc_shift s) 26) as [|Hgt]; [lia|]. exfalso.
assert (2 ^ 27 <= 2 ^ st_meta_alloc_shift s) by (apply Z.pow_le_mono_r; lia). lia.
- lia.
Qed.
