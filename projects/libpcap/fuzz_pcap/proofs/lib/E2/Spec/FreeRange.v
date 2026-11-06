(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Lps04.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eloZ (e : word * word) : Z := bv_unsigned (fst e).
Definition szZ (e : word * word) : Z := bv_unsigned (snd e).
Definition ehiZ (e : word * word) : Z := eloZ e + szZ e.

(* [comment removed for export] *)
Fixpoint wsum (nZ lo : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | e :: r => (if lo <? ehiZ e then szZ e + page_size + nZ else 0) + wsum nZ lo r
  end.

(* [comment removed for export] *)
Fixpoint wcnt (lo : Z) (l : list (word * word)) : nat :=
  match l with
  | [] => O
  | e :: r => ((if (lo <? ehiZ e)%Z then 1 else 0) + wcnt lo r)%nat
  end.

Lemma unsigned_lit64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma page_size_pos : 0 < page_size.
Proof. unfold page_size. lia. Qed.

Lemma szZ_nonneg : forall e, 0 <= szZ e.
Proof. intros e. unfold szZ. apply bv_unsigned_in_range. Qed.
Lemma eloZ_nonneg : forall e, 0 <= eloZ e.
Proof. intros e. unfold eloZ. apply bv_unsigned_in_range. Qed.

Lemma wsum_nonneg : forall nZ lo l, 0 <= nZ -> 0 <= wsum nZ lo l.
Proof.
  intros nZ lo l Hn. induction l as [|e l IH]; cbn; [lia|].
  pose proof (szZ_nonneg e). pose proof page_size_pos. destruct (lo <? ehiZ e); lia.
Qed.

(* [comment removed for export] *)
Lemma wsum_mono : forall nZ lo lo' l, 0 <= nZ -> lo <= lo' -> wsum nZ lo' l <= wsum nZ lo l.
Proof.
  intros nZ lo lo' l Hn Hle. induction l as [|e l IH]; cbn; [lia|].
  pose proof (szZ_nonneg e). pose proof page_size_pos.
  destruct (Z.ltb_spec lo' (ehiZ e)); destruct (Z.ltb_spec lo (ehiZ e)); try lia.
Qed.

Lemma wcnt_mono : forall lo lo' l, lo <= lo' -> (wcnt lo' l <= wcnt lo l)%nat.
Proof.
  intros lo lo' l Hle. induction l as [|e l IH]; cbn; [lia|].
  destruct (Z.ltb_spec lo' (ehiZ e)); destruct (Z.ltb_spec lo (ehiZ e)); try lia.
Qed.

(* [comment removed for export] *)
Lemma wsum_drop : forall nZ lo lo' l e, 0 <= nZ -> lo <= lo' -> In e l ->
  lo < ehiZ e -> ehiZ e <= lo' ->
  wsum nZ lo' l + (szZ e + page_size + nZ) <= wsum nZ lo l.
Proof.
  intros nZ lo lo' l e Hn Hle Hin H1 H2. induction l as [|x l IH]; [destruct Hin|].
  cbn. pose proof (szZ_nonneg x). pose proof page_size_pos.
  destruct Hin as [->|Hin].
  - pose proof (wsum_mono nZ lo lo' l Hn Hle).
    destruct (Z.ltb_spec lo' (ehiZ e)); destruct (Z.ltb_spec lo (ehiZ e)); try lia.
  - specialize (IH Hin).
    destruct (Z.ltb_spec lo' (ehiZ x)); destruct (Z.ltb_spec lo (ehiZ x)); try lia.
Qed.

Lemma wcnt_drop : forall lo lo' l e, lo <= lo' -> In e l -> lo < ehiZ e -> ehiZ e <= lo' ->
  (wcnt lo' l < wcnt lo l)%nat.
Proof.
  intros lo lo' l e Hle Hin H1 H2. induction l as [|x l IH]; [destruct Hin|].
  cbn. destruct Hin as [->|Hin].
  - pose proof (wcnt_mono lo lo' l Hle).
    destruct (Z.ltb_spec lo' (ehiZ e)); destruct (Z.ltb_spec lo (ehiZ e)); try lia.
  - specialize (IH Hin).
    destruct (Z.ltb_spec lo' (ehiZ x)); destruct (Z.ltb_spec lo (ehiZ x)); try lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_false : forall l lo n,
  region_free l lo n = false ->
  exists e, In e l /\ bv_unsigned lo < ehiZ e /\ eloZ e < bv_unsigned lo + bv_unsigned n.
Proof.
  induction l as [|[a sz] l IH]; intros lo n H; [discriminate|].
  cbn [region_free] in H. apply andb_false_iff in H as [H|H].
  - exists (a, sz). split; [left; reflexivity|]. unfold iv_overlap in H. apply negb_false_iff in H.
    apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    unfold ehiZ, eloZ, szZ. cbn [fst snd]. lia.
  - destruct (IH lo n H) as (e & Hin & He). exists e. split; [right; exact Hin| exact He].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_Z_bounds : forall x, x <= page_round_up_Z x < x + page_size.
Proof.
  intros x. unfold page_round_up_Z. pose proof page_size_pos.
  pose proof (Z_div_mod_eq_full (x + page_size - 1) page_size).
  pose proof (Z.mod_pos_bound (x + page_size - 1) page_size ltac:(lia)). lia.
Qed.

Lemma page_round_up_Z_aligned' : forall x, page_round_up_Z x mod page_size = 0.
Proof. intros x. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma bottomup_floor_aligned : bottomup_floor mod page_size = 0.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

Lemma bottomup_floor_pos : 0 < bottomup_floor.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

Lemma alloc_ceiling_small : band_ceiling < 2^63.
Proof. unfold band_ceiling, sp_window_lo, stack_max_size. lia. Qed.

Section Scan.
Variable h : VmMaps.
Variable nZ : Z.
Hypothesis HnZ : 0 < nZ.

Let ents := vm_reserved h ++ vm_maps h.

(* [comment removed for export] *)
Definition is_cand (lo : Z) : Prop :=
  lo = bottomup_floor \/ exists e, In e ents /\ lo = page_round_up_Z (ehiZ e).

#[using="Type"] Lemma cand_in : forall lo, is_cand lo -> 0 <= lo < 2^64 -> In (Z_to_bv 64 lo) (vm_base_candidates h).
Proof.
  intros lo [->|(e & Hin & ->)] Hr; unfold vm_base_candidates.
  - left. reflexivity.
  - right. apply in_map_iff. exists e. split; [|exact Hin]. unfold ehiZ, eloZ, szZ. reflexivity.
Qed.

#[using="HnZ"] Lemma scan : forall k lo,
  (wcnt lo ents <= k)%nat ->
  is_cand lo -> lo mod page_size = 0 -> bottomup_floor <= lo ->
  lo + nZ + wsum nZ lo ents <= band_ceiling ->
  exists a, In a (vm_base_candidates h) /\ vm_base_ok h nZ a = true.
Proof.
  induction k as [|k IH]; intros lo Hcnt Hc Hal Hfl Hpot.
  all: pose proof (wsum_nonneg nZ lo ents ltac:(lia)) as Wnn;
       pose proof alloc_ceiling_small as Hcs; pose proof bottomup_floor_pos as Hfp;
       assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit64; lia);
       assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply unsigned_lit64; lia);
       destruct (region_free ents (Z_to_bv 64 lo) (Z_to_bv 64 nZ)) eqn:Hrf.
  1,3: exists (Z_to_bv 64 lo); split; [apply cand_in; [exact Hc| lia]|];
       unfold vm_base_ok; rewrite Ulo; fold ents; rewrite Hrf, Hal, Z.eqb_refl;
       rewrite (proj2 (Z.ltb_lt 0 lo)) by lia; rewrite (proj2 (Z.leb_le _ lo) Hfl);
       rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity.
  - (* [comment removed for export] *)
    exfalso. destruct (region_free_false _ _ _ Hrf) as (e & Hin & H1 & H2). rewrite Ulo in H1.
    assert (1 <= wcnt lo ents)%nat; [|lia].
    clear - Hin H1. induction ents as [|x l IHl]; [destruct Hin|]. cbn. destruct Hin as [<-|Hin].
    + rewrite (proj2 (Z.ltb_lt _ _) H1). lia.
    + specialize (IHl Hin). lia.
  - destruct (region_free_false _ _ _ Hrf) as (e & Hin & H1 & H2). rewrite Ulo in H1. rewrite Ulo, Un in H2.
    set (lo' := page_round_up_Z (ehiZ e)).
    pose proof (page_round_up_Z_bounds (ehiZ e)) as [R1 R2]. fold lo' in R1, R2.
    pose proof (szZ_nonneg e) as Sz. unfold ehiZ in *.
    assert (Hle : lo <= lo') by lia.
    pose proof (wsum_drop nZ lo lo' ents e ltac:(lia) Hle Hin ltac:(unfold ehiZ; lia) ltac:(unfold ehiZ; lia)) as D.
    pose proof (wcnt_drop lo lo' ents e Hle Hin ltac:(unfold ehiZ; lia) ltac:(unfold ehiZ; lia)) as C.
    apply (IH lo').
    + lia.
    + right. exists e. split; [exact Hin| reflexivity].
    + apply page_round_up_Z_aligned'.
    + lia.
    + lia.
Qed.

#[using="HnZ ents"] Theorem vm_find_base_some :
  bottomup_floor + nZ + wsum nZ bottomup_floor (vm_reserved h ++ vm_maps h) <= band_ceiling ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  intros Hpot.
  destruct (scan (wcnt bottomup_floor ents) bottomup_floor ltac:(lia) (or_introl eq_refl)
              bottomup_floor_aligned ltac:(lia) Hpot) as (a & Hin & Hok).
  unfold vm_find_base. destruct (find (vm_base_ok h nZ) (vm_base_candidates h)) as [a'|] eqn:E; [exists a'; reflexivity|].
  exfalso. pose proof (find_none _ _ E a Hin) as H. rewrite Hok in H. discriminate.
Qed.

#[using="HnZ ents"] Corollary vm_gap_available_true :
  bottomup_floor + nZ + wsum nZ bottomup_floor (vm_reserved h ++ vm_maps h) <= band_ceiling ->
  vm_gap_available h nZ = true.
Proof.
  intros Hpot. unfold vm_gap_available. destruct (vm_find_base_some Hpot) as [a ->]. reflexivity.
Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition inband (e : word * word) : bool := bottomup_floor <? ehiZ e.

Fixpoint band_bytes (l : list (word * word)) : Z :=
  match l with [] => 0 | e :: r => (if inband e then szZ e else 0) + band_bytes r end.
Fixpoint band_count (l : list (word * word)) : Z :=
  match l with [] => 0 | e :: r => (if inband e then 1 else 0) + band_count r end.

Lemma wsum_floor : forall nZ l,
  wsum nZ bottomup_floor l = band_bytes l + band_count l * (page_size + nZ).
Proof.
  intros nZ l. induction l as [|e l IH]; cbn; [lia|]. unfold inband. rewrite IH.
  destruct (bottomup_floor <? ehiZ e); lia.
Qed.

Lemma band_bytes_app : forall l1 l2, band_bytes (l1 ++ l2) = band_bytes l1 + band_bytes l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.
Lemma band_count_app : forall l1 l2, band_count (l1 ++ l2) = band_count l1 + band_count l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.
Lemma band_bytes_nonneg : forall l, 0 <= band_bytes l.
Proof. induction l as [|e l IH]; cbn; [lia|]. pose proof (szZ_nonneg e). destruct (inband e); lia. Qed.
Lemma band_count_nonneg : forall l, 0 <= band_count l.
Proof. induction l as [|e l IH]; cbn; [lia|]. destruct (inband e); lia. Qed.

(* [comment removed for export] *)
Lemma band_below : forall l, (forall e, In e l -> ehiZ e <= bottomup_floor) -> band_bytes l = 0 /\ band_count l = 0.
Proof.
  induction l as [|e l IH]; intros H; cbn; [split; reflexivity|].
  destruct (IH ltac:(intros x Hx; apply H; right; exact Hx)) as [-> ->].
  unfold inband. destruct (Z.ltb_spec bottomup_floor (ehiZ e)); [|split; reflexivity].
  specialize (H e (or_introl eq_refl)). lia.
Qed.

(* [comment removed for export] *)
Lemma band_bytes_le_live : forall l, band_bytes l <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; cbn; [lia|]. unfold szZ; cbn [snd].
  pose proof (bv_unsigned_in_range 64 sz). destruct (inband (a, sz)); lia.
Qed.

(* [comment removed for export] *)
Theorem vm_gap_available_of_bound : forall h nZ (N L : Z),
  0 < nZ ->
  band_count (vm_reserved h ++ vm_maps h) <= N ->
  band_bytes (vm_reserved h ++ vm_maps h) <= L ->
  nZ + L + N * (page_size + nZ) <= band_ceiling - bottomup_floor ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ N L Hn HN HL Hfit. apply vm_gap_available_true; [exact Hn|].
  rewrite wsum_floor. pose proof page_size_pos.
  pose proof (band_count_nonneg (vm_reserved h ++ vm_maps h)). nia.
Qed.

(* [comment removed for export] *)
Lemma band_width : band_ceiling - bottomup_floor = 0x5554D4D55000.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

(* [comment removed for export] *)
Example band_fits_example : 2^28 + 2^34 + 2^18 * (page_size + 2^28) <= band_ceiling - bottomup_floor.
Proof. rewrite band_width. unfold page_size. lia. Qed.
