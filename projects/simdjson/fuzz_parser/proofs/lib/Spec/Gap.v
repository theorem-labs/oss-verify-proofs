(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MState.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MmapComplete.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FLOOR : Z := 0x2aaaaaaab000.
Definition CEIL : Z := 0x7fff7f800000.

Lemma FLOOR_val : FLOOR = 0x2aaaaaaab000.
Proof. reflexivity. Qed.
Lemma CEIL_val : CEIL = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma CEIL_le_alloc_top : forall h,
  sp_window_lo <= bv_unsigned (vm_init_sp h) -> CEIL <= alloc_top h.
Proof. intros h Hs. unfold alloc_top, CEIL. unfold sp_window_lo, stack_max_size in *. lia. Qed.

Lemma page_size_4096 : page_size = 4096.
Proof. reflexivity. Qed.

Definition glo (e : word * word) : Z := bv_unsigned (fst e).
Definition gsz (e : word * word) : Z := bv_unsigned (snd e).
Definition ghi (e : word * word) : Z := glo e + gsz e.

(* [comment removed for export] *)
Definition in_band_b (e : word * word) : bool := (glo e <? CEIL) && (FLOOR <? ghi e).

Fixpoint sum_sz (l : list (word * word)) : Z :=
  match l with [] => 0 | e :: r => gsz e + sum_sz r end.

Lemma sum_sz_live_bytes : forall l, sum_sz l = live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [reflexivity|]. unfold gsz. cbn. rewrite IH. reflexivity. Qed.

Lemma sum_sz_app : forall l1 l2, sum_sz (l1 ++ l2) = sum_sz l1 + sum_sz l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma gsz_nonneg : forall e, 0 <= gsz e.
Proof. intros e. unfold gsz. apply bv_unsigned_in_range. Qed.

Lemma sum_sz_nonneg : forall l, 0 <= sum_sz l.
Proof. induction l as [|e l IH]; cbn; [lia|]. pose proof (gsz_nonneg e). lia. Qed.

Lemma sum_sz_filter_le : forall f l, sum_sz (List.filter f l) <= sum_sz l.
Proof. induction l as [|e l IH]; intros; cbn; [lia|]. pose proof (gsz_nonneg e). destruct (f e); cbn; lia. Qed.

Lemma length_filter_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

(* [comment removed for export] *)
Definition above (c : Z) (e : word * word) : bool := in_band_b e && (c <? ghi e).
Definition pot (nZ c : Z) (maps : list (word * word)) : Z :=
  Z.of_nat (length (List.filter (above c) maps)) * (nZ + 4095) + sum_sz (List.filter (above c) maps).

Lemma above_mono_pt : forall c c' e, c <= c' -> above c' e = true -> above c e = true.
Proof.
  intros c c' e Hc H. unfold above in *. apply andb_prop in H as [H1 H2]. rewrite H1. cbn.
  apply Z.ltb_lt in H2. apply Z.ltb_lt. lia.
Qed.

Lemma filter_above_mono : forall c c' maps, c <= c' ->
  (length (List.filter (above c') maps) <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) <= sum_sz (List.filter (above c) maps).
Proof.
  intros c c' maps Hc. induction maps as [|e l [IH1 IH2]]; cbn; [split; lia|].
  pose proof (gsz_nonneg e).
  destruct (above c' e) eqn:E1; destruct (above c e) eqn:E2; cbn; try lia.
  rewrite (above_mono_pt c c' e Hc E1) in E2. discriminate.
Qed.

(* [comment removed for export] *)
Lemma filter_above_drop : forall c c' maps e, c <= c' -> In e maps -> above c e = true -> ghi e <= c' ->
  (length (List.filter (above c') maps) + 1 <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) + gsz e <= sum_sz (List.filter (above c) maps).
Proof.
  intros c c' maps e Hc Hin Ha Hhi. induction maps as [|x l IH]; [destruct Hin|].
  cbn. destruct Hin as [->|Hin].
  - rewrite Ha. assert (Hx : above c' e = false).
    { unfold above in *. apply andb_prop in Ha as [Hb _]. rewrite Hb. cbn. apply Z.ltb_ge. lia. }
    rewrite Hx. cbn. pose proof (filter_above_mono c c' l Hc) as [M1 M2]. lia.
  - specialize (IH Hin). destruct IH as [IH1 IH2]. pose proof (gsz_nonneg x).
    destruct (above c' x) eqn:E1; destruct (above c x) eqn:E2; cbn; try lia.
    rewrite (above_mono_pt c c' x Hc E1) in E2. discriminate.
Qed.

Lemma region_free_false_inv : forall maps lo n,
  region_free maps lo n = false -> exists e, In e maps /\ iv_overlap lo n (fst e) (snd e) = true.
Proof.
  induction maps as [|[a sz] l IH]; intros lo n H; cbn in H; [discriminate|].
  destruct (iv_overlap lo n a sz) eqn:E.
  - exists (a, sz). split; [left; reflexivity| exact E].
  - cbn in H. destruct (IH lo n H) as (e & Hin & He). exists e. split; [right; exact Hin| exact He].
Qed.

Lemma page_round_up_Z_bounds : forall z, z <= page_round_up_Z z <= z + 4095.
Proof.
  intros z. unfold page_round_up_Z. rewrite page_size_4096.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod 4096 = 0.
Proof. intros z. unfold page_round_up_Z. rewrite page_size_4096. apply Z_mod_mult. Qed.

Lemma FLOOR_aligned : FLOOR mod 4096 = 0.
Proof. rewrite FLOOR_val. reflexivity. Qed.

Lemma find_some_of_In {A} : forall (f : A -> bool) l x, In x l -> f x = true -> exists y, List.find f l = Some y.
Proof.
  intros f l x Hin Hf. destruct (List.find f l) as [y|] eqn:E; [exists y; reflexivity|].
  exfalso. pose proof (List.find_none _ _ E x Hin). congruence.
Qed.

Section Walk.
Variable h : VmMaps.
Variable nZ : Z.
Let maps := vm_reserved h ++ vm_maps h.
Hypothesis HnZ : 0 < nZ.
Hypothesis Htop : CEIL <= alloc_top h.

(* [comment removed for export] *)
Lemma walk_step : forall c,
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  (exists a, vm_find_base h nZ = Some a)
  \/ (exists e, In e maps /\ above c e = true /\ glo e < c + nZ).
Proof.
  intros c Hal Hfl Hinv. pose proof FLOOR_val as FV. pose proof CEIL_val as CV.
  assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia).
  assert (Hc64 : 0 <= c < 2^64) by (unfold FLOOR, CEIL in *; lia).
  assert (HnZ64 : 0 <= nZ < 2^64) by (unfold FLOOR, CEIL in *; lia).
  destruct (region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
  - left. apply (MmapComplete.vm_find_base_complete h nZ (Z_to_bv 64 c)); rewrite ?unsigned_lit by exact Hc64.
    + lia.
    + rewrite page_size_4096. exact Hal.
    + lia.
    + unfold CEIL in *. lia.
    + exact Hfree.
  - right. destruct (region_free_false_inv _ _ _ Hfree) as (e & Hin & Hov). exists e.
    unfold iv_overlap in Hov. rewrite !unsigned_lit in Hov by assumption. apply andb_prop in Hov as [O1 O2].
    apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
    split; [exact Hin|]. split; [| unfold glo; lia].
    unfold above, in_band_b, ghi, glo, gsz. unfold CEIL, FLOOR in *.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned (fst e)) _)) by lia.
    rewrite (proj2 (Z.ltb_lt 0x2aaaaaaab000 _)) by lia.
    rewrite (proj2 (Z.ltb_lt c _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma walk : forall k c,
  (length (List.filter (above c) maps) <= k)%nat ->
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  induction k as [|k IH]; intros c Hk Hal Hfl Hinv.
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    exfalso. assert (HinF : In e (List.filter (above c) maps)) by (apply filter_In; auto).
    destruct (List.filter (above c) maps); [destruct HinF| cbn in Hk; lia].
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    set (c' := page_round_up_Z (ghi e)).
    pose proof (page_round_up_Z_bounds (ghi e)) as [R1 R2]. fold c' in R1, R2.
    assert (Hhi : c < ghi e). { unfold above in Hab. apply andb_prop in Hab as [_ Hab]. apply Z.ltb_lt in Hab. exact Hab. }
    assert (Hcc : c <= c') by lia.
    destruct (filter_above_drop c c' maps e Hcc Hin Hab R1) as [D1 D2].
    apply (IH c').
    + lia.
    + apply page_round_up_Z_aligned'.
    + lia.
    + unfold pot in *. unfold ghi in *. pose proof (gsz_nonneg e).
      pose proof (sum_sz_nonneg (List.filter (above c') maps)). nia.
Qed.
End Walk.

(* [comment removed for export] *)
Theorem vm_gap_available_intro : forall h nZ,
  0 < nZ -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  (Z.of_nat (length (List.filter in_band_b maps)) + 1) * (nZ + 4095) + live_bytes maps <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ HnZ Htop maps Hb. unfold vm_gap_available.
  assert (Hinv : FLOOR + nZ + pot nZ FLOOR maps <= CEIL).
  { unfold pot. rewrite <- sum_sz_live_bytes in Hb.
    assert (L1 : (length (List.filter (above FLOOR) maps) <= length (List.filter in_band_b maps))%nat).
    { unfold above. clear. induction maps as [|e l IH]; cbn; [lia|]. destruct (in_band_b e); cbn; [destruct (_ <? _); cbn; lia| lia]. }
    pose proof (sum_sz_filter_le (above FLOOR) maps). pose proof (sum_sz_nonneg maps).
    assert (M : Z.of_nat (length (List.filter (above FLOOR) maps)) * (nZ + 4095)
                <= Z.of_nat (length (List.filter in_band_b maps)) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  destruct (walk h nZ HnZ Htop (length (List.filter (above FLOOR) maps)) FLOOR (le_n _) FLOOR_aligned (Z.le_refl _) Hinv) as [a ->].
  reflexivity.
Qed.

(* [comment removed for export] *)
Corollary vm_gap_available_intro_N : forall h nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4095) + T <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ N R T HnZ Htop maps HN HT HB. apply vm_gap_available_intro; [lia| exact Htop|]. fold maps.
  set (L := Z.of_nat (length (List.filter in_band_b maps))) in *.
  assert (M1 : (L + 1) * (nZ + 4095) <= (N + 1) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (M2 : (N + 1) * (nZ + 4095) <= (N + 1) * (R + 4095)) by (apply Z.mul_le_mono_nonneg_l; subst L; lia).
  lia.
Qed.
