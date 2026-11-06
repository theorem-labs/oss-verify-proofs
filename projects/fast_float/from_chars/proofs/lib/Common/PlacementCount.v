(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint ledger_size (L : list (word * word)) : Z :=
  match L with
  | [] => 0%Z
  | (_, s) :: r => (bv_unsigned s + ledger_size r)%Z
  end.

Lemma ledger_size_nonneg : forall L, (0 <= ledger_size L)%Z.
Proof.
  induction L as [|[a s] r IH]; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). lia.
Qed.

Lemma ledger_size_app : forall L1 L2,
  ledger_size (L1 ++ L2) = (ledger_size L1 + ledger_size L2)%Z.
Proof. induction L1 as [|[a s] r IH]; intro L2; cbn; [lia | rewrite IH; lia]. Qed.

Definition entry_eqb (p q : word * word) : bool :=
  bv_eqb (fst p) (fst q) && bv_eqb (snd p) (snd q).

Lemma entry_eqb_true : forall p q, entry_eqb p q = true -> p = q.
Proof.
  intros [a s] [b t] H. unfold entry_eqb in H. cbn in H.
  apply andb_true_iff in H as [H1 H2].
  apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. reflexivity.
Qed.

Lemma entry_eqb_refl : forall p, entry_eqb p p = true.
Proof.
  intros [a s]. unfold entry_eqb, bv_eqb. cbn. rewrite !Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Definition remove_entry (p : word * word) (L : list (word * word)) : list (word * word) :=
  List.filter (fun q => negb (entry_eqb q p)) L.

Lemma remove_entry_length : forall p L, In p L ->
  (length (remove_entry p L) < length L)%nat.
Proof.
  intros p L. induction L as [|q r IH]; intro Hin; [contradiction|].
  unfold remove_entry in *. cbn [List.filter].
  pose proof (filter_length_le (fun q0 => negb (entry_eqb q0 p)) r).
  destruct (entry_eqb q p) eqn:E; cbn [negb length].
  - lia.
  - destruct Hin as [-> | Hin]; [rewrite entry_eqb_refl in E; discriminate E|].
    specialize (IH Hin). lia.
Qed.

Lemma filter_size_le : forall f L, (ledger_size (List.filter f L) <= ledger_size L)%Z.
Proof.
  intros f. induction L as [|[c u] r IH]; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 u).
  destruct (f (c, u)); cbn; lia.
Qed.

Lemma remove_entry_size : forall p L, In p L ->
  (ledger_size (remove_entry p L) + bv_unsigned (snd p) <= ledger_size L)%Z.
Proof.
  intros [a s] L. induction L as [|[b t] r IH]; intro Hin; [contradiction|].
  unfold remove_entry in *. cbn - [entry_eqb].
  pose proof (bv_unsigned_in_range 64 t).
  destruct (entry_eqb (b, t) (a, s)) eqn:E; cbn - [entry_eqb].
  - apply entry_eqb_true in E. injection E as -> ->.
    pose proof (filter_size_le (fun q => negb (entry_eqb q (a, s))) r). lia.
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. rewrite entry_eqb_refl in E. discriminate E.
    + specialize (IH Hin). cbn in IH. lia.
Qed.

Lemma region_free_remove_entry : forall L lo n p,
  region_free (remove_entry p L) lo n = true ->
  iv_overlap lo n (fst p) (snd p) = false ->
  region_free L lo n = true.
Proof.
  intros L lo n p Hfree Hp. apply region_free_intro. intros a sz Hin.
  destruct (entry_eqb (a, sz) p) eqn:E.
  - apply entry_eqb_true in E. rewrite <- E in Hp. exact Hp.
  - eapply region_free_In; [exact Hfree|].
    unfold remove_entry. apply List.filter_In. split; [exact Hin | rewrite E; reflexivity].
Qed.

Lemma region_free_false_In : forall L lo n,
  region_free L lo n = false -> exists p, In p L /\ iv_overlap lo n (fst p) (snd p) = true.
Proof.
  induction L as [|[a s] r IH]; intros lo n H; [discriminate H|].
  cbn in H. destruct (iv_overlap lo n a s) eqn:E.
  - exists (a, s). split; [now left | exact E].
  - cbn in H. destruct (IH lo n H) as (p & Hin & Hov). exists p. split; [now right | exact Hov].
Qed.

Lemma page_round_up_Z_aligned' : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_bounds : forall z, (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
Theorem free_gap_exists : forall (L : list (word * word)) (lo hi nZ : Z),
  (0 <= lo)%Z -> (lo mod page_size = 0)%Z ->
  (0 < nZ)%Z -> (hi <= two_pow_64)%Z ->
  (lo + ledger_size L + Z.of_nat (length L) * (nZ + page_size) + nZ <= hi)%Z ->
  exists g : Z, (g mod page_size = 0)%Z /\ (lo <= g)%Z /\ (g + nZ <= hi)%Z
    /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros L lo hi nZ.
  remember (length L) as k eqn:Hk.
  assert (Hle : (length L <= k)%nat) by lia. clear Hk.
  revert L lo Hle.
  induction k as [|k IH]; intros L lo Hle Hlo Hal HnZ Hhi Hb; unfold page_size in *.
  - destruct L; [|cbn in Hle; lia].
    exists lo. cbn in Hb. split; [exact Hal|]. split; [lia|]. split; [lia|]. reflexivity.
  - pose proof (ledger_size_nonneg L) as Hs0. pose proof (Nat2Z.is_nonneg k).
    destruct (region_free L (Z_to_bv 64 lo) (Z_to_bv 64 nZ)) eqn:Hfree.
    + exists lo. split; [exact Hal|]. split; [lia|]. split; [| exact Hfree].
      rewrite Nat2Z.inj_succ in Hb. nia.
    + destruct (region_free_false_In L _ _ Hfree) as ([a s] & Hin & Hov).
      cbn [fst snd] in Hov. unfold iv_overlap in Hov.
      apply andb_true_iff in Hov as [Hov1 Hov2].
      apply Z.ltb_lt in Hov1. apply Z.ltb_lt in Hov2.
      assert (Hlo64 : (lo < two_pow_64)%Z).
      { unfold page_size in *. nia. }
      assert (HnZ64 : (nZ < two_pow_64)%Z).
      { unfold page_size in *. nia. }
      rewrite Z_to_bv_unsigned, bv_wrap_small in Hov1, Hov2
        by (unfold two_pow_64 in *; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
      rewrite (Z_to_bv_unsigned 64 nZ), bv_wrap_small in Hov2
        by (unfold two_pow_64 in *; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
      set (lo' := page_round_up_Z (bv_unsigned a + bv_unsigned s)).
      pose proof (page_round_up_Z_bounds (bv_unsigned a + bv_unsigned s)) as Hr.
      pose proof (remove_entry_length (a, s) L Hin) as HlenR.
      pose proof (remove_entry_size (a, s) L Hin) as HszR. cbn [snd] in HszR.
      pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 s).
      destruct (IH (remove_entry (a, s) L) lo' ltac:(lia)) as (g & Hg1 & Hg2 & Hg3 & Hg4).
      * fold lo'. lia.
      * apply page_round_up_Z_aligned'.
      * exact HnZ.
      * exact Hhi.
      * fold lo'. unfold page_size in *. nia.
      * exists g. split; [exact Hg1|]. split; [lia|]. split; [exact Hg3|].
        apply (region_free_remove_entry L _ _ (a, s) Hg4). cbn [fst snd].
        unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge.
        rewrite Z_to_bv_unsigned, bv_wrap_small
          by (unfold two_pow_64 in *; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
        lia.
Qed.

(* [comment removed for export] *)
Theorem null_hint_placement : forall (h : VmMaps) (nZ : Z),
  (0 < nZ)%Z ->
  (page_size + ledger_size (vm_reserved h ++ vm_maps h)
   + Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (nZ + page_size) + nZ
   <= alloc_top h)%Z ->
  exists a : word,
    (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
    /\ (bv_unsigned a + nZ <= alloc_top h)%Z
    /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ HnZ Hb.
  pose proof (alloc_top_lt h) as Htop.
  assert (Hp0 : (0 <= page_size)%Z) by (unfold page_size; lia).
  assert (Hp1 : (page_size mod page_size = 0)%Z) by reflexivity.
  assert (Hp2 : (alloc_top h <= two_pow_64)%Z) by lia.
  destruct (free_gap_exists (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ
              Hp0 Hp1 HnZ Hp2 Hb) as (g & Hg1 & Hg2 & Hg3 & Hg4).
  exists (Z_to_bv 64 g).
  assert (Hg : bv_unsigned (Z_to_bv 64 g) = g).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold two_pow_64, page_size in *. change (bv_modulus 64) with (2 ^ 64)%Z. lia. }
  rewrite Hg. split; [exact Hg1|]. split; [unfold page_size in *; lia|]. split; [exact Hg3 | exact Hg4].
Qed.

Lemma ledger_size_bounded : forall (L : list (word * word)) (smax : Z),
  Forall (fun p => (bv_unsigned (snd p) <= smax)%Z) L ->
  (ledger_size L <= Z.of_nat (length L) * smax)%Z.
Proof.
  intros L smax H. induction H as [|[a s] r Hs Hr IH]; cbn [ledger_size length]; [lia|].
  cbn [snd] in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Corollary null_hint_placement_bounded : forall (h : VmMaps) (nZ smax : Z) (K : nat),
  (0 < nZ)%Z -> (0 <= smax)%Z ->
  (length (vm_reserved h ++ vm_maps h) <= K)%nat ->
  Forall (fun p => (bv_unsigned (snd p) <= smax)%Z) (vm_reserved h ++ vm_maps h) ->
  (page_size + Z.of_nat K * (smax + nZ + page_size) + nZ <= alloc_top h)%Z ->
  exists a : word,
    (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
    /\ (bv_unsigned a + nZ <= alloc_top h)%Z
    /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ smax K HnZ Hsmax HK Hall Hb.
  apply null_hint_placement; [exact HnZ|].
  pose proof (ledger_size_bounded _ smax Hall) as Hsz.
  set (k := length (vm_reserved h ++ vm_maps h)) in *.
  assert (Hk : (Z.of_nat k <= Z.of_nat K)%Z) by lia.
  unfold page_size in *.
  assert (Z.of_nat k * (nZ + 4096) <= Z.of_nat K * (nZ + 4096))%Z by nia.
  assert (Z.of_nat k * smax <= Z.of_nat K * smax)%Z by nia.
  nia.
Qed.
