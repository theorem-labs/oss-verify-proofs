(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gap_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma gap_region_free_false : forall maps lo n,
  region_free maps lo n = false -> exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov). exists b', s'. split; [now right|exact Hov].
Qed.

Lemma page_up_ge : forall z, z <= page_round_up_Z z.
Proof. intros z. unfold page_round_up_Z, page_size. pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)). lia. Qed.
Lemma page_up_le : forall z, page_round_up_Z z <= z + 4095.
Proof. intros z. unfold page_round_up_Z, page_size. pose proof (Z.mul_div_le (z + 4096 - 1) 4096 ltac:(lia)). lia. Qed.
Lemma page_up_aligned : forall z, page_round_up_Z z mod page_size = 0.
Proof. intros z. unfold page_round_up_Z, page_size. rewrite Z.mul_comm, Z.mul_mod; [reflexivity| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_app : forall nZ l1 l2, gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2.
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma gw_sizes_app : forall l1 l2, gw_sizes (l1 ++ l2) = gw_sizes l1 + gw_sizes l2.
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma gw_sizes_nonneg : forall l, 0 <= gw_sizes l.
Proof. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 s). lia. Qed.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof. induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia. Qed.

Lemma gap_weight_sizes : forall nZ l, gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. cbn [snd]. lia.
Qed.

Lemma gap_weight_mono : forall n1 n2 l, n1 <= n2 -> gap_weight n1 l <= gap_weight n2 l.
Proof. intros n1 n2 l H. rewrite !gap_weight_sizes. nia. Qed.

(* [comment removed for export] *)
Definition live_at (c : Z) (p : word * word) : bool := c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ -> gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). destruct (f (b, s)); cbn; lia.
Qed.

Lemma gap_weight_cons : forall nZ a s l, gap_weight nZ ((a, s) :: l) = bv_unsigned s + nZ + 4095 + gap_weight nZ l.
Proof. reflexivity. Qed.

Lemma gap_weight_perm : forall nZ l1 l2, Permutation l1 l2 -> gap_weight nZ l1 = gap_weight nZ l2.
Proof. intros nZ l1 l2 P. induction P as [|[b s] l l' P IH|[b s] [b' s'] l|l l' l'' P1 IH1 P2 IH2]; cbn; lia. Qed.

Lemma gw_sizes_perm : forall l1 l2, Permutation l1 l2 -> gw_sizes l1 = gw_sizes l2.
Proof. intros l1 l2 P. induction P; cbn; lia. Qed.

Lemma gap_weight_map : forall {A} nZ (f : A -> word * word) (l : list A),
  gap_weight nZ (map f l) = fold_right (fun x acc => bv_unsigned (snd (f x)) + nZ + 4095 + acc) 0 l.
Proof. intros A nZ f l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f x) as [b s] eqn:Hf. cbn. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma gap_weight_remove_In : forall nZ l a s, 0 <= nZ -> In (a, s) l ->
  gap_weight nZ (map_remove l a) + (bv_unsigned s + nZ + 4095) <= gap_weight nZ l.
Proof.
  intros nZ l a s HnZ. unfold map_remove. induction l as [|[b s0] l IH]; intros Hin; [destruct Hin|].
  cbn. pose proof (bv_unsigned_in_range 64 s0). destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn. pose proof (gap_weight_filter_le nZ (fun p => negb (bv_eqb (fst p) a)) l HnZ). lia.
  - specialize (IH Hin). destruct (bv_eqb b a); cbn; lia.
Qed.

Lemma gap_weight_remove_le : forall nZ l a, 0 <= nZ -> gap_weight nZ (map_remove l a) <= gap_weight nZ l.
Proof. intros. unfold map_remove. apply gap_weight_filter_le. assumption. Qed.

Lemma live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
  gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095) <= gap_weight nZ (List.filter (live_at c) l)
  /\ (length (List.filter (live_at c') l) < length (List.filter (live_at c) l))%nat.
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
  { intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gap.
  Variable L : list (word * word).
  Variables nZ F U : Z.
  Hypothesis HnZ : 0 <= nZ.
  Hypothesis HF : 0 <= F /\ F mod page_size = 0.
  Hypothesis HU : U < 2^64.

  Definition scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ F <= c /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= U.

  Definition gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ F <= c /\ c + nZ <= U /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma scan_ok_or_step : forall c, scan_inv c ->
    gap_at c \/ exists c', scan_inv c' /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply gap_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply gap_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (gap_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_up_ge (B + S)) as Hge. pose proof (page_up_le (B + S)) as Hle. fold c' in Hge, Hle.
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_up_aligned|]. split; lia.
  Qed.

  Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c -> exists g, gap_at g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia]. exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)]; [exists c; exact Hok|]. apply (IH c'); [lia|exact Hinv'].
  Qed.

  Theorem free_gap_live :
    F + nZ + gap_weight nZ (List.filter (live_at F) L) <= U ->
    exists g, g mod page_size = 0 /\ F <= g /\ g + nZ <= U /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof. intros Hslack. exact (scan _ F (le_n _) (conj (proj2 HF) (conj (Z.le_refl _) Hslack))). Qed.

  Theorem free_gap :
    F + nZ + gap_weight nZ L <= U ->
    exists g, g mod page_size = 0 /\ F <= g /\ g + nZ <= U /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof. intros Hslack. apply free_gap_live. pose proof (gap_weight_filter_le nZ (live_at F) L HnZ). lia. Qed.
End Gap.

(* [comment removed for export] *)
Theorem free_gap_of_totals : forall (L : list (word * word)) nZ F U,
  0 <= nZ -> 0 <= F -> F mod page_size = 0 -> U < 2^64 ->
  F + nZ + gw_sizes L + Z.of_nat (length L) * (nZ + 4095) <= U ->
  exists g, g mod page_size = 0 /\ F <= g /\ g + nZ <= U /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros L nZ F U HnZ HF0 HFa HU Hs. apply free_gap; auto. rewrite gap_weight_sizes. lia.
Qed.

(* [comment removed for export] *)
Theorem null_hint_window : forall (h : VmMaps) nZ,
  0 <= nZ -> alloc_top h < 2^64 ->
  page_size + nZ + gap_weight nZ (vm_reserved h ++ vm_maps h) <= alloc_top h ->
  exists g, g mod page_size = 0 /\ 0 < g /\ g + nZ <= alloc_top h
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ HnZ HT Hs.
  destruct (free_gap (vm_reserved h ++ vm_maps h) nZ page_size (alloc_top h) HnZ ltac:(unfold page_size; split; [lia| reflexivity]) HT Hs)
    as (g & G1 & G2 & G3 & G4).
  exists g. unfold page_size in *. repeat split; auto; lia.
Qed.
