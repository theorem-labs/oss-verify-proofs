(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BlacementSearch.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma fg_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

Lemma fg_region_free_false : forall maps lo n,
  region_free maps lo n = false ->
  exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

Definition live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
  gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

Lemma live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
  gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095)
  <= gap_weight nZ (List.filter (live_at c) l)
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

Section Gap.
  Variable L : list (word * word).
  Variable nZ : Z.
  Hypothesis HnZ : 0 <= nZ.

  Definition scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c
    /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.

  Definition gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c /\ c + nZ <= alloc_ceiling
    /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma scan_ok_or_step : forall c, scan_inv c ->
    gap_at c
    \/ exists c', scan_inv c'
         /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof fg_alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_round_up_Z_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { unfold c', page_round_up_Z, page_size.
        pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_round_up_Z_aligned|].
      split; lia.
  Qed.

  Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c ->
    exists g, gap_at g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  Theorem free_gap_of_slack :
    bottomup_floor + nZ + gap_weight nZ L <= alloc_ceiling ->
    exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
              /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros Hslack.
    assert (Hinv : scan_inv bottomup_floor).
    { split; [rewrite bottomup_floor_val; reflexivity|]. split; [lia|].
      pose proof (gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ). lia. }
    exact (scan _ bottomup_floor (le_n _) Hinv).
  Qed.
End Gap.

Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : forall nZ l,
  gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Theorem free_gap_of_totals : forall (h : VmMaps) nZ tot,
  0 <= nZ ->
  gw_sizes (vm_reserved h ++ vm_maps h) <= tot ->
  bottomup_floor + nZ + tot + Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (nZ + 4095) <= alloc_ceiling ->
  exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ tot HnZ Htot Hband.
  destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ HnZ) as (g & Hal & Hfl & Hc & Hfree).
  { rewrite gap_weight_sizes. lia. }
  exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. exact Hfree.
Qed.

Definition kHighMemBeg : Z := 0x10007fff8000.
