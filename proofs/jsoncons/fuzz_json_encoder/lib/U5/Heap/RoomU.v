(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Address room from a byte sum and a mapping count. The kernel model may grant an mmap at any free page-aligned
   address below alloc_top (RefNodes.grant_ok_na), so the existing mappings can fragment the window; a gap of n
   bytes exists when the window exceeds the mapped bytes plus (count + 1) * (n + page). This is AsanPlacement's
   scan argument (AsanPlacement.v:54-186) over an arbitrary page-aligned window [lo, hi) instead of
   [bottomup_floor, alloc_ceiling). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PlacementSearch RefNodes.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ru_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma ru_region_free_false : forall maps lo n,
  region_free maps lo n = false ->
  exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

(* Bytes a request of nZ bytes may lose to one mapping (b, s): its size, the request, and page rounding. *)
Fixpoint ru_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + ru_weight nZ r
  end.

Lemma ru_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= ru_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

Definition ru_live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma ru_weight_filter_le : forall nZ f l, 0 <= nZ ->
  ru_weight nZ (List.filter f l) <= ru_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

Lemma ru_live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> ru_live_at c (b, s) = true -> ru_live_at c' (b, s) = false ->
  ru_weight nZ (List.filter (ru_live_at c') l) + (bv_unsigned s + nZ + 4095)
  <= ru_weight nZ (List.filter (ru_live_at c) l)
  /\ (length (List.filter (ru_live_at c') l) < length (List.filter (ru_live_at c) l))%nat.
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, ru_live_at c' p = true -> ru_live_at c p = true).
  { intros [x y] H. unfold ru_live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : ru_weight nZ (List.filter (ru_live_at c') l) <= ru_weight nZ (List.filter (ru_live_at c) l)
                /\ (length (List.filter (ru_live_at c') l) <= length (List.filter (ru_live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (ru_live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (ru_live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (ru_live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (ru_live_at c (b0, s0)); cbn; split; lia.
Qed.

Section GapWin.
  Variable L : list (word * word).
  Variable nZ lo hi : Z.
  Hypothesis HnZ : 0 <= nZ.
  Hypothesis Hlo : 0 < lo.
  Hypothesis Hhi : hi < 2 ^ 64.

  Definition ru_scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ lo <= c
    /\ c + nZ + ru_weight nZ (List.filter (ru_live_at c) L) <= hi.

  Definition ru_gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ lo <= c /\ c + nZ <= hi
    /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma ru_scan_ok_or_step : forall c, ru_scan_inv c ->
    ru_gap_at c
    \/ exists c', ru_scan_inv c'
         /\ (length (List.filter (ru_live_at c') L) < length (List.filter (ru_live_at c) L))%nat.
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof (ru_weight_nonneg nZ (List.filter (ru_live_at c) L) HnZ) as Hw0.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply ru_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply ru_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (ru_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_round_up_Z_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { unfold c', page_round_up_Z, page_size.
        pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : ru_live_at c (b, s) = true) by (unfold ru_live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : ru_live_at c' (b, s) = false) by (unfold ru_live_at; cbn; apply Z.ltb_ge; lia).
      destruct (ru_live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_round_up_Z_aligned|].
      split; lia.
  Qed.

  Lemma ru_scan : forall k c, (length (List.filter (ru_live_at c) L) <= k)%nat -> ru_scan_inv c ->
    exists g, ru_gap_at g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (ru_scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (ru_scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  Theorem ru_free_gap :
    lo mod page_size = 0 ->
    lo + nZ + ru_weight nZ L <= hi ->
    exists g, g mod page_size = 0 /\ lo <= g /\ g + nZ <= hi
              /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros Hal Hslack.
    assert (Hinv : ru_scan_inv lo).
    { split; [exact Hal|]. split; [lia|].
      pose proof (ru_weight_filter_le nZ (ru_live_at lo) L HnZ). lia. }
    exact (ru_scan _ lo (le_n _) Hinv).
  Qed.
End GapWin.

Lemma ru_weight_live : forall nZ l,
  ru_weight nZ l = live_bytes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add live_bytes]; [reflexivity|].
  change (live_bytes ((b, s) :: l)) with (bv_unsigned s + live_bytes l).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

(* A null-hint anonymous mmap of n bytes finds an address when the window [page, alloc_top) exceeds the mapped
   bytes B plus count * (n + 4095) plus n. *)
Theorem grant_exists_na_room : forall hint (m : Model) (n C B : Z),
  0 <= n ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  live_bytes (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) <= B ->
  alloc_top (m_vmmaps m) < 2 ^ 64 ->
  page_size + n + B + C * (n + 4095) <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na hint m a n = true.
Proof.
  intros hint m n C B Hn HC HB Htop Hroom.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  assert (HC' : Z.of_nat (length l) * (n + 4095) <= C * (n + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct (ru_free_gap l n page_size (alloc_top (m_vmmaps m)) Hn ltac:(unfold page_size; lia) Htop
              ltac:(unfold page_size; reflexivity) ltac:(rewrite ru_weight_live; lia)) as (g & Hal & Hlo & Hhi & Hfree).
  exists (Z_to_bv 64 g). unfold grant_ok_na.
  assert (Hg : bv_unsigned (Z_to_bv 64 g) = g) by (apply ru_u64_lit; unfold page_size in Hlo; lia).
  rewrite Hg, Hal. fold l. rewrite Hfree.
  rewrite (proj2 (Z.ltb_lt 0 g)) by (unfold page_size in Hlo; lia).
  rewrite (proj2 (Z.leb_le (g + n) _)) by lia. reflexivity.
Qed.
