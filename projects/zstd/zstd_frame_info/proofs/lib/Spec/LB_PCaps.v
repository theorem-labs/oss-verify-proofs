(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Malloc MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_StmtA LB_Raw.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stc_lowf (k : Z) : bool := let c := stc_k k in (c =? 0) || (size_class (c - 1) <=? k).
Lemma stc_low_b_true : forallb stc_lowf (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_low n : 0 <= n < MMAP_THRESHOLD -> 1 <= size_to_class n -> S_ (size_to_class n - 1) - IB < n.
Proof.
  intros Hn Hc. pose proof (size_to_class_ok n Hn) as [R _]. revert Hc. rewrite size_to_class_k in *. rewrite Z.shiftr_div_pow2 in * by lia.
  unfold IB, UNIT, MMAP_THRESHOLD, S_ in *.
  set (k := (n + 4 - 1) / 2 ^ 4) in *.
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange stc_lowf 0 8191 k stc_low_b_true ltac:(lia) ltac:(lia)) as H. unfold stc_lowf in H. cbn zeta in H.
  intros Hc. apply Bool.orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia|]. apply Z.leb_le in H. unfold UNIT. lia.
Qed.

(* [comment removed for export] *)
Definition lmin (c : Z) : Z := if c =? 0 then 0 else (S_ (c - 1) - IB) / 4.

Lemma S_mod16 : forall c, 0 <= c < 48 -> S_ c mod 16 = 0.
Proof. intros c Hc. unfold S_, UNIT. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Lemma kv_class_len : forall len, 0 <= len -> 4 * (len + 1) < MMAP_THRESHOLD ->
  let c := size_to_class (4 * (len + 1)) in 0 <= c < 48 /\ lmin c <= len.
Proof.
  intros len Hlen Hsmall c. pose proof (size_to_class_ok (4 * (len + 1)) ltac:(lia)) as [R _]. fold c in R. split; [exact R|].
  unfold lmin. destruct (Z.eqb_spec c 0) as [E|NE]; [lia|].
  pose proof (size_to_class_low (4 * (len + 1)) ltac:(lia) ltac:(fold c; lia)) as L. fold c in L.
  pose proof (S_mod16 (c - 1) ltac:(lia)) as M. unfold IB in *.
  pose proof (Z.div_mod (S_ (c - 1)) 16 ltac:(lia)) as D. rewrite M, Z.add_0_r in D.
  set (t := S_ (c - 1) / 16) in *. rewrite D. replace (16 * t - 4) with (4 * (4 * t - 1)) by lia.
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma lmin_pos : forall c, 1 <= c < 48 -> 3 <= lmin c.
Proof.
  intros c Hc. unfold lmin. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (proj1 (tab_basic_ok (c - 1) ltac:(lia))). unfold IB. apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition W : Z := 2^24 + 1.
Definition AMBC : Z := 8.
(* [comment removed for export] *)
Lemma stc_24 : size_to_class 24 = 1. Proof. reflexivity. Qed.

Definition kvcap (c : Z) : Z := if c =? 0 then 3 * W else W / lmin c.
(* [comment removed for export] *)
Definition Pcap (c : Z) : Z :=
  if c =? 63 then AMBC
  else if (0 <=? c) && (c <? 48) then AMBC
  else 0.

Lemma Pcap_nonneg : forall c, 0 <= Pcap c.
Proof.
  intros c. unfold Pcap, AMBC.
  destruct (c =? 63); [lia|]. destruct ((0 <=? c) && (c <? 48)); lia.
Qed.

(* [comment removed for export] *)
Definition RBIG : Z := 3 * (2^26 + 8192) + 5 * W + (24 * 2^24 + 8192).

Lemma PHI_Pcap_eq : PHI Pcap = 231057408.
Proof. vm_compute. reflexivity. Qed.

Lemma PHI_Pcap : PHI Pcap + RBIG <= LBUDGET.
Proof. rewrite PHI_Pcap_eq. unfold RBIG, W, LBUDGET. cbn. lia. Qed.
