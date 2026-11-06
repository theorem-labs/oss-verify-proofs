(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 AMallocI AMalmys ASecB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition zrange (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) = Some (Z_to_bv 8 0).
Lemma zrange_mapped : forall m a n, zrange m a n -> mapped m a n.
Proof. intros m a n Z i Hi. rewrite (Z i Hi). discriminate. Qed.
Lemma zrange_sub : forall m a n b k, zrange m a n -> a <= b -> b + k <= a + n -> zrange m b k.
Proof. intros m a n b k Z H1 H2 i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply Z. lia. Qed.

Section Junk.
Context {Clg : Ceiling}.
  Variables (m : mem) (a : Z).
  Hypothesis A0 : 0x60a000 <= a.

  (* [comment removed for export] *)
  Lemma mapped_CBj : forall k : nat, a + Z.of_nat k <= 2^64 -> mapped m a (Z.of_nat k) ->
    exists bs, length bs = k /\ rw_cells rsegs m a [CB k bs].
  Proof.
    intros k Hk M. exists (rdbytes m a k). split; [apply rdbytes_length|].
    apply ro_rw; [| cbn [cells_size csize]; rewrite Nat.add_0_r; exact M].
    split; [cbn; rewrite rdbytes_length; exact (conj eq_refl I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply rdbytes_bytes_at; [exact M| lia| lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mapped_C1j : a + 1 <= 2^64 -> mapped m a 1 -> exists b, rw_cells rsegs m a [C1 b].
  Proof.
    intros H1 M. destruct (mapped_CBj 1 ltac:(lia) ltac:(exact M)) as (bs & L & R).
    destruct bs as [|b [|]]; cbn in L; try lia. exists b.
    refine (rwc_rebytes _ _ _ _ _ _ R); [cbn; exact (conj I I)| reflexivity].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mapped_u8arr : forall k : nat, a + Z.of_nat k <= 2^64 -> mapped m a (Z.of_nat k) ->
    exists bs, length bs = k /\ u8arr rsegs m a bs.
  Proof.
    intros k Hk M. destruct (mapped_CBj k Hk M) as (bs & L & R). exists bs. split; [exact L|]. apply (u8arr_of_rw_cells _ _ _ k). exact R.
  Qed.
  Lemma mapped_stk : forall k, a + k <= 2^64 -> mapped m a k -> stk rsegs m a (a + k).
  Proof.
    intros k Hk M. split; [lia|]. split; [lia|]. intros x Hx.
    assert (X : m (Z_to_bv 64 x) <> None) by (replace x with (a + (x - a)) by lia; apply M; lia).
    unfold wview, mrd, wa. destruct (m (Z_to_bv 64 x)) as [b|] eqn:E; [| exfalso; exact (X eq_refl)]. split; [discriminate| exists b; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma zrange_CB : forall k : nat, a + Z.of_nat k <= 2^64 -> zrange m a (Z.of_nat k) ->
    rw_cells rsegs m a [CB k (repeat (Z_to_bv 8 0) k)].
  Proof.
    intros k Hk Z. apply ro_rw; [| cbn [cells_size csize]; rewrite Nat.add_0_r; apply zrange_mapped; exact Z].
    split; [cbn; rewrite repeat_length; exact (conj eq_refl I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi. unfold mrd, wa. rewrite (Z (Z.of_nat i) ltac:(lia)).
    symmetry. apply nth_error_repeat. exact Hi.
  Qed.
  Lemma zrange_C8s : forall k : nat, a + 8 * Z.of_nat k <= 2^64 -> zrange m a (8 * Z.of_nat k) ->
    rw_cells rsegs m a (map C8 (repeat (wz 0) k)).
  Proof.
    intros k Hk Z. pose proof (zrange_CB (8 * k) ltac:(lia) ltac:(rewrite Nat2Z.inj_mul; exact Z)) as R.
    refine (rwc_rebytes _ _ _ _ _ _ R); [apply CB8_wf|]. rewrite CB8_bytes. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    clear. induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH.
    replace (8 * S k)%nat with (8 + 8 * k)%nat by lia. rewrite repeat_app. reflexivity.
  Qed.
  Lemma zrange_HDR : a + 16 <= 2^64 -> zrange m a 16 ->
    rw_cells rsegs m a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0); C4 (wz 0); C8 (wz 0)].
  Proof.
    intros H Z. pose proof (zrange_CB 16 ltac:(lia) ltac:(exact Z)) as R.
    refine (rwc_rebytes _ _ _ _ _ _ R); [cbn; tauto| reflexivity].
  Qed.
  (* [comment removed for export] *)
End Junk.

(* [comment removed for export] *)
Section DKeys.
Context {Clg : Ceiling}.
  Lemma sec_dkeys : forall A, WF AL_pboth A ->
    Forall (fun k => (1 <= length k <= 255)%nat) (p_dkeys (a_pl A)) /\ NoDup (map depot_hashC (p_dkeys (a_pl A))) /\
    (length (p_dkeys (a_pl A)) <= 2048)%nat.
  Proof. intros A W. pose proof (wfP A W) as PL. unfold wf_place in PL. cbv zeta in PL. tauto. Qed.
End DKeys.
