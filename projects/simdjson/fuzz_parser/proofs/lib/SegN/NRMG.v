(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SNU.
Local Notation u := bv_unsigned.

Section Fam.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition topnz (M : word -> option byte) (x n : word) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 (u x + 8 * u n - 8)) 8 = Some bs /\ bytes_le_to_Z bs <> 0.
Definition tbnd (x n : word) : Prop := 8 <= u x + 8 * u n < 2^64.

Definition g_nrm (M : word -> option byte) (x n : word) : Prop := tbnd x n /\ (u n = 0 \/ topnz M x n).
Definition g_nrm62 (M : word -> option byte) (x n : word) : Prop := tbnd x n /\ (62 <= u n \/ u n = 0 \/ topnz M x n).
Definition g_nrmc (M : word -> option byte) (x n c : word) : Prop := tbnd x n /\ (62 <= u n \/ u c <> 0 \/ u n = 0 \/ topnz M x n).
Definition g_topw (M : word -> option byte) (a : word) : Prop :=
  8 <= u a /\ exists bs, rdn segs M (Z_to_bv 64 (u a - 8)) 8 = Some bs /\ bytes_le_to_Z bs <> 0.

Definition snu_gp (id : nat) (vs : list word) (M : word -> option byte) : Prop :=
  match id, vs with
  | 7%nat, [x; n] => g_nrm M x n
  | 8%nat, [x; n] => g_nrm62 M x n
  | 9%nat, [x; n; c] => g_nrmc M x n c
  | 10%nat, [a] => g_topw M a
  | _, _ => SNG.sng_gp segs id vs M
  end.
End Fam.

Definition topwin (x n : expr) : SG.gwin := (EAlu ALU_ADD x (EMd M_MUL (ELit 8) n), -8, ELit 8).

Definition snu_gfp (id : nat) (args : list expr) : list SG.gwin :=
  match id, args with
  | 7%nat, [x; n] => [topwin x n]
  | 8%nat, [x; n] => [topwin x n]
  | 9%nat, [x; n; c] => [topwin x n]
  | 10%nat, [a] => [(a, -8, ELit 8)]
  | _, _ => SNG.sng_gfp id args
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variable segs : list Segment.

Lemma u_add1' : forall a : word, u a + 1 < 2^64 -> u (a + 1) = u a + 1.
Proof.
  intros a H. rewrite bv_add_unsigned. rewrite (bv_unsigned_BV 64 1).
  unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_small. pose proof (SNG.u_rng' a). lia.
Qed.

Lemma rdn_frame : forall (M M' : word -> option byte) n (a : word), u a + Z.of_nat n <= 2^64 ->
  (forall y : word, u a <= u y < u a + Z.of_nat n -> M' y = M y) -> rdn segs M' a n = rdn segs M a n.
Proof.
  intros M M' n. induction n as [|n IH]; intros a Hn HF; [reflexivity|].
  cbn [rdn]. rewrite (HF a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - match goal with |- context [rdn segs M' ?b (S n')] => set (b' := b) end.
    assert (Ub : u b' = u a + 1) by (apply u_add1'; lia).
    rewrite (IH b'); [reflexivity | rewrite Ub; lia |].
    intros y Hy. rewrite Ub in Hy. apply HF. lia.
Qed.

Lemma u_top : forall E x n, u (edenot E x) + 8 * u (edenot E n) < 2^64 ->
  u (edenot E (EAlu ALU_ADD x (EMd M_MUL (ELit 8) n))) = u (edenot E x) + 8 * u (edenot E n).
Proof.
  intros E x n H. rewrite SNG.u_edenot_add. cbn [edenot]. rewrite u_mul64.
  assert (H8 : u (Z_to_bv 64 8) = 8) by reflexivity. rewrite H8.
  pose proof (SNG.u_rng' (edenot E x)). pose proof (SNG.u_rng' (edenot E n)).
  rewrite (Z.mod_small (8 * _)) by lia. apply Z.mod_small. lia.
Qed.

Lemma topnz_frame : forall (M M' : word -> option byte) E x n, tbnd (edenot E x) (edenot E n) ->
  (forall y : word, (exists w, In w [topwin x n] /\ let '(lo, hi) := SG.win_den E w in lo <= u y < hi) -> M' y = M y) ->
  topnz segs M (edenot E x) (edenot E n) -> topnz segs M' (edenot E x) (edenot E n).
Proof.
  intros M M' E x n Hb HF (bs & Hr & Hnz). exists bs. split; [|exact Hnz]. unfold tbnd in Hb.
  set (a := Z_to_bv 64 (u (edenot E x) + 8 * u (edenot E n) - 8)).
  assert (Ua : u a = u (edenot E x) + 8 * u (edenot E n) - 8) by (apply SNG.u_small'; lia).
  rewrite (rdn_frame M M'); [exact Hr | cbn; lia |].
  intros y Hy. apply HF. exists (topwin x n). split; [left; reflexivity|]. unfold topwin. cbn [SG.win_den].
  rewrite u_top by lia. assert (H8 : u (edenot E (ELit 8)) = 8) by reflexivity. rewrite H8. cbn in Hy. lia.
Qed.

Theorem snu_frame : SG.gp_frameP (snu_gp segs) snu_gfp.
Proof.
  intros id args E M M' HF H.
  destruct (Nat.eq_dec id 7) as [->|N7]; [|destruct (Nat.eq_dec id 8) as [->|N8]; [|destruct (Nat.eq_dec id 9) as [->|N9];
    [|destruct (Nat.eq_dec id 10) as [->|N10]]]].
  - destruct args as [|x [|n [|? ?]]]; cbn [map snu_gp snu_gfp] in *; try exact H.
    destruct H as (Hb & [H|H]); split; [exact Hb|left; exact H|exact Hb|right]. exact (topnz_frame M M' E x n Hb HF H).
  - destruct args as [|x [|n [|? ?]]]; cbn [map snu_gp snu_gfp] in *; try exact H.
    destruct H as (Hb & [H|[H|H]]); split; try exact Hb; [left; exact H|right; left; exact H|right; right].
    exact (topnz_frame M M' E x n Hb HF H).
  - destruct args as [|x [|n [|c [|? ?]]]]; cbn [map snu_gp snu_gfp] in *; try exact H.
    destruct H as (Hb & [H|[H|[H|H]]]); split; try exact Hb; [left; exact H|right; left; exact H|right; right; left; exact H|right; right; right].
    exact (topnz_frame M M' E x n Hb HF H).
  - destruct args as [|a [|? ?]]; cbn [map snu_gp snu_gfp] in *; try exact H.
    destruct H as (Ha & bs & Hr & Hnz). split; [exact Ha|]. exists bs. split; [|exact Hnz].
    pose proof (SNG.u_rng' (edenot E a)).
    rewrite (rdn_frame M M'); [exact Hr | rewrite SNG.u_small' by lia; cbn; lia |].
    intros y Hy. rewrite SNG.u_small' in Hy by lia. apply HF. exists (a, -8, ELit 8). split; [left; reflexivity|].
    cbn [SG.win_den]. assert (H8 : u (edenot E (ELit 8)) = 8) by reflexivity. rewrite H8. cbn in Hy. lia.
  - assert (Hg : forall MM, snu_gp segs id (map (edenot E) args) MM = SNG.sng_gp segs id (map (edenot E) args) MM).
    { intros MM. unfold snu_gp. destruct id as [|[|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]]; try reflexivity; try contradiction;
      destruct (map (edenot E) args) as [|a [|b [|c ?]]]; reflexivity. }
    assert (Hf : snu_gfp id args = SNG.sng_gfp id args).
    { unfold snu_gfp. destruct id as [|[|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]]; try reflexivity; try contradiction;
      destruct args as [|a [|b [|c ?]]]; reflexivity. }
    rewrite Hg in H. rewrite Hg. rewrite Hf in HF. exact (SNG.sng_frame segs id args E M M' HF H).
Qed.
End Frame.
End SNU.
