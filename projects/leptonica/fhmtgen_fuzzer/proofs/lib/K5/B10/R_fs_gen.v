(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import R_fs_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac fs_cases c :=
  let H := fresh "Hcase" in
  assert (H : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10) by lia;
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; subst c.
Ltac fs_cases_nat k :=
  let H := fresh "Hcase" in
  assert (H : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10)%nat) by lia;
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; subst k.
(* [comment removed for export] *)
Ltac fs_norm :=
  repeat match goal with
  | |- context [NF ?c] => let v := eval vm_compute in (NF c) in progress change (NF c) with v in *
  | |- context [fsz ?c] => let v := eval vm_compute in (fsz c) in progress change (fsz c) with v in *
  | |- context [flags_off ?c] => let v := eval vm_compute in (flags_off c) in progress change (flags_off c) with v in *
  | H : context [NF ?c] |- _ => let v := eval vm_compute in (NF c) in progress change (NF c) with v in *
  | H : context [fsz ?c] |- _ => let v := eval vm_compute in (fsz c) in progress change (fsz c) with v in *
  | H : context [flags_off ?c] |- _ => let v := eval vm_compute in (flags_off c) in progress change (flags_off c) with v in *
  end.

Lemma NF_g : forall c, 0 <= c <= 10 -> 16 <= NF c <= 16384.
Proof. intros c Hc. fs_cases c; fs_norm; lia. Qed.
Lemma fsz_g : forall c, 0 <= c <= 10 -> 64 <= fsz c <= 65536 /\ fsz c = 8 * (fsz c / 8) /\ fsz c = 64 * (fsz c / 64).
Proof. intros c Hc. fs_cases c; vm_compute; repeat split; discriminate. Qed.
Lemma NF_fsz_g : forall c, 0 <= c <= 10 -> NF c * fsz c = 2 ^ 20.
Proof. intros c Hc. fs_cases c; reflexivity. Qed.
Lemma flags_off_g : forall c, 0 <= c <= 10 -> 0 <= flags_off c /\ flags_off c + NF c <= 32752.
Proof. intros c Hc. fs_cases c; fs_norm; lia. Qed.
Lemma flags_off_step : forall c, 0 <= c <= 10 -> flags_off c + NF c = flags_off (c + 1).
Proof. intros c Hc. fs_cases c; reflexivity. Qed.
Lemma flags_off_mono : forall c c', 0 <= c -> c < c' -> c' <= 10 -> flags_off c + NF c <= flags_off c'.
Proof.
  intros c c' H0 Hlt H10.
  assert (M : forall n : nat, forall a, 0 <= a -> a + Z.of_nat n <= 10 -> flags_off a <= flags_off (a + Z.of_nat n)).
  { induction n as [|n IH]; intros a Ha Hb; [rewrite Z.add_0_r; lia|].
    pose proof (flags_off_step a ltac:(lia)) as E. pose proof (NF_g a ltac:(lia)) as N.
    pose proof (IH (a + 1) ltac:(lia) ltac:(lia)) as I. replace (a + Z.of_nat (S n)) with (a + 1 + Z.of_nat n) by lia. lia. }
  rewrite (flags_off_step c ltac:(lia)).
  pose proof (M (Z.to_nat (c' - (c + 1))) (c + 1) ltac:(lia) ltac:(lia)) as X.
  replace (c + 1 + Z.of_nat (Z.to_nat (c' - (c + 1)))) with c' in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma frame_cls_range_g : forall FSB c p, 0 <= c <= 10 -> 0 <= p < NF c ->
  FSB + 0x9000 + c * 2 ^ 20 <= frame_addr FSB c p /\ frame_addr FSB c p + fsz c <= FSB + 0x9000 + c * 2 ^ 20 + 2 ^ 20.
Proof. intros FSB c p Hc Hp. unfold frame_addr. fs_cases c; fs_norm; lia. Qed.

Lemma frame_addr_range_g : forall FSB c p, 0 <= c <= 10 -> 0 <= p < NF c ->
  FSB + 0x9000 <= frame_addr FSB c p /\ frame_addr FSB c p + fsz c <= FSB + kFakeStackSize.
Proof. intros FSB c p Hc Hp. pose proof (frame_cls_range_g FSB c p Hc Hp). unfold kFakeStackSize. lia. Qed.

Lemma fl_base_range_g : forall FSB c p, 0 <= c <= 10 -> 0 <= p < NF c ->
  FSB + 0x1000 <= fl_base FSB c + p /\ fl_base FSB c + p + 1 <= FSB + 0x9000.
Proof. intros FSB c p Hc Hp. unfold fl_base. pose proof (flags_off_g c Hc). lia. Qed.

Lemma frames_apart_all_g : forall FSB c c' p q, 0 <= c <= 10 -> 0 <= c' <= 10 ->
  0 <= p < NF c -> 0 <= q < NF c' -> (c <> c' \/ p <> q) ->
  frame_addr FSB c p + fsz c <= frame_addr FSB c' q \/ frame_addr FSB c' q + fsz c' <= frame_addr FSB c p.
Proof.
  intros FSB c c' p q Hc Hc' Hp Hq Hne.
  destruct (Z.eq_dec c c') as [E|NE].
  - subst c'. unfold frame_addr. fs_cases c; fs_norm; lia.
  - pose proof (frame_cls_range_g FSB c p Hc Hp). pose proof (frame_cls_range_g FSB c' q Hc' Hq). lia.
Qed.

Lemma frame_mod64_g : forall FSB c p, FSB mod 4096 = 0 -> 0 <= c <= 10 -> frame_addr FSB c p mod 64 = 0.
Proof.
  intros FSB c p HF Hc. unfold frame_addr.
  assert (E : FSB = 4096 * (FSB / 4096)) by (apply Z.div_exact; lia).
  set (f := FSB / 4096) in *. rewrite E.
  fs_cases c; fs_norm; apply Z.mod_divide; try lia;
    [exists (64 * f + 576 + 0 * 16384 + p)| exists (64 * f + 576 + 1 * 16384 + p * 2)| exists (64 * f + 576 + 2 * 16384 + p * 4)
    | exists (64 * f + 576 + 3 * 16384 + p * 8)| exists (64 * f + 576 + 4 * 16384 + p * 16)| exists (64 * f + 576 + 5 * 16384 + p * 32)
    | exists (64 * f + 576 + 6 * 16384 + p * 64)| exists (64 * f + 576 + 7 * 16384 + p * 128)| exists (64 * f + 576 + 8 * 16384 + p * 256)
    | exists (64 * f + 576 + 9 * 16384 + p * 512)| exists (64 * f + 576 + 10 * 16384 + p * 1024)]; lia.
Qed.

(* [comment removed for export] *)
Lemma frame_shad_in_g : forall FSB c p, FSB mod 4096 = 0 -> 0 <= c <= 10 -> 0 <= p < NF c ->
  shad FSB + 0x1200 + c * 2 ^ 17 <= shad (frame_addr FSB c p)
  /\ shad (frame_addr FSB c p) + fsz c / 8 <= shad FSB + 0x1200 + c * 2 ^ 17 + 2 ^ 17.
Proof.
  intros FSB c p HF Hc Hp. rewrite shad_frame by lia. unfold shad.
  fs_cases c; fs_norm; change (2 ^ 17) with 131072;
    repeat match goal with |- context [?a / 8] => lazymatch a with FSB => fail | _ => let v := eval vm_compute in (a / 8) in change (a / 8) with v end end; lia.
Qed.

Lemma shad_fsb_end_g : forall FSB, shad (FSB + 0xb09000) = shad FSB + 0x161200.
Proof. intros FSB. unfold shad. replace (FSB + 0xb09000) with (FSB + 0x161200 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma frame_shad_in2_g : forall FSB c p, FSB mod 4096 = 0 -> 0 <= c <= 10 -> 0 <= p < NF c ->
  shad FSB <= shad (frame_addr FSB c p) /\ shad (frame_addr FSB c p) + fsz c / 8 <= shad (FSB + 0xb09000).
Proof.
  intros FSB c p HF Hc Hp. pose proof (frame_shad_in_g FSB c p HF Hc Hp) as (S1 & S2). rewrite shad_fsb_end_g.
  change (2 ^ 17) with 131072 in *. lia.
Qed.

Lemma frame_shads_apart_all_g : forall FSB c c' p q, FSB mod 4096 = 0 -> 0 <= c <= 10 -> 0 <= c' <= 10 ->
  0 <= p < NF c -> 0 <= q < NF c' -> (c <> c' \/ p <> q) ->
  shad (frame_addr FSB c p) + fsz c / 8 <= shad (frame_addr FSB c' q) \/ shad (frame_addr FSB c' q) + fsz c' / 8 <= shad (frame_addr FSB c p).
Proof.
  intros FSB c c' p q HF Hc Hc' Hp Hq Hne.
  destruct (Z.eq_dec c c') as [E|NE].
  - subst c'. rewrite !shad_frame by lia. fs_cases c; fs_norm;
      repeat match goal with |- context [?a / 8] => lazymatch a with FSB => fail | _ => let v := eval vm_compute in (a / 8) in change (a / 8) with v end end; lia.
  - pose proof (frame_shad_in_g FSB c p HF Hc Hp). pose proof (frame_shad_in_g FSB c' q HF Hc' Hq). change (2 ^ 17) with 131072 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cls_nat_g : forall k : nat, (k <= 10)%nat -> 0 <= Z.of_nat k <= 10.
Proof. intros k Hk. lia. Qed.
