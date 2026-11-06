(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/Shadow.v, with its module paths changed; 1 of its 79 lines of code is new or changed. *)
(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/Shadow.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib Require Import PropExec MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SHB : Z := 2147450880.   (* [comment removed for export] *)
Definition shad (a : Z) : Z := a / 8 + SHB.

Definition sh_ok (b : byte) (a : Z) : Prop :=
  bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ a mod 8 < bv_unsigned b).

Definition acc (segs : list Segment) (m : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> exists b, bytes_at segs m (shad (a + i)) [b] /\ sh_ok b (a + i).

Definition z8 : byte := Z_to_bv 8 0.

(* [comment removed for export] *)
Definition ushadow (n : Z) : list byte :=
  repeat z8 (Z.to_nat (n / 8)) ++ (if Z.eqb (n mod 8) 0 then [] else [Z_to_bv 8 (n mod 8)]).

Section Intro.
Variable segs : list Segment.

Lemma bytes_at_nth1 : forall m A bs j b,
  bytes_at segs m A bs -> nth_error bs j = Some b -> bytes_at segs m (A + Z.of_nat j) [b].
Proof.
  intros m A bs j b (HA & Hl & H) Hn.
  assert (Hj : (j < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i.
  replace (A + Z.of_nat j + Z.of_nat 0) with (A + Z.of_nat j) by lia. rewrite (H j Hj). exact Hn.
Qed.

Lemma shad_aligned_add : forall a i, a mod 8 = 0 -> 0 <= i -> shad (a + i) = shad a + i / 8.
Proof.
  intros a i Ha Hi. unfold shad.
  assert (E : a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia).
  rewrite E. rewrite Z.mul_comm.
  replace (a / 8 * 8 + i) with (i + a / 8 * 8) by lia. rewrite Z.div_add by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_zero_run : forall m a k,
  a mod 8 = 0 -> 0 <= a ->
  bytes_at segs m (shad a) (repeat z8 k) -> acc segs m a (8 * Z.of_nat k).
Proof.
  intros m a k Ha Ha0 Hb i Hi. exists z8. split; [| left; reflexivity].
  rewrite (shad_aligned_add a i Ha ltac:(lia)).
  replace (i / 8) with (Z.of_nat (Z.to_nat (i / 8))) by (rewrite Z2Nat.id; [reflexivity| apply Z.div_pos; lia]).
  apply (bytes_at_nth1 m _ (repeat z8 k)); [exact Hb|].
  apply nth_error_repeat. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
  apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma acc_ushadow : forall m a n,
  a mod 8 = 0 -> 0 <= a -> 0 <= n ->
  bytes_at segs m (shad a) (ushadow n) -> acc segs m a n.
Proof.
  intros m a n Ha Ha0 Hn Hb. unfold ushadow in Hb. apply bytes_at_app in Hb. destruct Hb as [Hz Hp].
  pose proof (acc_zero_run m a _ Ha Ha0 Hz) as Hacc. rewrite Z2Nat.id in Hacc by (apply Z.div_pos; lia).
  intros i Hi. destruct (Z_lt_dec i (8 * (n / 8))) as [Hlt|Hge].
  - apply Hacc. lia.
  - assert (Hr : n mod 8 <> 0).
    { intros E. pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
    rewrite <- Z.eqb_neq in Hr. rewrite Hr in Hp. rewrite Z.eqb_neq in Hr.
    rewrite repeat_length, Z2Nat.id in Hp by (apply Z.div_pos; lia).
    exists (Z_to_bv 8 (n mod 8)). split.
    + rewrite (shad_aligned_add a i Ha ltac:(lia)).
      replace (i / 8) with (n / 8).
      * exact Hp.
      * pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
        apply Z.div_unique with (r := i - 8 * (n / 8)); [left|]; lia.
    + right. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
      rewrite Z_to_bv_small. 2:{ unfold bv_modulus. change (Z.of_N 8) with 8%Z. lia. }
      split; [lia|].
      pose proof (Z.div_mod n 8 ltac:(lia)).
      assert (Ea : (a + i) mod 8 = i mod 8).
      { replace (a + i) with (i + (a / 8) * 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia).
        apply Z.mod_add; lia. }
      rewrite Ea. replace i with (i - 8 * (n / 8) + (n / 8) * 8) at 1 by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma acc_sub : forall m a n a' n', acc segs m a n -> a <= a' -> a' + n' <= a + n -> acc segs m a' n'.
Proof.
  intros m a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

End Intro.
