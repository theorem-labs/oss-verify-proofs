(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Class RunRandom : Type := mkRunRandom {
  rr_canary : Z;
  rr_secret : Z;
  rr_canary_range : 0 <= rr_canary < 2 ^ 64;
  rr_secret_range : 0 <= rr_secret < 2 ^ 64;

  rr_canary_byte1 : Z.land rr_canary 0xff00 = 0
}.

Definition rr_canary_of (rnd : bv 128) : Z :=
  Z.land (bv_unsigned (bv_extract 0 64 rnd)) (2 ^ 64 - 1 - 0xff00).
Definition rr_secret_of (rnd : bv 128) : Z := bv_unsigned (bv_extract 64 64 rnd).

Lemma rr_canary_of_range : forall rnd, 0 <= rr_canary_of rnd < 2 ^ 64.
Proof.
  intros rnd. unfold rr_canary_of. pose proof (bv_unsigned_in_range 64 (bv_extract 0 64 rnd)) as [H1 H2].
  unfold bv_modulus in H2. split.
  - apply Z.land_nonneg. left. exact H1.
  - set (x := bv_unsigned (bv_extract 0 64 rnd)).
    assert (E : Z.land x (2 ^ 64 - 1 - 0xff00) = Z.land (Z.land x (2 ^ 64 - 1 - 0xff00)) (Z.ones 64)).
    { rewrite <- Z.land_assoc. f_equal. }
    rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma rr_secret_of_range : forall rnd, 0 <= rr_secret_of rnd < 2 ^ 64.
Proof. intros rnd. unfold rr_secret_of. pose proof (bv_unsigned_in_range 64 (bv_extract 64 64 rnd)) as H. unfold bv_modulus in H. exact H. Qed.

Lemma rr_canary_of_byte1 : forall rnd, Z.land (rr_canary_of rnd) 0xff00 = 0.
Proof.
  intros rnd. unfold rr_canary_of. rewrite <- Z.land_assoc.
  change (Z.land (2 ^ 64 - 1 - 0xff00) 0xff00) with 0. apply Z.land_0_r.
Qed.

Definition rr_of_rnd (rnd : bv 128) : RunRandom :=
  mkRunRandom (rr_canary_of rnd) (rr_secret_of rnd)
    (rr_canary_of_range rnd) (rr_secret_of_range rnd) (rr_canary_of_byte1 rnd).

Definition rr_of_draw (d : EntryDraw) : RunRandom := rr_of_rnd (ed_random d).

Section WithRR.
Context {RRND : RunRandom}.

End WithRR.
