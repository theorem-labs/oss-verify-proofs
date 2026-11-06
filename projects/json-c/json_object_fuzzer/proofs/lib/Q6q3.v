(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QxOB.

Class RunConsts : Type := mkRunConsts {
rc_ceil   : Z;
rc_canary : word;
rc_secret : Z;
rc_ceil_range : (0x7fff7f800000 <= rc_ceil <= 0x7fffff800000)%Z;
rc_ceil_al16 : (rc_ceil mod 16 = 0)%Z;
rc_secret_range : (0 <= rc_secret < 2^64)%Z
}.

Definition alloc_ceiling {RC__ : RunConsts} : Z := rc_ceil.

Section RCFacts.
Context {RC__ : RunConsts}.

#[using="Type"] Lemma alloc_ceiling_val : alloc_ceiling = rc_ceil.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alloc_ceiling_range : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.
Proof. exact rc_ceil_range. Qed.

#[using="Type"] Lemma alloc_ceiling_ge : (0x7fff7f800000 <= alloc_ceiling)%Z.
Proof. exact (proj1 rc_ceil_range). Qed.

#[using="Type"] Lemma alloc_ceiling_le : (alloc_ceiling <= 0x7fffff800000)%Z.
Proof. exact (proj2 rc_ceil_range). Qed.

#[using="Type"] Lemma alloc_ceiling_lt : (alloc_ceiling < 2^63)%Z.
Proof. pose proof rc_ceil_range. unfold alloc_ceiling. lia. Qed.

#[using="Type"] Lemma alloc_ceiling_small : (alloc_ceiling + 2^48 < 2^63)%Z.
Proof. pose proof rc_ceil_range. unfold alloc_ceiling. lia. Qed.

#[using="Type"] Lemma alloc_ceiling_pos : (0 < alloc_ceiling)%Z.
Proof. pose proof rc_ceil_range. unfold alloc_ceiling. lia. Qed.

#[using="Type"] Lemma alloc_ceiling_al16 : (alloc_ceiling mod 16 = 0)%Z.
Proof. exact rc_ceil_al16. Qed.
End RCFacts.

Ltac rc_pose_range i :=
lazymatch goal with
| _ : (_ <= @rc_ceil i <= _)%Z |- _ => idtac
| _ => pose proof (@rc_ceil_range i)
end.

Ltac rc_lia_prep :=
try progress unfold alloc_ceiling in *;
match goal with
| |- context [@rc_ceil ?i] => rc_pose_range i
| _ : context [@rc_ceil ?i] |- _ => rc_pose_range i
| _ => idtac
end.

Ltac lia ::= term_slim ltac:(
rc_lia_prep;
first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_prune; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ]). Ltac mkr__lia_0 := term_slim ltac:(
rc_lia_prep;
first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_prune; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ]).

Ltac nia ::= term_slim ltac:(rc_lia_prep; Zify.zify; xnia zchecker). Ltac mkr__nia_1 := term_slim ltac:(rc_lia_prep; Zify.zify; xnia zchecker).
