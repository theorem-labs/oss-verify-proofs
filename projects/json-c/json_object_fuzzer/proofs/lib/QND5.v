(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1.
Import ListNotations.
Open Scope bv_scope.

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
unfold bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.

Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.

Lemma rdn_addr_eq : forall segs m (a b : word) n r,
a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.

Ltac rdn_at b :=
apply (rdn_addr_eq _ _ _ b);
[ first [ f_equal; lia
| lazymatch goal with |- ?g => QJ4Q.Mq0.check_closed_term g end;
apply bv_eq; vm_compute; reflexivity ]
| ].

Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
match n with
| O => true
| S n' => if f z then zall n' f (z + 1)%Z else false
end.

Ltac rdn_at_hyp Hb :=
lazymatch type of Hb with
| rdn _ _ ?b _ = _ => rdn_at b; exact Hb
end.
