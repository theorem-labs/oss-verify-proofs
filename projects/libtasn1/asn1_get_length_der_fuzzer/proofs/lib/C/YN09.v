(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK0o YK0j YK15 YK18.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState}.

Theorem shape_strong_equiv_efs_budgets :
forall (ls lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput),
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd ls inp) T ->
srealizes target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) T' ->
t_eq T T' ->
strong_equiv_error_free_budgets ls lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros ls lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp Hs Ht Heq.
unfold strong_equiv_error_free_budgets, error_free. cbn.
split; [| split].
- eapply realizes_no_error; exact Hs.
- eapply srealizes_no_error; exact Ht.
- intro tr.
rewrite (realizes_obs_iff source_segs _ T Hs tr).
rewrite (srealizes_obs_iff target_segs _ T' Ht tr).
apply Heq.
Qed.
End a.
