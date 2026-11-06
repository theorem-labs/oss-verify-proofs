(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc MallocRep.
Import ListNotations.
Open Scope Z_scope.

Class run_params := RunParams {
  rp_secret : Z;
  rp_canary : Z;
  rp_ceil : Z;
  rp_secret_range : 0 <= rp_secret < 2^64;
  rp_canary_range : 0 <= rp_canary < 2^64;
  rp_ceil_ok : ceil_ok rp_ceil }.

Section RP. Context {hRP : run_params}.

(* [comment removed for export] *)
Definition rceil : Z := rp_ceil.

#[using="Type"] Lemma rceil_bounds : 0x7fff7f800000 <= rceil <= 0x7fffff800000.
Proof. pose proof rp_ceil_ok as H. unfold ceil_ok, ALLOC_CEIL_LO, ALLOC_CEIL_HI in H. unfold rceil. exact H. Qed.

#[using="Type"] Lemma rceil_ok : ceil_ok rceil.
Proof. exact rp_ceil_ok. Qed.

(* [comment removed for export] *)
Definition rW_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> rceil <= lo.

#[using="Type"] Lemma rW_high_disjoint : forall W a n, rW_high W -> a + n <= rceil -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

End RP.

(* [comment removed for export] *)
Ltac rceilb :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= rceil <= 0x7fffff800000 |- _ => idtac
  | _ => let H := fresh "RCB" in pose proof rceil_bounds as H
  end.
