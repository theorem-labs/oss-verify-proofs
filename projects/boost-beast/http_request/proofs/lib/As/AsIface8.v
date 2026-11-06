(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface7 AsCXXHeap.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition AWILDB : Z := 2 ^ 20.          (* [comment removed for export] *)

Section Iface8.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition asan_rt_hyps8 : Prop :=
       (forall n, 0 <= n -> as_Cf H n <= as_Cm H n)
    /\ ACWILD <= as_Cm H AWILDB.

  (* [comment removed for export] *)
  Lemma hyps8_realloc_round : asan_rt_hyps H -> asan_rt_hyps8 ->
    forall A newcap oldcap, 0 <= A -> 0 <= newcap -> 0 <= oldcap ->
    as_Cm H newcap + as_Cf H oldcap + ACWILD <= as_Cm H (A + (newcap + oldcap + AWILDB)) - as_Cm H A.
  Proof.
    intros HH [CF CW] A newcap oldcap HA HN HO.
    pose proof (ah_costs H HH) as (Cm0 & CmM & Cf0 & CfM & CmS & CfS).
    assert (W0 : 0 <= AWILDB) by (unfold AWILDB; lia).
    pose proof (CF oldcap HO) as K1.
    pose proof (CmS newcap oldcap HN HO) as K2.
    pose proof (CmS (newcap + oldcap) AWILDB ltac:(lia) W0) as K3.
    pose proof (CmS A (newcap + oldcap + AWILDB) HA ltac:(lia)) as K4.
    lia.
  Qed.
End Iface8.
