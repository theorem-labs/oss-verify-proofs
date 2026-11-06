(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface7 AsIface8 AS_InstDefs.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Laws8.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Theorem inst_rt_hyps8 : asan_rt_hyps8 (KHp p).
  Proof.
    unfold asan_rt_hyps8. cbn [as_Cm as_Cf KHp]. unfold ICm, ICf, ACWILD, AWILDB. split.
    - intros n Hn. destruct (n <=? 64512); lia.
    - change (2 ^ 20 <=? 64512) with false. cbv iota. apply Z.le_refl.
  Qed.
End Laws8.
