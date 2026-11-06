(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem RzCPS.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import RT_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import LibKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIBW_A : list (Z * Z) := [(0x5ade60, 0x5ae680); (0xba32c0, 0xba7780); (0xbc9440, 0xbc9838)].

Class ARun : Type := mkARun {
  ar_RT : rt_sig;
  ar_RC : rt_contracts ar_RT;          (* [comment removed for export] *)
  ar_SP0 : Z;
  ar_PMc : Model -> Prop;
  ar_PMc_fdfs : fdfs_only ar_PMc;
  ar_PMc_ms : mat_stable ar_PMc;
  ar_LIBW_cs : forall x, rin_ivs LIBW_A x -> client_static x
}.

(* [comment removed for export] *)
Definition ar_AF {AR : ARun} : art_facts ar_RT := rc_facts ar_RT ar_RC.
