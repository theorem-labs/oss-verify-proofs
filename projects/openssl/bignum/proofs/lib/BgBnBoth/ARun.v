(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem RzCPS.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface RT_iface2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LIBW_A : list (Z * Z) := [(0x5e2880, 0x5e3360); (0xbd20c0, 0xbd64e0); (0xbf81a0, 0xbf8598)].

Class ARun : Type := mkARun {
  ar_RT : rt_sig;
  ar_RC : rt_contracts ar_RT;
  ar_SP0 : Z;
  ar_PMc : Model -> Prop;
  ar_PMc_fdfs : fdfs_only ar_PMc;
  ar_PMc_ms : mat_stable ar_PMc;
  ar_LIBW_cs : forall x, rin_ivs LIBW_A x -> client_static x;

  ar_FR : list (Z * nat);
  ar_RC2 : rt_contracts2 ar_RT
}.

Definition ar_AF {AR : ARun} : art_facts ar_RT := rc_facts ar_RT ar_RC.
