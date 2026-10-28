(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem RzCPS Nodes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIBW_A : list (Z * Z) := [(0x5aebe0, 0x5af400); (0xba46c0, 0xba8ae0); (0xba934c, 0xba9350); (0xba935a, 0xba935b); (0xba9390, 0xba9398); (0xbca7a0, 0xbcab98)]. (* [comment removed for export] *)

Class ARun : Type := mkARun {
  ar_RT : rt_sig;
  ar_RC : rt_contracts ar_RT;          (* [comment removed for export] *)
  ar_SP0 : Z;
  ar_PMc : Model -> Prop;
  ar_PMc_fdfs : fdfs_only ar_PMc;
  ar_PMc_ms : mat_stable ar_PMc;
  ar_LIBW_cs : forall x, rin_ivs LIBW_A x -> client_static x;
  (* [comment removed for export] *)
  ar_FR : list (Z * nat);              (* [comment removed for export] *)
  ar_RC2 : rt_contracts2 ar_RT         (* [comment removed for export] *)
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition ar_AF {AR : ARun} : art_facts ar_RT := rc_facts ar_RT ar_RC.
