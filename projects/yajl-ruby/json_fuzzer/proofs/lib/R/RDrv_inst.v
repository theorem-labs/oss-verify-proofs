(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import KLink.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RAlloc_rz RDrv_iface RDrv_ctx.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Theorem drv_iface_R : drv_iface RHKG.
Proof.
  constructor.
  - intros G s LB m mo H. exact (RHKG_G G s LB m mo H).
  - intros G G' s LB m mo H HGG. exact (RHKG_weak G G' s LB m mo H HGG).
  - intros G s LB m mo n rsp mo' evs H LF ST VM HG. exact (RHKG_mo G s LB m mo n rsp mo' evs H LF ST VM HG).
  - intros G s LB m mo H. exact (RHKG_run G s LB m mo H).
  - intros G s LB m mo H. exact (RHKG_ssp G s LB m mo H).
  - intros G s LB m mo H. exact (libc_head_cells m (RHKG_need_locks G s LB m mo H)).
  - intros G s LB LB' m mo H P. exact (RHKG_perm G s LB LB' m mo H P).
  - intros G s LB m m' mo W H MU WM FW. exact (RHKG_frame G s LB m m' mo W H MU WM FW).
  - intros G s LB m mo H. exact (RHKG_blocks G s LB m mo H).
  - intros G FG. exact (rmalloc_rz G FG).
  - intros G FG. exact (rfree_rz G FG).
Qed.

End RC__1.
