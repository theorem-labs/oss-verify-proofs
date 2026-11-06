(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngWk.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMWP AXG_ffstep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition callee_regs' : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

(* [comment removed for export] *)
Definition mw_post (HTOP : Z) (regs0 : bvmap 5 word) (m0 : word -> option byte) (L : layout) (s : astate) :
  @wpost (option sptr * astate) :=
  fun L' r R pc m' => exists p s', r = (Some p, s') /\ pc = wa 0x54a98 /\
    (forall k, In k callee_regs' -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (loc_addr L' (LMem p)) /\
    Heap0 L' s' m' /\ lext L L' s /\ rgeo HTOP L' s' /\
    mframe (bv_unsigned (getr regs0 2)) 8192 L s L' s' m0 m' /\ stk_ok SEGS m' (getr regs0 2) 8192.   (* [comment removed for export] *)
