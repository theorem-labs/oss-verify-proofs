(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).

  Definition at_latch (ci' co' hold' bits' : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 : word) (fo' : Z -> Z),
      ms' = oms SP Zs S D n OB osz la da gp tp FR fc x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 ci' co' hold' bits' 0x97f98 m' /\ INV m' fo'.

  Definition wst (x5 x6 x7 x10 x11 x24 x29 : word) (len dist op ci co hold bits pc : Z) (m : amem) : machine_state :=
    gms SP Zs S D n OB osz la da gp tp FR fc x5 x6 x7 x10 x11 (Z_to_bv 64 wnext) (Z_to_bv 64 len) x24 (Z_to_bv 64 op) x29 (Z_to_bv 64 dist)
        ci co hold bits pc m.

  Definition if_window_stmt : Prop :=
    if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 ->
    forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x24 x29 : word) (len dist op ci co hold bits : Z),
    INV m fo -> wsz <> 0 -> 3 <= len <= 258 -> 1 <= dist <= 32768 -> op = dist - (co - bo) -> 1 <= op <= whave -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (at_latch ci (co + len) hold bits) (wst x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits 0x9823c m).
End P.
End CANSEC1.
