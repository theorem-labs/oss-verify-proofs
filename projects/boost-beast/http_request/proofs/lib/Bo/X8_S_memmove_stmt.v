(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition amemmove_fwd_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (src junk : list byte) (lo : Z),
      bytes_at bsegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
      rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
      bv_unsigned a0 < bv_unsigned a1 ->                                              (* [comment removed for export] *)
      accessible m (bv_unsigned a1) (bv_unsigned a2) -> accessible m (bv_unsigned a0) (bv_unsigned a2) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv bsegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
      aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt bsegs (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

  Definition asan_memmove_fwd_stmt : Prop := amemmove_fwd_stmt_at AASAN_MEMMOVE.
End HCW.
