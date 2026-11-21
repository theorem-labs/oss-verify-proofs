(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (POST : machine_state -> Prop).

  Lemma six_a : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA val rb op H : Z),
    0 <= H < 18446744073709551616 -> 1 <= rb <= 15 -> 1 <= op -> rb + op <= 15 -> 0 <= val < 65536 -> 0 <= TA < 140737488355328 ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 val) x7 x8 x9 x10 (Z_to_bv 64 (TA + 4 * (H mod 2 ^ (rb + op) / 2 ^ rb + val))) (Z_to_bv 64 (rb + op)) x13 x14 (Z_to_bv 64 TA) (Z_to_bv 64 rb) x17 x18 x19 (Z_to_bv 64 H) x25 x22 x23 x24 x20 x21 x27 (Z_to_bv 64 (2 ^ (rb + op) - 1)) x29 x30 x31) FR (Z_to_bv 64 0x91394) fc None m (seg_rom asegs)) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 val) x7 x8 x9 x10 x11 (Z_to_bv 64 op) x13 x14 (Z_to_bv 64 TA) (Z_to_bv 64 rb) x17 x18 x19 (Z_to_bv 64 H) x25 x22 x23 x24 x20 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x9136c) fc None m (seg_rom asegs)).
  Proof.
    intros until H. intros HH RB OP1 OP15 VAL TAR K.
    pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (mod_pow2_bound H (rb + op) ltac:(lia)) as MR. pose proof (sidx_range rb op H ltac:(lia) ltac:(lia)) as JR.
    zs. zs. zs. zs.
    rewrite (mask_sllw (rb + op)) by lia.
    zs. rewrite (InfAGlue_w7.land_mask_mod H (rb + op)) by lia.
    zs. rewrite (srlw_wrap_small (H mod 2 ^ (rb + op)) rb) by lia.
    zs. zs. zs. rewrite (zext32_shift30 (H mod 2 ^ (rb + op) / 2 ^ rb + val)) by lia.
    zs.
    exact K.
  Time Qed.

  Lemma six_b : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA val rb op H : Z),
    0 <= H < 18446744073709551616 -> 1 <= rb <= 15 -> 1 <= op -> rb + op <= 15 -> 0 <= val < 65536 -> 0 <= TA < 140737488355328 ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 val) x7 x8 x9 x10 (Z_to_bv 64 (TA + 4 * (H mod 2 ^ (rb + op) / 2 ^ rb + val))) x12 x13 x14 (Z_to_bv 64 TA) (Z_to_bv 64 rb) x17 x18 x19 (Z_to_bv 64 H) x25 x22 x23 x24 x20 x21 x27 (Z_to_bv 64 (2 ^ (rb + op) - 1)) x29 x30 x31) FR (Z_to_bv 64 0x91408) fc None m (seg_rom asegs)) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 val) x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 TA) (Z_to_bv 64 rb) x17 x18 x19 (Z_to_bv 64 H) x25 x22 x23 x24 x20 x21 x27 (Z_to_bv 64 (2 ^ (rb + op) - 1)) x29 x30 x31) FR (Z_to_bv 64 0x913f0) fc None m (seg_rom asegs)).
  Proof.
    intros until H. intros HH RB OP1 OP15 VAL TAR K.
    pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (mod_pow2_bound H (rb + op) ltac:(lia)) as MR. pose proof (sidx_range rb op H ltac:(lia) ltac:(lia)) as JR.
    zs. rewrite (InfAGlue_w7.land_mask_mod H (rb + op)) by lia.
    zs. rewrite (srlw_wrap_small (H mod 2 ^ (rb + op)) rb) by lia.
    zs. zs. zs. rewrite (zext32_shift30 (H mod 2 ^ (rb + op) / 2 ^ rb + val)) by lia.
    zs.
    exact K.
  Time Qed.
End S.
End CANSEC1.
