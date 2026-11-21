(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7ltab InfB_w7lenr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).

  Definition L_L1 (cx : ictx) (ly : ilay) (st : ist) (k : ltk) (ci H B : Z) (x10 x13 x23 x26 x29 x30 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (8 * (c_n cx - ci))) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (H mod 2 ^ t_lb st)) x13 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 B) (Z_to_bv 64 (lt_TA (c_p cx) k)) (Z_to_bv 64 1)
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (Z.shiftl (c_n cx - t_cin st) 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H)
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) x29 x30 (Z_to_bv 64 (c_n cx - ci)))
       FR (Z_to_bv 64 0x91620) fc None m (seg_rom bsegs).

  Definition L_E1 (cx : ictx) (ly : ilay) (st : ist) (k : ltk) (c ci H B : Z) (x10 x13 x23 x26 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (8 * (c_n cx - ci))) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 c) x13 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 B) (Z_to_bv 64 (lt_TA (c_p cx) k)) (Z_to_bv 64 1)
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (Z.shiftl (c_n cx - t_cin st) 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H)
            (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 x26 (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 (code_bits c)) (Z_to_bv 64 (c_n cx - ci)))
       FR (Z_to_bv 64 0x9170c) fc None m (seg_rom bsegs).
End S.
End CANSEC1.
