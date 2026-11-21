(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface Z_dend Z_dinit_kit Z_dinit_model Z_dreset Z_dendk Z_dinit_pieces.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Deflate RefDeflateInitLib RefDeflSafeI5b HarnessSmall ZApiInst ZApiOk DeflateTaintRel ZTaint BoundPat ZPat FillWinModel DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation MP := (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.Monad.M PState).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section DINIT_TAIL.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HTRI : tr_init_stmt.
  Local Notation dinit_failH := (dinit_fail FREE HND HBR HBD HFRAME).
  Local Notation dinit_env_munchH := (dinit_env_munch HBR HFRAME).
  Local Notation dinit_pres_munchH := (dinit_pres_munch HND HBR HBD).
  Local Notation buf_inH := (buf_in HBR).
  Local Notation buf_disjH := (buf_disj HND HBR HBD).
  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).
  Local Transparent the_zapi.

  Definition sx5 (jks : list byte) : deflate_state := s_lbs (s_setup (orc jks) 0%N dinit_cs 1 15 8) 8.

  Definition G5 (jks jkw jkp jkh jkb : list byte) (k : N) : Z -> Z :=
    match k with 0%N => orc jks | 1%N => orc jkw | 2%N => orc jkp | 3%N => orc jkh | _ => orc jkb end.

End DINIT_TAIL.
End WithCeiling0.
