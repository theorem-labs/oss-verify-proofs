(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit F_atof_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma atof_185_evt : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo s : Z),
  bytes_at asegs m s [Z_to_bv 8 49; Z_to_bv 8 56; Z_to_bv 8 53; Z_to_bv 8 0] ->
  io_ssp m -> mem_inv asegs m -> stk asegs m lo usp ->
  lo + ATOF_STACK <= usp -> usp <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo -> 0 < s -> s + 4 <= lo ->
  evt asegs (atof_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m usp lo 4640713125400674304)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 F_ATOF) fc None m (seg_rom asegs)).
Proof.
  intros until s. intros TOK SSP MI ST LO UHI SAL LOH S0 SLO.
  destruct SSP as (g & SSP1 & SSP2).
  unfold F_ATOF, ATOF_STACK in *.
  pose proof (munch_refl [(usp - 8832, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  cwalk (@nil Z).
  carve_frame 4096%nat ST.          (* [comment removed for export] *)
  cwalk (@nil Z).
  tok_read 0 (Z_to_bv 8 49).
  cwalk (@nil Z).
  tok_read 1 (Z_to_bv 8 56).
  cwalk (@nil Z).
  tok_read 2 (Z_to_bv 8 53).
  cwalk (@nil Z).
  tok_read 3 (Z_to_bv 8 0).
  cwalk (@nil Z).
  atof_finish usp MU WM MI.
Qed.
