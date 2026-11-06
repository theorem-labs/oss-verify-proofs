(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.




From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import LeptC_cmapvalid_N0 LeptC_cmapvalid_P0 LeptC_cmapvalid_N16 LeptC_cmapvalid_P16.

Section CV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis STDERR : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis MAXIDX : pixGetMaxColorIndex_cps RT.

Theorem pixcmapIsValid_ok : pixcmapIsValid_cps RT.
Proof using AF GP STDERR RERR MAXIDX.
  unfold pixcmapIsValid_cps. intros.
  destruct (Z.eq_dec (bv_unsigned sp mod 32) 0) as [CASEH|CASEH]; destruct (Z.eq_dec pix 0) as [CASEX|CASEX].
  - eapply (pixcmapIsValid_ok_N0 RT AF GP STDERR RERR MAXIDX); first [eassumption | split; assumption].
  - eapply (pixcmapIsValid_ok_P0 RT AF GP STDERR RERR MAXIDX); first [eassumption | split; assumption].
  - eapply (pixcmapIsValid_ok_N16 RT AF GP STDERR RERR MAXIDX); first [eassumption | split; assumption].
  - eapply (pixcmapIsValid_ok_P16 RT AF GP STDERR RERR MAXIDX); first [eassumption | split; assumption].
Qed.
End CV.
