(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_chain Gm_iface Gm_livekit Gm_livekit2 Fh_iface Fh_border1_defs Fh_rmb1_c0 Fh_rmb1_c16 Fh_rmb1_wrap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section RMB1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RE : returnError_cps RT e_returnErrorPtr.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis CRES : pixCopyResolution_cps RT.
Hypothesis CSPP : pixCopySpp_cps RT.
Hypothesis CCM : pixCopyColormap_cps RT.
Hypothesis ROPS : pixRasterop_src1_cps RT.

Theorem pixRemoveBorderGeneral1_ok : pixRemoveBorder1_cps RT e_pixRemoveBorderGeneral.
Proof using AF GP RE CRE CRES CSPP CCM ROPS.
  apply rmborder1_of_cases; [exact (rmborder1_c0 RT AF GP RE CRE CRES CSPP CCM ROPS)| exact (rmborder1_c16 RT AF GP RE CRE CRES CSPP CCM ROPS)].
Qed.

Theorem pixRemoveBorder1_ok : pixRemoveBorder1_cps RT e_pixRemoveBorder.
Proof using AF GP RE CRE CRES CSPP CCM ROPS.
  exact (pixRemoveBorder1_of_general RT AF GP pixRemoveBorderGeneral1_ok).
Qed.
End RMB1.
