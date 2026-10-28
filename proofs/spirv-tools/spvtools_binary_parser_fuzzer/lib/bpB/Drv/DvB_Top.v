(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BShapeAlg BShapeLaws BpinAlg Bcfg BSpec BeapCeil BFBridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 RtB_Iface RtB_TR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt BsDrvDefs BsMainPre DvB_MainA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsStartupTop BsMainState BsInstance BS_InstanceKit DvB_TopParts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_RtOwn BS_InstDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require BaseAsanA.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Section Top.

  Variable FZP : fuzz_params.
  Variable LIB : list (list Z).
  Hypothesis FZ_ALL : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_bp H -> asan_driver_laws H -> LbB_RtOwn.rt_own H -> RtB_Td.td_law H -> fuzz_stmt H FZP.
  Hypothesis PO : fz_params_ok FZP.
  Hypothesis FZINV : forall m, mem_inv asegs m -> arelro_none m -> ACONST m -> LbB_DStat.dstat m -> fz_inv FZP m.
  Hypothesis FZINV' : forall m, fz_inv FZP m -> LbB_DStat.dstat m.
  Hypothesis LIBLEN : Nat.leb (length (TR_bp LIB)) 1000 = true.
  Hypothesis PCOST : 4 * fz_cost FZP (2 ^ 26) <= 2 ^ 38.
  Hypothesis PPF : Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ [0xe8790]) LIB /\ ~ In (fst pp) (snd pp ++ [0xe8790])) (fz_pf FZP).
  Hypothesis PTR : forall H : asr, as_TR H = TR_bp LIB -> fz_tr_ok FZP H.

  Hypothesis RTOWN : forall (HC : HeapCeil) (p : BS_InstDefs.iparams), @LbB_RtOwn.rt_own HC (@BS_InstDefs.KHp HC p).

  Theorem as_realizes_spec_B_of_lib : BaseAsanA.as_realizes_spec_B.
  Proof.
    exact (as_realizes_spec_B_of_parts FZP FZ_ALL (as_instance_kit FZP LIB LIBLEN PCOST PPF PTR RTOWN)
             (fun HCEIL H HHB DL LIVE FZ => as_main_A H FZP HHB DL LIVE PO FZINV FZINV' FZ)).
  Qed.
End Top.

