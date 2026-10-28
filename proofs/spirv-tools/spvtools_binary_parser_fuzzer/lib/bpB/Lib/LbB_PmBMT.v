(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_Own LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_DStat LbB_DiagStmt LbB_PmBMRS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section BMDefs.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Definition mag_bytes (e : went H) (m : mem) (b0 b1 b2 b3 : byte) : Prop :=
    PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 0)) 1 = Some [b0] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 1)) 1 = Some [b1]
    /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 2)) 1 = Some [b2] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 3)) 1 = Some [b3].
  Definition bp_mag_at (e : went H) (ff fp : Z) (P : mem -> Prop) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 H e ff fp [14; 20; 21]%nat BP_MAG (bp_rmag H e ff)
      (fun w s LB LBs m c => bp_pfresh H w s LB LBs m c /\ w_words e <> 0 /\ 5 <= w_n e /\ P m) Q mo0.
  Definition BM_TAIL : Z := 0xeba90.
  Definition bm_rtail (ff : Z) (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
  Definition bm_tail_at (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 H e ff fp [14; 20; 21]%nat BM_TAIL (bm_rtail ff)
      (fun w s LB LBs m c => bp_pfresh H w s LB LBs m c /\ w_words e <> 0 /\ 5 <= w_n e) Q mo0.
  Definition BM_MID : Z := 0xebc48.
  Definition bm_mid_regs (ff : Z) (R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 1760) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
  Definition bm_mid_mem (e : went H) (ff fp : Z) (m : mem) : Prop :=
    bp_shad ff [14; 15; 20; 21]%nat m
    /\ ds_obj H ((6, ff, fp) :: w_LF e) m (wS1 e) (ff + 1760) DS_SIZE
    /\ obj_inframe ((6, ff, fp) :: w_LF e) (ff + 1760) DS_SIZE.
  Definition bm_mid_ok (len spent : Z) : Prop :=
    len + 26 <= 1024 /\ spent + ds_cost (len + 24) + ds_cost (len + 26) <= PM_RESERVE.
End BMDefs.
