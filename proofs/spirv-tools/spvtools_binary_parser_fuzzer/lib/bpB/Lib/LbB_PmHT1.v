(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BsCXXHeap RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_SR LbB_TablStmt LbB_HdrGet LbB_PmHTK LbB_PmHTS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition HT_START : Z := 0xebdc4.
Definition HT_RET : Z := 0xebde8.
Definition HT_D4 : Z := 0xebdec.
Definition HT_LOOP : Z := 0xec0b4.
Definition HT_WIN (sf : Z) : list (Z * Z) := [(sf + 278, sf + 282)].
Definition HT_SAVED : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section HT1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pm_ht1 : forall (s : as_St H) (msF : machine_state) (mo : Model) (R F : bvmap 5 word) (fc : bv 32) (m : mem)
      (p sf fb b e h : Z) (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 HT_START) fc None m (seg_rom asegs) -> rfull R ->
    mem_inv asegs m -> ht_a_pre R m p sf fb b e h ->
    (forall msF1 mo1 R1 M1, as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AHDR_GET) fc None M1 (seg_rom asegs) -> rfull R1 -> mem_inv asegs M1 ->
       munch (HT_WIN sf) m M1 -> wmono asegs m M1 ->
       fldA M1 (sf + 278) 1 0 -> fldA M1 (sf + 279) 1 0 -> fldA M1 (sf + 280) 1 0 -> fldA M1 (sf + 281) 1 0 ->
       getr R1 1 = wz HT_RET -> getr R1 9 = wz fb -> getr R1 10 = wz b -> getr R1 11 = wz e -> getr R1 12 = wz h ->
       getr R1 18 = wz p -> getr R1 19 = wz sf -> getr R1 25 = wz b ->
       (forall r, In r [2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv -> getr R1 r = getr R r) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s msF mo R F fc m p sf fb b e h Q KR VIS RF MI P K.
    destruct (ht_a_bp R F fc m p sf fb b e h P)
      as (R1 & M1 & Hms & MU & WM & F3 & F2 & F1 & F0 & G1 & G9 & G10 & G11 & G12 & G18 & G19 & G25 & KP).
    change (wz (0xea7c4 + 5632)) with (Z_to_bv 64 HT_START) in Hms.
    change (wz 959156) with (Z_to_bv 64 AHDR_GET) in Hms.
    pose proof (msteps_mem_inv asegs _ _ Hms MI) as MI1. cbn [ms_mem] in MI1.
    eapply (sr_msteps H HH s msF mo R F _ fc m R1 _ M1 Q KR VIS RF Hms).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    exact (K msF1 mo1 R1 M1 KR1 MP1 VIS1 RF1 MI1 MU WM F0 F1 F2 F3 G1 G9 G10 G11 G12 G18 G19 G25 KP).
  Qed.
End HT1.
