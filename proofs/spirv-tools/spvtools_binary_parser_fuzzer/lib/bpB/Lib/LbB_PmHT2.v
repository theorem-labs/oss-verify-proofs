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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHT1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section HT2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pm_ht2 : hdr_get_stmt -> forall (x : Z * Z * Z * Z * Z * list Z) (s : as_St H) (msF : machine_state) (mo : Model)
      (R F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AHDR_GET) fc None m (seg_rom asegs) -> rfull R ->
    getr R 1 = wz HT_RET ->
    stk asegs m lo (bv_unsigned (getr R 2)) -> aceil <= lo -> lo <= bv_unsigned (getr R 2) - HG_STACK ->
    bv_unsigned (getr R 2) mod 16 = 0 -> bv_unsigned (getr R 2) <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    hg_pre x m (bv_unsigned (getr R 2)) (getr R 10) (getr R 11) (getr R 12) (getr R 13) ->
    (forall msF1 mo1 R1 m1, as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 HT_RET) fc None m1 (seg_rom asegs) -> rfull R1 ->
       (forall r, In r HT_SAVED -> getr R1 r = getr R r) ->
       munch ((bv_unsigned (getr R 2) - HG_STACK, bv_unsigned (getr R 2)) :: hg_win x) m m1 -> wmono asegs m m1 ->
       mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned (getr R 2)) -> ACONST m1 ->
       hg_post x m (getr R1 10) (getr R1 11) m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HG x s msF mo R F fc m lo Q KR VIS RF G1 ST L1 L2 SA SH MI AC PRE K.
    rewrite (rfull_eq R RF) in VIS.
    eapply (sr_tleaf H HH AHDR_GET HG_STACK hg_pre hg_win hg_post HG x s msF mo);
      [exact KR | exact VIS | exact ST | exact L1 | exact L2 | exact SA | exact SH | exact MI | exact AC | exact PRE |].
    intros msF1 mo1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 KR1 MP1 VIS1 MU WM MI1 ST1 AC1 HQ.
    assert (ERA : ret_pc (getr R 1) = Z_to_bv 64 HT_RET) by (rewrite G1; apply bv_eq; vm_compute; reflexivity).
    rewrite ERA in VIS1.
    eapply (K msF1 mo1 _ m1 KR1 MP1 VIS1 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
      [ | exact MU | exact WM | exact MI1 | exact ST1 | exact AC1 | exact HQ ].
    intros r Hr. unfold HT_SAVED in Hr.
    repeat (destruct Hr as [<- | Hr]; [reflexivity |]). destruct Hr.
  Qed.
End HT2.
