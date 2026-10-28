(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec SeqExec StepTac ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_exit_base U_exit U_code_3b000_3c000.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exit_main () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_common"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_pre"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"].


Lemma exit_common_set_ra : ltac2:(CDefT.buildp (gd_tbl_P_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Psp,(1.&40.)Ptp,(1.&40.)Pcode,(1.&40.)Ptid,$3.Pwp2,(1.&40.)Prp2,(1.&40.)Pv,(1.&40.)P,(4.R9.R8.R7.R6.R5.R4.R3.R2.)(4.(5.R:.(6.&5.+1.$7.)R2.)R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros regs mem sp tp code tid wp2 rp2 v EC. destruct EC.
  split; try assumption; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; cbn in E; discriminate); assumption.
Qed.

Lemma exit_pre_set_ra : ltac2:(CDefT.buildp (gd_tbl_P_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$8.Pcode,(1.&40.)Ppending,(9.(1.&8.))Pv,(1.&40.)P,(:.R6.R5.R4.R3.R2.)(:.(5.R7.(6.&5.+1.$7.)R2.)R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros regs mem model code pending v dd_H; ddestruct dd_H as (sp & tp & tid & wp2 & rp2 & EC & REST)).
  dexists sp, tp, tid, wp2, rp2. split; [apply exit_common_set_ra; exact EC | exact REST].
Qed.

Lemma E_3bb50 : is_ecall W_3bb50 = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem main_ret_exit : ltac2:(CDefT.buildp (gd_tbl_P_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$8.Pcode,(1.&40.)Ppending,(9.(1.&8.))P,(:.R5.R4.R3.R2.R1.)(;.$<.(=.(>.$?.R6.(10.&40.+3?2:8.)R5.(11.$<.))R4.)(12.(13.+1.R2.)(14.(15.&40.R3.(10.&40.+??.))(16.R4.))))")
(* [comment removed for export] *).
Proof.
  intros regs mem model code pending PRE.
  dpose PRE as (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & _).
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | |].
  - replace (Z_to_bv 64 0x3f2a8) with (0x3f2a8 : word) by (apply bv_eq; reflexivity).
    exact (step_jal_link RSEGS regs (0x3f2a8 : word) mem (seg_rom RSEGS) W_3bb50 1 1188 F_3bb50 E_3bb50 D_3bb50).
  - cbn [bv_eqb]. change (btgt (0x3f2a8 : word) (bv_signed (1188 : bv 21))) with (Z_to_bv 64 0x3f74c : word).
    apply ref_exit_Z. apply exit_pre_set_ra. exact PRE.
Qed.

(* [comment removed for export] *)
Corollary main_ret_exit_code : ltac2:(CDefT.buildp (gd_tbl_P_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$8.Pz,$3.Ppending,(9.(1.&8.))P,(17.(18.=R2.)(19.R2.+100.))P,(:.R6.R5.R4.(10.&40.R3.)R2.)(;.$<.(=.(>.$?.R7.(10.&40.+3?2:8.)R6.(11.$<.))R5.)(12.(13.+1.R3.)(14.(1:.R4.)(16.R5.))))")
(* [comment removed for export] *).
Proof.
  intros regs mem model z pending Hz PRE.
  replace (exit_code z) with (bv_and (Z_to_bv 64 z) (Z_to_bv 64 255)).
  - apply main_ret_exit. exact PRE.
  - unfold exit_code. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite !Z.mod_small by lia. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
