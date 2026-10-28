(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_code_3c000_3d000 U_code_3e000_3f000 U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exit_run2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.stdio_globals"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "mem_w3a"].


Definition mem_w3a (mem : word -> option byte) (sp code : word) := ltac2:(CDefT.buildp (gd_tbl_P_exit_run2 ()) "(0.(0.(0.(0.O3.(1.&40.(2.(3.&40.O2.)+18.))(4.#8.(1.&40.+3?7;8.)))(1.&40.(2.(3.&40.O2.)+20.))(4.#8.O1.))(1.&40.(2.(3.&40.O2.)+28.))(4.#8.(1.&40.+418:0.)))(1.&40.(2.(3.&40.O2.)+30.))(4.#8.O1.))")
(* [comment removed for export] *).

Lemma w3a : ltac2:(CDefT.buildp (gd_tbl_P_exit_run2 ()) "Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pcode,(6.&40.)Pwp1,(6.&40.)Prp1,(6.&40.)Pwp2,(6.&40.)Prp2,(6.&40.)P,(8.(6.&40.)(9.R9.(:.&5.+2.$;.))(1.&40.(2.(3.&40.R6.)+10.)))P,(8.(6.&40.)(9.R:.(:.&5.+8.$;.))R6.)P,(8.(6.&40.)(9.R;.(:.&5.+1.$;.))(1.&40.+3?7;8.))P,(<.+100000000.(2.(3.&40.R9.)+90.))P,(<.(3.&40.R:.)+800000000000.)P,(8.$=.(>.$?.R=.(1.&40.(2.(3.&40.R;.)+90.))#90.)$10.)P,(11.R>.)P,(12.R?.+4<>20.R;.R:.)P,(12.R10.+4<=30.R:.R9.)(13.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(14.(15.$?.(16.$17.R13.(:.&40.+41890.$;.)R12.R11.)(16.$17.R1.(:.&40.+3?7<8.$;.)(18.R12.R10.R?.)R11.))(14.(8.(6.&40.)(9.R1.(:.&5.+:.$;.))R?.)(14.(8.(6.&40.)(9.R1.(:.&5.+11.$;.))(1.&40.+5>.))(8.(6.&40.)(9.R1.(:.&5.+2.$;.))(1.&40.(2.(3.&40.R10.)+10.)))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK dd_H; ddestruct dd_H as (Gnl & Gofl & Gin & Gout & Gerr); intros dd_H; ddestruct dd_H as (F1l & F1wp & F1wb & F1rp & F1re); intros dd_H; ddestruct dd_H as (F2l & F2wp & F2wb & F2rp & F2re)).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_3e144 D_3e144. rewrite Hsp. sp_renorm.
    stepST F_3e148 D_3e148 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x3f7b8) ltac:(sok_stack SOK).
    stepST F_3e14c D_3e14c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_3e150 D_3e150.
    stepn F_3e758 D_3e758. sp_renorm.
    stepST F_3e75c D_3e75c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x418a0) ltac:(sok_stack SOK).
    stepST F_3e760 D_3e760 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_3e764 D_3e764.
    stepn F_3e768 D_3e768.
    stepn F_3e76c D_3e76c.
    (* [comment removed for export] *)
    stepn F_3e770 D_3e770.
    stepn F_43834 D_43834.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_43838 | reflexivity | exact D_43838 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_4383c D_4383c ltac:(cond_compute).
    stepret F_43a2c D_43a2c (0x41ec0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_3e774 D_3e774.
    stepLD8 F_3e778 D_3e778 (Z_to_bv 64 0x418a0).
    stepLD8 F_3e77c D_3e77c code.
    stepn F_3e780 D_3e780. sp_renorm.
    stepret F_3e784 D_3e784 (0x418a0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_3e154 D_3e154 (Z_to_bv 64 0).
    stepb_ft F_3e158 D_3e158 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_3e15c D_3e15c.
    stepLD8 F_3e160 D_3e160 (Z_to_bv 64 0).
    stepb_tk F_3e164 D_3e164 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_3e1b8 D_3e1b8.
    stepLD8 F_3e1bc D_3e1bc (Z_to_bv 64 0x4ce20).
    stepb_ft F_3e1c0 D_3e1c0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_3e1c4 D_3e1c4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_3e1c8 D_3e1c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_3e1d4 D_3e1d4 wp1.
    stepLD8 F_3e1d8 D_3e1d8 wp1.
    stepb_tk F_3e1dc D_3e1dc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_3e1f4 D_3e1f4 rp1.
    stepLD8 F_3e1f8 D_3e1f8 rp1.
    stepb_tk F_3e1fc D_3e1fc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_3e214 D_3e214.
    stepLD8 F_3e218 D_3e218 (Z_to_bv 64 0x4cd30).
    stepb_ft F_3e21c D_3e21c ltac:(cond_compute).
    stepLD F_3e220 D_3e220 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_3e224 D_3e224 ltac:(cond_compute).
    stepLD8 F_3e230 D_3e230 wp2.
    stepLD8 F_3e234 D_3e234 wp2.
    stepb_tk F_3e238 D_3e238 ltac:(apply c_eq_refl).
    stepLD8 F_3e250 D_3e250 rp2.
    stepLD8 F_3e254 D_3e254 rp2.
    stepb_tk F_3e258 D_3e258 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_3e2d8 D_3e2d8 (Z_to_bv 64 0x3f7b8).
    stepLD8 F_3e2dc D_3e2dc code.
    stepn F_3e2e0 D_3e2e0. sp_renorm.
    stepret F_3e2e4 D_3e2e4 (0x3f7b8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_3c06c D_3c06c.
    stepn F_3c070 D_3c070.
    stepn F_3c074 D_3c074.
    stepn F_3c078 D_3c078.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
