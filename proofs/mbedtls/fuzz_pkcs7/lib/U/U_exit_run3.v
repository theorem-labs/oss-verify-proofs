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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_exit_run2 U_code_3c000_3d000 U_code_3e000_3f000 U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exit_run3 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.stdio_globals"; "stdout_dirty_hdr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.U.U_exit_run2.mem_w3a"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"].


(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_exit_run3 ()) "(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+4<>20.+8<.))#4.)(9.(3.(4.&8.))(:.#4.(7.&40.+????????.))))(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+4<>20.+28.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.O1.))))(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+4<>20.+38.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.O2.))))(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+4<>20.+48.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+41:34.)))))))")
(* [comment removed for export] *).

Lemma w3b1 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run3 ()) "Pregs,(;.&5.(4.&40.))Pmem,P,(4.&40.)(2.(4.&8.))Prom,P,(4.&40.)(2.(4.&8.))Psp,(4.&40.)Pcode,(4.&40.)Pwb,$<.Pwp,$<.P,(1.(4.&40.)(=.R7.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R4.)+10.)))P,(1.(4.&40.)(=.R8.(>.&5.+8.$?.))R4.)P,(1.(4.&40.)(=.R9.(>.&5.+1.$?.))(7.&40.+3?7;8.))P,(12.+100000000.(10.(11.&40.R7.)+90.))P,(12.(11.&40.R8.)+800000000000.)P,(1.$13.(14.$6.R;.(7.&40.(10.(11.&40.R9.)+90.))#90.)$15.)P,(16.R<.)P,(17.R=.R9.R8.)P,(0.(12.=R:.)(18.R:.(19.+2.+40.)))P,(0.(12.=R:.)(18.R:.(19.+2.+40.)))P,(1:.(1.$<.R<.R;.))(1;.(;.&5.(4.&40.))Lregs',(;.&5.(4.&40.))(0.(1<.$6.(1=.$1>.R13.(>.&40.+41890.$?.)R12.R11.)(1=.$1>.R1.(>.&40.+41:34.$?.)(1?.R12.R10.R?.)R11.))(0.(1.(4.&40.)(=.R1.(>.&5.+:.$?.))(7.&40.+4<>20.))(0.(1.(4.&40.)(=.R1.(>.&5.+;.$?.))(7.&40.=))(0.(1.(4.&40.)(=.R1.(>.&5.+<.$?.))(7.&40.=))(0.(1.(4.&40.)(=.R1.(>.&5.+1.$?.))(7.&40.+41940.))(0.(1.(4.&40.)(=.R1.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R10.)+20.)))(0.(1.(4.&40.)(=.R1.(>.&5.+8.$?.))(7.&40.+4<>20.))(0.(1.(4.&40.)(=.R1.(>.&5.+3.$?.))(=.R13.(>.&5.+3.$?.)))(1.(4.&40.)(=.R1.(>.&5.+4.$?.))(=.R13.(>.&5.+4.$?.))))))))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK dd_H; ddestruct dd_H as (Gnl & Gofl & Gin & Gout & Gerr); intros dd_H; ddestruct dd_H as (F1l & F1wp & F1wb & F1wr); intros WB WP NE).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
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
    stepLD8 F_3e1d4 D_3e1d4 (Z_to_bv 64 wp).
    stepLD8 F_3e1d8 D_3e1d8 (Z_to_bv 64 wb).
    stepb_ft F_3e1dc D_3e1dc ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_3e1e0 D_3e1e0 (Z_to_bv 64 0x41a34).
    stepn F_3e1e4 D_3e1e4.
    stepn F_3e1e8 D_3e1e8.
    stepn F_3e1ec D_3e1ec.
    stepjr F_3e1f0 D_3e1f0 (Z_to_bv 64 0x41a34) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run3 ()) "Pregs,(;.&5.(4.&40.))Pmem,P,(4.&40.)(2.(4.&8.))Prom,P,(4.&40.)(2.(4.&8.))Psp,(4.&40.)Pcode,(4.&40.)Prp1,(4.&40.)Pwp2,(4.&40.)Prp2,(4.&40.)P,(1.(4.&40.)(=.R8.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R5.)+20.)))P,(1.(4.&40.)(=.R9.(>.&5.+8.$?.))(7.&40.+4<>20.))P,(12.+100000000.(10.(11.&40.R7.)+90.))P,(12.(11.&40.R8.)+800000000000.)P,(1.(2.(3.(4.&8.)))(5.$6.R;.(7.&40.(10.(11.&40.R9.)+18.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+3?7;8.))))P,(1.(2.(3.(4.&8.)))(5.$6.R<.(7.&40.(10.(11.&40.R:.)+20.))#8.)(9.(3.(4.&8.))(:.#8.R9.)))P,(1.(2.(3.(4.&8.)))(5.$6.R=.(7.&40.(8.+4<>20.+8.))#8.)(9.(3.(4.&8.))(:.#8.R9.)))P,(1.(2.(3.(4.&8.)))(5.$6.R>.(7.&40.(8.+4<>20.+10.))#8.)(9.(3.(4.&8.))(:.#8.R:.)))P,(1.(2.(3.(4.&8.)))(5.$6.R?.(7.&40.+4<>18.)#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+4<=30.))))P,(20.R10.+4<=30.R;.R:.)(1;.(;.&5.(4.&40.))Lregs',(;.&5.(4.&40.))(0.(1<.$6.(1=.$1>.R13.(>.&40.+41940.$?.)R12.R11.)(1=.$1>.R1.(>.&40.+3?7<8.$?.)R12.R11.))(0.(1.(4.&40.)(=.R1.(>.&5.+:.$?.))R?.)(0.(1.(4.&40.)(=.R1.(>.&5.+11.$?.))(7.&40.+5>.))(1.(4.&40.)(=.R1.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R10.)+10.)))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr dd_H; ddestruct dd_H as (F2l & F2wp & F2wb & F2rp & F2re)).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
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
    stepn F_3e2e0 D_3e2e0. rewrite Hsp. sp_renorm.
    stepret F_3e2e4 D_3e2e4 (0x3f7b8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_3c06c D_3c06c.
    stepn F_3c070 D_3c070.
    stepn F_3c074 D_3c074.
    stepn F_3c078 D_3c078.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
