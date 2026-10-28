(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_base A_exit_run2 A_code_dd000_de000 A_code_e3000_e4000 A_code_e7000_e8000 A_code_e8000_e9000            .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_exit_run3 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.stdio_globals"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.file_clean"; "stdout_dirty_hdr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.B.A_exit_run2.mem_w3a"].


(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_run3 ()) "(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+?:578.+8<.))#4.)(9.(3.(4.&8.))(:.#4.(7.&40.+????????.))))(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+?:578.+28.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.O1.))))(0.(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+?:578.+38.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.O2.))))(1.(2.(3.(4.&8.)))(5.$6.O3.(7.&40.(8.+?:578.+48.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+>66;8.)))))))")
(* [comment removed for export] *).

Lemma w3b1 : ltac2:(CDefT.buildp (gd_tbl_A_exit_run3 ()) "Pregs,(;.&5.(4.&40.))Pmem,P,(4.&40.)(2.(4.&8.))Prom,P,(4.&40.)(2.(4.&8.))Psp,(4.&40.)Pcode,(4.&40.)Pwp0,(4.&40.)Prp0,(4.&40.)Pwb,$<.Pwp,$<.P,(1.(4.&40.)(=.R9.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R6.)+10.)))P,(1.(4.&40.)(=.R:.(>.&5.+8.$?.))R6.)P,(1.(4.&40.)(=.R;.(>.&5.+1.$?.))(7.&40.+>1214.))P,(12.+100000000.(10.(11.&40.R9.)+90.))P,(12.(11.&40.R:.)+800000000000.)P,(1.$13.(14.$6.R=.(7.&40.(10.(11.&40.R;.)+90.))#90.)$15.)P,(16.R>.)P,(17.R?.+?:668.R;.R:.)P,(18.R10.R:.R9.)P,(0.(12.=R;.)(19.R;.(1:.+2.+40.)))P,(0.(12.=R;.)(19.R;.(1:.+2.+40.)))P,(1;.(1.$<.R=.R<.))(1<.(;.&5.(4.&40.))Lregs',(;.&5.(4.&40.))(0.(1=.$6.(1>.$1?.R16.(>.&40.+>6<98.$?.)R15.R14.)(1>.$1?.R1.(>.&40.+>66;8.$?.)(20.R15.R13.R12.)R14.))(0.(1.(4.&40.)(=.R1.(>.&5.+:.$?.))(7.&40.+?:578.))(0.(1.(4.&40.)(=.R1.(>.&5.+;.$?.))(7.&40.=))(0.(1.(4.&40.)(=.R1.(>.&5.+<.$?.))(7.&40.=))(0.(1.(4.&40.)(=.R1.(>.&5.+1.$?.))(7.&40.+>6=48.))(0.(1.(4.&40.)(=.R1.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R13.)+20.)))(0.(1.(4.&40.)(=.R1.(>.&5.+8.$?.))(7.&40.+?:578.))(0.(1.(4.&40.)(=.R1.(>.&5.+3.$?.))(=.R16.(>.&5.+3.$?.)))(1.(4.&40.)(=.R1.(>.&5.+4.$?.))(=.R16.(>.&5.+4.$?.))))))))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code wp0 rp0 wb wp Hsp Hs0 Hra SPlo SPhi SOK dd_H; ddestruct dd_H as (Gnl & Gofl & Gin & Gout & Gerr); intros dd_H; ddestruct dd_H as (F0l & F0wp & F0wb & F0rp & F0re); intros dd_H; ddestruct dd_H as (F1l & F1wp & F1wb & F1wr); intros WB WP NE).
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_e38e8 D_e38e8. rewrite Hsp. sp_renorm.
    stepST F_e38ec D_e38ec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x0e1214) ltac:(sok_stack SOK).
    stepST F_e38f0 D_e38f0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_e38f4 D_e38f4.
    stepn F_e3cd0 D_e3cd0. sp_renorm.
    stepST F_e3cd4 D_e3cd4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x0e6ca8) ltac:(sok_stack SOK).
    stepST F_e3cd8 D_e3cd8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_e3cdc D_e3cdc.
    stepn F_e3ce0 D_e3ce0.
    stepn F_e3ce4 D_e3ce4.
    (* [comment removed for export] *)
    stepn F_e3ce8 D_e3ce8.
    stepn F_e7ee0 D_e7ee0.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_e7ee4 | reflexivity | exact D_e7ee4 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_e7ee8 D_e7ee8 ltac:(cond_compute).
    stepret F_e80d8 D_e80d8 (0x0e709c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_e3cec D_e3cec.
    stepLD8 F_e3cf0 D_e3cf0 (Z_to_bv 64 0x0e6ca8).
    stepLD8 F_e3cf4 D_e3cf4 code.
    stepn F_e3cf8 D_e3cf8. sp_renorm.
    stepret F_e3cfc D_e3cfc (0x0e6ca8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_e38f8 D_e38f8 (Z_to_bv 64 0).
    stepb_ft F_e38fc D_e38fc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_e3900 D_e3900.
    stepLD8 F_e3904 D_e3904 (Z_to_bv 64 0x0fa668).
    stepb_ft F_e3908 D_e3908 ltac:(cond_compute).
    stepLD F_e390c D_e390c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_e3910 D_e3910 ltac:(cond_compute).
    stepLD8 F_e391c D_e391c wp0.
    stepLD8 F_e3920 D_e3920 wp0.
    stepb_tk F_e3924 D_e3924 ltac:(apply c_eq_refl).
    stepLD8 F_e393c D_e393c rp0.
    stepLD8 F_e3940 D_e3940 rp0.
    stepb_tk F_e3944 D_e3944 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_e395c D_e395c.
    stepLD8 F_e3960 D_e3960 (Z_to_bv 64 0x0fa578).
    stepb_ft F_e3964 D_e3964 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_e3968 D_e3968 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_e396c D_e396c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_e3978 D_e3978 (Z_to_bv 64 wp).
    stepLD8 F_e397c D_e397c (Z_to_bv 64 wb).
    stepb_ft F_e3980 D_e3980 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_e3984 D_e3984 (Z_to_bv 64 0x0e66b8).
    stepn F_e3988 D_e3988.
    stepn F_e398c D_e398c.
    stepn F_e3990 D_e3990.
    stepjr F_e3994 D_e3994 (Z_to_bv 64 0x0e66b8) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : ltac2:(CDefT.buildp (gd_tbl_A_exit_run3 ()) "Pregs,(;.&5.(4.&40.))Pmem,P,(4.&40.)(2.(4.&8.))Prom,P,(4.&40.)(2.(4.&8.))Psp,(4.&40.)Pcode,(4.&40.)Prp1,(4.&40.)Pwp2,(4.&40.)Prp2,(4.&40.)P,(1.(4.&40.)(=.R8.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R5.)+20.)))P,(1.(4.&40.)(=.R9.(>.&5.+8.$?.))(7.&40.+?:578.))P,(12.+100000000.(10.(11.&40.R7.)+90.))P,(12.(11.&40.R8.)+800000000000.)P,(1.(2.(3.(4.&8.)))(5.$6.R;.(7.&40.(10.(11.&40.R9.)+18.))#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+>1214.))))P,(1.(2.(3.(4.&8.)))(5.$6.R<.(7.&40.(10.(11.&40.R:.)+20.))#8.)(9.(3.(4.&8.))(:.#8.R9.)))P,(1.(2.(3.(4.&8.)))(5.$6.R=.(7.&40.(8.+?:578.+8.))#8.)(9.(3.(4.&8.))(:.#8.R9.)))P,(1.(2.(3.(4.&8.)))(5.$6.R>.(7.&40.(8.+?:578.+10.))#8.)(9.(3.(4.&8.))(:.#8.R:.)))P,(1.(2.(3.(4.&8.)))(5.$6.R?.(7.&40.+?:570.)#8.)(9.(3.(4.&8.))(:.#8.(7.&40.+?:488.))))P,(17.R10.+?:488.R;.R:.)(1<.(;.&5.(4.&40.))Lregs',(;.&5.(4.&40.))(0.(1=.$6.(1>.$1?.R13.(>.&40.+>6=48.$?.)R12.R11.)(1>.$1?.R1.(>.&40.+>0?80.$?.)R12.R11.))(0.(1.(4.&40.)(=.R1.(>.&5.+:.$?.))R?.)(0.(1.(4.&40.)(=.R1.(>.&5.+11.$?.))(7.&40.+5>.))(1.(4.&40.)(=.R1.(>.&5.+2.$?.))(7.&40.(10.(11.&40.R10.)+10.)))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr dd_H; ddestruct dd_H as (F2l & F2wp & F2wb & F2rp & F2re)).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_e3998 D_e3998 rp1.
    stepLD8 F_e399c D_e399c rp1.
    stepb_tk F_e39a0 D_e39a0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_e39b8 D_e39b8.
    stepLD8 F_e39bc D_e39bc (Z_to_bv 64 0x0fa488).
    stepb_ft F_e39c0 D_e39c0 ltac:(cond_compute).
    stepLD F_e39c4 D_e39c4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_e39c8 D_e39c8 ltac:(cond_compute).
    stepLD8 F_e39d4 D_e39d4 wp2.
    stepLD8 F_e39d8 D_e39d8 wp2.
    stepb_tk F_e39dc D_e39dc ltac:(apply c_eq_refl).
    stepLD8 F_e39f4 D_e39f4 rp2.
    stepLD8 F_e39f8 D_e39f8 rp2.
    stepb_tk F_e39fc D_e39fc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_e3a7c D_e3a7c (Z_to_bv 64 0x0e1214).
    stepLD8 F_e3a80 D_e3a80 code.
    stepn F_e3a84 D_e3a84. rewrite Hsp. sp_renorm.
    stepret F_e3a88 D_e3a88 (0x0e1214 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_dde64 D_dde64.
    stepn F_dde68 D_dde68.
    stepn F_ddbc8 D_ddbc8.
    stepn F_ddbcc D_ddbcc.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
