(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s1k AF_huf_w4s1x AF_huf_w4s12_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s1kb AF_huf_w4s1r.
Ltac2 kr_t_AF_huf_w4s1r2 () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4skx1;w4s_src_ctxC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01C45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4s1r5w4relC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C56Stdlib6ZArith6BinInt1Z3subK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib6ZArith6BinInt1Z3divC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01K47Corelib4Init9Datatypes6option01K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC47Corelib4Init5Peano2ltC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K47Corelib4Init9Datatypes4prod01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_rw_cells_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zur_ok_blkK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC56Stdlib6ZArith6BinInt1Z3oppI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost:kx_apart_bC5ARocqVerifyHarness?AgentSubmission6Common7KXCell2?kx_cell_store8cK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:apart_sub'C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintK47Corelib7Numbers7BinNums8positive03I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop05c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4s1r2=w4s1_r34_case".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).

Notation zlen l := (Z.of_nat (length l)).


Section CANSEC1. Context {rc : runConstT}.

Ltac kxr_ev := lazymatch goal with
  | |- _ <= bv_unsigned (ev ?E ?j) <= _ => let H := fresh "HR" in kx_range (EVar j) H; exact H
  end.

Ltac w4ge_pre tl :=
  lazymatch goal with
  | |- branch_taken _ (edenot ?E ?a) (edenot ?E ?c) = _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs);
        rewrite (ez_ok zv (kE zv xs) (kE_atoms zv xs) a), (ez_ok zv (kE zv xs) (kE_atoms zv xs) c);
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with |- context [bv_unsigned (edenot ?E' (EAlu ALU_SRL ?x ?s))] =>
          lazymatch goal with _ : 0 <= bv_unsigned (edenot E' (EAlu ALU_SRL x s)) < 2^62 |- _ => fail | _ => idtac end;
          let SB := fresh "SB" in
          assert (SB : 0 <= bv_unsigned (edenot E' (EAlu ALU_SRL x s)) < 2^62)
            by (apply w4_srl_lt62; rewrite (ez_ok zv (kE zv xs) (kE_atoms zv xs) s); cbv [ez]; change (length zv) with na;
                cbv [nth Nat.ltb Nat.leb]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
                rewrite (Z.mod_small _ (2^64)) by lia; rewrite (Z.mod_small _ 64) by lia; lia)
        end;
        kx_abstract;
        unfold branch_taken; try unfold bv_lts;
        rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2^64);
        rewrite ?Z.mod_small by lia
      end
  end.
Ltac w4ge tl :=
  w4ge_pre tl;
  repeat (match goal with |- context [(?x <? ?y)%Z] =>
            lazymatch x with context [Z.ltb _ _] => fail | _ => idtac end;
            lazymatch y with context [Z.ltb _ _] => fail | _ => idtac end;
            destruct (Z.ltb_spec x y) end; cbv beta iota);
  repeat (match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end; cbv beta iota);
  cbn [negb]; first [reflexivity | exfalso; lia].
Ltac w4fl_pre :=
  lazymatch goal with
  | |- flat ?E ?a1 ?n1 /\ flat ?E ?a2 ?n2 /\ _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs); unfold flat, elenZ;
        cbn [edenot]; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite ?(Z.mod_small 1) by lia;
        rewrite (estart_ez_kE zv xs a1) by (cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
            try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia);
        rewrite (estart_ez_kE zv xs a2) by (cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
            try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia);
        cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        try change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia
      end
  end.
Ltac w4fl := w4fl_pre; Z.div_mod_to_equations; lia.
Ltac w4m1_post :=
  kx_post_regs_keep;
  lazymatch goal with
  | OUT : u8arr bsegs ?m0 ?D (map (Z_to_bv 8) ?ob), HL : log_flat _ _, HR : 3 * ?ee + ?jj + 4 <= ?dc,
    HS : 2^20 <= ?sp <= 2^47, KK : context [munch ?W _ _] |- _ =>
      let obuf' := fresh "obuf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
      destruct (kx_u8arr_ex bsegs _ m0 _ D ob OUT HL) as (obuf' & OUT' & LB');
      repeat match goal with Dk : rw_cells bsegs m0 _ (_ :: _ :: _) |- _ =>
        lazymatch type of Dk with
        | rw_cells _ _ (sp + -376) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -144) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -184) _ => kx_cells_split Dk
        | rw_cells _ _ (sp + -224) _ => kx_cells_split Dk
        end end;
      w4_cells_post;
      let MU := fresh "MU" in let WM := fresh "WM" in
      pose proof (munch_refl W m0) as MU; pose proof (wmono_refl bsegs m0) as WM;
      kx_munch_wins MU [(D + jj, 4); (D + ee + jj, 4); (D + 2 * ee + jj, 4); (D + 3 * ee + jj, 4);
                        (sp + -368, 4); (sp + -216, 4); (sp + -176, 4); (sp + -136, 4)];
      kx_post_mem_free;
      eapply KK; [ exact MU | exact WM | eassumption | exact OUT' | rewrite LB'; lia | .. ]
  end.
Ltac r1abs :=
  repeat match goal with
  | |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?B (ELit 3)))] =>
      let Hh := fresh "Hh" in let h := fresh "h" in
      assert (Hh : bv_unsigned (edenot E (EAluw ALU_SRL B (ELit 3))) = bv_unsigned (edenot E B) / 8) by (apply r1_srlw3; w4uz);
      let b0 := eval unfold E in E in
      lazymatch b0 with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        rewrite (ez_ok zv E (kE_atoms zv xs) B) in Hh; cbv [ez] in Hh; change (length zv) with na in Hh;
        cbv [nth Nat.ltb Nat.leb] in Hh; rewrite ?Z_to_bv_unsigned in Hh; unfold bv_wrap, bv_modulus in Hh;
        try change (2 ^ Z.of_N 64) with (2^64) in Hh; rewrite ?(Z.mod_small _ (2^64)) in Hh by lia
      end;
      set (h := bv_unsigned (edenot E (EAluw ALU_SRL B (ELit 3)))) in *; clearbody h;
      let Hb := fresh "Hb" in assert (Hb : 0 <= h <= 14 /\ 8 * h <= h * 8) by (rewrite Hh; split; [split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia] | lia])
  end.
Ltac r1uz :=
  r1abs; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
  rewrite ?Z.mod_small by lia; first [lia | Z.div_mod_to_equations; lia].
Ltac r1rel :=
  rewrite ?r1_and7; r1abs; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
  rewrite ?Z.mod_small by lia; first [lia | Z.div_mod_to_equations; lia].
Ltac r1meq :=
  f_equal;
  try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal end);
  lazymatch goal with
  | |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => first [ reflexivity | f_equal; lia ]
  | |- Z_to_bv 64 ?a = ?w => apply Z_to_bv_bv_unsigned
  | |- _ => reflexivity
  end.
Ltac r1appK KN KS O2 ob :=
  first [ eapply r1_evtF_eq; [eapply (KN O2 _ ob) | r1meq] | eapply r1_evtF_eq; [eapply (KS O2 _ ob) | r1meq] ].
Ltac w4s_src_ctx_post mm0 :=
  unfold w4s_src_ctx;
  lazymatch goal with
  | |- mem_inv _ ?M /\ _ =>
      match goal with SB : bytes_at _ M _ ?sb, SL : Z.of_nat (length ?sb) = _ |- _ =>
        refine (conj _ (conj (ex_intro _ sb (conj SB SL)) _)); [ eassumption | ];
        split; [ eapply (unpoisoned_munch _ mm0 M); [ eassumption | eassumption |
                   cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia ]
               | repeat split; assumption ]
      end
  end.
Ltac r1ap := w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; unfold KXGoM.apart in *; lia.
Ltac r1shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      first [ apply (w4_shd_ap E X B O k) | apply (w4_shd4 E X B O k) | apply (w4_shd8 E X B O k) ];
      [ w4xbw | lia | lia | w4uz | w4uz | r1ap ]
  end.
Ltac r1acc := idtac.

Lemma w4s1_R3n_s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  o4 < 8 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  8 <= o3 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567196) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP HO2 HS2 HP2 KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o3 -> o3 + 8 <= L3 /\ 0 <= b3 <= 56) /\ (o3 < 8 -> 0 <= b3 <= 112)) by lia.
  kx_runFLd [567400; 567700] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -184) 40;
       KZRange c3 0 (2^64 - 1); KZRange S3 4096 (2^47); KZRange (S3 + o3) 4096 (2^47);
       KZWord (SP + -184) 8 c3; KZWord (SP + -168) 8 (S3 + o3); KZWord (SP + -160) 8 S3; KZWord (SP + -152) 8 (S3 + 8);
       KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47); KZWord (SP + -192) 8 (S4 + 8);
       KZRange o3 8 (2^47); KZRange L3 16 (2^47); KZRange (L3 - o3) 8 (2^47); KZRange b3 0 56;
       KZDisj S3 L3 (SP + -480) 480; KZDisj DST dcap S3 L3;
       KZRange o4 0 7]
      [(S3, L3)] [(SP + -480, 480); (DST, dcap); (S3, L3)] [(S3, L3); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 24); (SP + -440, 8)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R3n_n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  8 <= o4 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  8 <= o3 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567196) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP HO2 HS2 HP2 KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o3 -> o3 + 8 <= L3 /\ 0 <= b3 <= 56) /\ (o3 < 8 -> 0 <= b3 <= 112)) by lia.
  kx_runFLd [567400; 567700] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -184) 40;
       KZRange c3 0 (2^64 - 1); KZRange S3 4096 (2^47); KZRange (S3 + o3) 4096 (2^47);
       KZWord (SP + -184) 8 c3; KZWord (SP + -168) 8 (S3 + o3); KZWord (SP + -160) 8 S3; KZWord (SP + -152) 8 (S3 + 8);
       KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47); KZWord (SP + -192) 8 (S4 + 8);
       KZRange o3 8 (2^47); KZRange L3 16 (2^47); KZRange (L3 - o3) 8 (2^47); KZRange b3 0 56;
       KZDisj S3 L3 (SP + -480) 480; KZDisj DST dcap S3 L3;
       KZRange o4 8 (2^47)]
      [(S3, L3)] [(SP + -480, 480); (DST, dcap); (S3, L3)] [(S3, L3); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 24); (SP + -440, 8)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R3n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  8 <= o3 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567196) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3.
  destruct (Z.lt_ge_cases o4 8) as [ON|ON].
  - exact (w4s1_R3n_s Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 ON).
  - exact (w4s1_R3n_n Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 ON).
Qed.

Lemma w4s1_R3s_s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  o4 < 8 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  o3 < 8 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567684) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP HO2 HS2 HP2 KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o3 -> o3 + 8 <= L3 /\ 0 <= b3 <= 56) /\ (o3 < 8 -> 0 <= b3 <= 112)) by lia.
  kx_runFLd [567400; 567700] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -184) 40;
       KZRange c3 0 (2^64 - 1); KZRange S3 4096 (2^47); KZRange (S3 + o3) 4096 (2^47);
       KZWord (SP + -184) 8 c3; KZWord (SP + -168) 8 (S3 + o3); KZWord (SP + -160) 8 S3; KZWord (SP + -152) 8 (S3 + 8);
       KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47); KZWord (SP + -192) 8 (S4 + 8);
       KZRange o3 0 7; KZRange b3 0 112;
       KZRange o4 0 7]
      (@nil (Z * Z)) [(SP + -480, 480); (DST, dcap)] [(DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 24); (SP + -440, 8)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R3s_n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  8 <= o4 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  o3 < 8 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567684) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP HO2 HS2 HP2 KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o3 -> o3 + 8 <= L3 /\ 0 <= b3 <= 56) /\ (o3 < 8 -> 0 <= b3 <= 112)) by lia.
  kx_runFLd [567400; 567700] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -184) 40;
       KZRange c3 0 (2^64 - 1); KZRange S3 4096 (2^47); KZRange (S3 + o3) 4096 (2^47);
       KZWord (SP + -184) 8 c3; KZWord (SP + -168) 8 (S3 + o3); KZWord (SP + -160) 8 S3; KZWord (SP + -152) 8 (S3 + 8);
       KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47); KZWord (SP + -192) 8 (S4 + 8);
       KZRange o3 0 7; KZRange b3 0 112;
       KZRange o4 8 (2^47)]
      (@nil (Z * Z)) [(SP + -480, 480); (DST, dcap)] [(DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -184 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -184) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -184, 24); (SP + -440, 8)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R3s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o3 ->
  o3 < 8 ->
  (o3 = 0 /\ 0 <= b3 <= 112) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 56) ->
  SS <= S3 ->
  S3 + L3 <= SS + n ->
  0 <= c3 < 2^64 ->
  4096 <= S3 + o3 <= 2^47 ->
  0 <= o4 ->
  SS <= S4 ->
  4096 <= S4 + o4 <= 2^47 ->
  (8 <= o4 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567400) fc None mm' (seg_rom bsegs))) ->
  (o4 < 8 -> forall (mm' : amem) (obuf' : list Z) (c3' b3' o3' st : Z) (x8 x18 x19 x21 x22 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o3 < 8 /\ o3' = o3 /\ b3' = b3 /\ c3' = c3 /\ st = 3) \/ (8 <= o3 /\ o3' = o3 - b3 / 8 /\ b3' = b3 mod 8 /\ st = 0) ->
     0 <= c3' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3')) r7 x8 r9 r10 r11 r12 r13 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (3)) r17 x18 x19 r20 x21 x22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 (Z_to_bv 64 (st)))
       F (Z_to_bv 64 567700) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 (Z_to_bv 64 (b3)) r7 r8 r9 r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 (Z_to_bv 64 (S3 + o3)) r20 r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 r27 r28 r29 r30 r31)
    F (Z_to_bv 64 567684) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3.
  destruct (Z.lt_ge_cases o4 8) as [ON|ON].
  - exact (w4s1_R3s_s Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 ON).
  - exact (w4s1_R3s_n Q RNG mm F fc gp tp r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r17 r18 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 f0 f1 f2 f3 f4 f8 f9 f10 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L3 ON).
Qed.

Lemma w4s1_R4n_s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  dcap < 3 * e1 + j + 8 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  8 <= o4 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567400) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31
    f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o4 -> o4 + 8 <= L4 /\ 0 <= b4 <= 56) /\ (o4 < 8 -> 0 <= b4 <= 112)) by lia.
  kx_runFLd [567616; 568408] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -224) 40;
       KZRange c4 0 (2^64 - 1); KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZWord (SP + -224) 8 c4; KZWord (SP + -208) 8 (S4 + o4); KZWord (SP + -200) 8 S4; KZWord (SP + -192) 8 (S4 + 8);
       KZRange c4 0 (2^64 - 1); KZRange (DST + 3 * e1 + j) 4096 (2^47); KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -400) 8 DST;
       KZRange o4 8 (2^47); KZRange L4 16 (2^47); KZRange (L4 - o4) 8 (2^47); KZRange b4 0 56;
       KZDisj S4 L4 (SP + -480) 480; KZDisj DST dcap S4 L4;
       KZRange (dcap - 3 * e1 - j) 4 7]
      [(S4, L4)] [(SP + -480, 480); (DST, dcap); (S4, L4)] [(S4, L4); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -224, 24)] end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _) _ _ _ _ _ _) => first [rewrite <- (Z_to_bv_bv_unsigned _ w) | rewrite <- (Z_to_bv_bv_unsigned w)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R4n_n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  3 * e1 + j + 8 <= dcap ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  8 <= o4 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567400) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31
    f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o4 -> o4 + 8 <= L4 /\ 0 <= b4 <= 56) /\ (o4 < 8 -> 0 <= b4 <= 112)) by lia.
  kx_runFLd [567616; 568408] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -224) 40;
       KZRange c4 0 (2^64 - 1); KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZWord (SP + -224) 8 c4; KZWord (SP + -208) 8 (S4 + o4); KZWord (SP + -200) 8 S4; KZWord (SP + -192) 8 (S4 + 8);
       KZRange c4 0 (2^64 - 1); KZRange (DST + 3 * e1 + j) 4096 (2^47); KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -400) 8 DST;
       KZRange o4 8 (2^47); KZRange L4 16 (2^47); KZRange (L4 - o4) 8 (2^47); KZRange b4 0 56;
       KZDisj S4 L4 (SP + -480) 480; KZDisj DST dcap S4 L4;
       KZRange (dcap - 3 * e1 - j) 8 (2^32)]
      [(S4, L4)] [(SP + -480, 480); (DST, dcap); (S4, L4)] [(S4, L4); (DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -224, 24)] end).
  all: try (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _) _ _ _ _ _ _) => first [rewrite <- (Z_to_bv_bv_unsigned _ w) | rewrite <- (Z_to_bv_bv_unsigned w)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R4n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  8 <= o4 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567400) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4.
  destruct (Z.lt_ge_cases dcap (3 * e1 + j + 8)) as [ON|ON].
  - exact (w4s1_R4n_s Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 ON).
  - exact (w4s1_R4n_n Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 ON).
Qed.

Lemma w4s1_R4s_s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  dcap < 3 * e1 + j + 8 ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  o4 < 8 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567700) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31
    f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o4 -> o4 + 8 <= L4 /\ 0 <= b4 <= 56) /\ (o4 < 8 -> 0 <= b4 <= 112)) by lia.
  kx_runFLd [567616; 568408] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -224) 40;
       KZRange c4 0 (2^64 - 1); KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZWord (SP + -224) 8 c4; KZWord (SP + -208) 8 (S4 + o4); KZWord (SP + -200) 8 S4; KZWord (SP + -192) 8 (S4 + 8);
       KZRange c4 0 (2^64 - 1); KZRange (DST + 3 * e1 + j) 4096 (2^47); KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -400) 8 DST;
       KZRange o4 0 7; KZRange b4 0 112;
       KZRange (dcap - 3 * e1 - j) 4 7]
      (@nil (Z * Z)) [(SP + -480, 480); (DST, dcap)] [(DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -224, 24)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R4s_n : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  3 * e1 + j + 8 <= dcap ->
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  o4 < 8 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567700) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31
    f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf
    SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4
    ON C SC AP AD OUT LO FR D1 D2 D3 D4 HJ HE HQ1 HDC HSP HO HK G HS HL HC HP KN KS.
  w4s1_dctx_intro C. w4s_src_intro SC.
  assert (HLq : (8 <= o4 -> o4 + 8 <= L4 /\ 0 <= b4 <= 56) /\ (o4 < 8 -> 0 <= b4 <= 112)) by lia.
  kx_runFLd [567616; 568408] 200%nat (repeat true 64)
      [KZRange DST 4096 (2^47); KZRange dcap 4 (2^32); KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange SP (0x10007fff8000 + 480) (2^47);
       KZDisj DST dcap 0x7fff8000 17592186044416; KZDisj DST dcap (SP + -480) 480; KZWr DST dcap;
       KZWr (SP + -480) 104; KZWr (SP + -224) 40;
       KZRange c4 0 (2^64 - 1); KZRange S4 4096 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZWord (SP + -224) 8 c4; KZWord (SP + -208) 8 (S4 + o4); KZWord (SP + -200) 8 S4; KZWord (SP + -192) 8 (S4 + 8);
       KZRange c4 0 (2^64 - 1); KZRange (DST + 3 * e1 + j) 4096 (2^47); KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -400) 8 DST;
       KZRange o4 0 7; KZRange b4 0 112;
       KZRange (dcap - 3 * e1 - j) 8 (2^32)]
      (@nil (Z * Z)) [(SP + -480, 480); (DST, dcap)] [(DST, dcap)].
  all: try w4br.
  all: try w4word4.
  all: try (lazymatch goal with |- flat _ _ _ /\ flat _ _ _ /\ _ => r1shd end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      repeat match goal with H : bytes_at _ _ _ _ |- _ => kx_frame H | H : u8arr _ _ _ _ |- _ => fail
        | H : rw_cells _ _ ?A _ |- _ => lazymatch A with _ + -224 => fail | _ + -480 => fail | _ => kx_frame H end end end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -224) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with HD : rw_cells _ _ (_ + -480) _ |- evtF _ _ _ _ => kx_cells_split HD end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_cells_post end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_mem_free end).
  all: try (lazymatch goal with KXLF : log_flat ?E ?log, HU : u8arr bsegs ?m ?A (map (Z_to_bv 8) ?ob) |- evtF _ _ _ _ =>
      destruct (kx_u8arr_ex bsegs E m log A ob HU KXLF) as (obuf2 & OUT2 & LB2); clear HU end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm) as MUW;
      kx_munch_wins MUW [(SP + -224, 24)] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => r1appK KN KS ON obuf2 end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; kx_cells_merge end).
  all: try (lazymatch goal with |- wmono _ _ _ => apply kx_wmono_log, wmono_refl end).
  all: try (lazymatch goal with |- w4s_src_ctx _ _ _ _ _ _ => unfold w4s_src_ctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- w4s1_dctx _ _ _ _ _ _ _ _ _ => unfold w4s1_dctx; repeat match goal with |- _ /\ _ => split end end).
  all: try (lazymatch goal with |- exists sb, bytes_at _ _ _ sb /\ _ => eexists; split; eassumption end).
  all: try (lazymatch goal with MW : munch ?W ?m0 ?M |- unpoisoned ?M _ _ => eapply (unpoisoned_munch W m0 M); [eassumption | exact MW |
      cbn [disjoint_from]; unfold shad, ASHOFF in *; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- Z.of_nat (length _) = _ => rewrite LB2; assumption end).
  all: try (lazymatch goal with |- 0 <= bv_unsigned ?w < 2^64 => apply bv_unsigned_in_range end).
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ (8 <= _ /\ _) => rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
      rewrite ?Z.mod_small by lia; first [left; split; [assumption | repeat split; first [reflexivity | lia]] | right; split; [assumption | repeat split; first [reflexivity | lia | r1rel]]] end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try eassumption.
  all: try lia.
Time Qed.

Lemma w4s1_R4s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 : word)
    (f0 f1 f2 f4 f8 f9 f11 f12 : word) (pad1 pad2 pad3 pad4 : list byte) (obuf : list Z)
    (SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl ->
  w4s_src_ctx RNG mm SS n SBL SBH ->
  KXGoM.apart SS n (SP + -480) 480 ->
  KXGoM.apart SS n DST dcap ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) ->
  Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
     C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  0 <= j ->
  0 <= e1 ->
  3 * e1 + j + 4 <= dcap ->
  dcap <= 2^32 ->
  2^20 <= SP <= 2^47 ->
  0 <= o4 ->
  o4 < 8 ->
  (o4 = 0 /\ 0 <= b4 <= 112) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 56) ->
  SS <= S4 ->
  S4 + L4 <= SS + n ->
  0 <= c4 < 2^64 ->
  4096 <= S4 + o4 <= 2^47 ->
  (3 * e1 + j + 8 <= dcap -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 567616) fc None mm' (seg_rom bsegs))) ->
  (dcap < 3 * e1 + j + 8 -> forall (mm' : amem) (obuf' : list Z) (c4' b4' o4' st : Z) (x8 x9 x18 x19 x22 x23 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     w4s1_dctx RNG mm' (SP + -480) (DT + 4) DBL DBH DST dcap tl -> w4s_src_ctx RNG mm' SS n SBL SBH ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
    rw_cells bsegs mm' (SP + -480) [C8 f0; C8 f1; C8 f2; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 f4; C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2);
       C8 (Z_to_bv 64 c1); C8 f8; C8 f9; C8 (Z_to_bv 64 DST); C8 f11; C8 f12] ->
    rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
    rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
    rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
    rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o4 < 8 /\ o4' = o4 /\ b4' = b4 /\ c4' = c4 /\ st = 3) \/ (8 <= o4 /\ o4' = o4 - b4 / 8 /\ b4' = b4 mod 8 /\ st = 0) ->
     0 <= c4' < 2^64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4')) x8 x9 r10 r11 r12 r13 r14 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (st)) r17 x18 x19 (Z_to_bv 64 (j + 4)) (Z_to_bv 64 (DST)) x22 x23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4')) r28 r29 r30 r31)
       F (Z_to_bv 64 568408) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp r5 r6 (Z_to_bv 64 (b4)) r8 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) r10 r11 r12 r13 r14 r15 (Z_to_bv 64 (3)) r17 r18 r19 (Z_to_bv 64 (j)) r21 r22 r23 (Z_to_bv 64 0x7fff8000) r25 r26 (Z_to_bv 64 (c4)) r28 r29 r30 r31)
    F (Z_to_bv 64 567700) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4.
  destruct (Z.lt_ge_cases dcap (3 * e1 + j + 8)) as [ON|ON].
  - exact (w4s1_R4s_s Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 ON).
  - exact (w4s1_R4s_n Q RNG mm F fc gp tp r5 r6 r8 r10 r11 r12 r13 r14 r15 r17 r18 r19 r21 r22 r23 r25 r26 r28 r29 r30 r31 f0 f1 f2 f4 f8 f9 f11 f12 pad1 pad2 pad3 pad4 obuf SP DST dcap DT tl DBL DBH j e1 SS n SBL SBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 L4 ON).
Qed.

Ltac r2meq :=
  f_equal;
  try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal end);
  lazymatch goal with
  | |- Z_to_bv 64 ?a = Z_to_bv 64 ?b =>
      first [ reflexivity
            | f_equal; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; try change (2 ^ Z.of_N 64) with (2^64);
              rewrite ?Z.mod_small by lia; lia ]
  | |- Z_to_bv 64 ?a = ?w => apply Z_to_bv_bv_unsigned
  | |- _ => reflexivity
  end.

Definition w4s_rl5 (o o' b b' c c' st : Z) : Prop :=
  (o < 8 /\ o' = o /\ b' = b /\ c' = c /\ st = 3) \/ (8 <= o /\ o' = o - b / 8 /\ b' = b mod 8 /\ st = 0).

Lemma w4s_rl5_st : forall o o' b b' c c' st, w4s_rl5 o o' b b' c c' st -> st = 0 \/ st = 3.
Proof. unfold w4s_rl5. intros. lia. Qed.

Lemma w4s_rl5_b : forall o o' b b' c c' st, w4s_rl5 o o' b b' c c' st -> 0 <= st <= 3.
Proof. unfold w4s_rl5. intros. lia. Qed.

Lemma w4s_rl5_0 : forall o o' b b' c c' st, w4s_rl5 o o' b b' c c' st -> st = 0 ->
  8 <= o /\ o' = o - b / 8 /\ b' = b mod 8.
Proof. unfold w4s_rl5. intros. lia. Qed.

Lemma w4s_rl5_f : forall o o' b b' c c' st, w4s_rl5 o o' b b' c c' st ->
  (o < 8 /\ o' = o /\ b' = b) \/ (8 <= o /\ o' = o - b / 8 /\ b' = b mod 8).
Proof. unfold w4s_rl5. intros. lia. Qed.

Theorem w4s1_rall : w4s1_rall_case.
Proof.
  unfold w4s1_rall_case.
  intros Q RNG mm F fc gp tp y12 y13 y14 y15 y16 y21 y23 w0 pad1 pad2 pad3 pad4 obuf
    SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 SS n SBL SBH L1 L2 L3 L4
    C MI SC AP AD OUT LO FR B1 B2 B3 B4 HTL HRS HJ HE HROOM HDC HO1 HO2 HO3 HO4 G1 G2 G3 G4
    HS1 HL1 HS2 HL2 HS3 HL3 HS4 HL4 HC1 HC2 HC3 HC4 HP1 HP2 HP3 HP4 HDT HSP KL KF.
  pose proof C as C0. w4s1_dctx_intro C0.
  eapply w4s1_R1; try eassumption; try lia.
  all: intros ON1 mm1 ob1 c1' b1' o1' st1 ? ? ? ? ? MU1 WM1 MI1 DC1 SC1 OU1 LO1 FR1 E11 E12 E13 E14 RL1 HC1'.
  all: change (w4s_rl5 o1 o1' b1 b1' c1 c1' st1) in RL1; clear G1.
  all: first [eapply w4s1_R2n with (j := j) (e1 := e1) | eapply w4s1_R2s with (j := j) (e1 := e1)]; try eassumption; try lia.
  all: intros ON2 mm2 ob2 c2' b2' o2' st2 ? ? ? ? MU2 WM2 MI2 DC2 SC2 OU2 LO2 FR2 E21 E22 E23 E24 RL2 HC2'.
  all: change (w4s_rl5 o2 o2' b2 b2' c2 c2' st2) in RL2; clear G2.
  all: first [eapply w4s1_R3n with (j := j) (e1 := e1) | eapply w4s1_R3s with (j := j) (e1 := e1)]; try eassumption; try lia.
  all: intros ON3 mm3 ob3 c3' b3' o3' st3 ? ? ? ? ? MU3 WM3 MI3 DC3 SC3 OU3 LO3 FR3 E31 E32 E33 E34 RL3 HC3'.
  all: change (w4s_rl5 o3 o3' b3 b3' c3 c3' st3) in RL3; clear G3.
  all: first [eapply w4s1_R4n | eapply w4s1_R4s]; try eassumption; try lia.
  all: intros ON4 mm4 ob4 c4' b4' o4' st4 ? ? ? ? ? ? MU4 WM4 MI4 DC4 SC4 OU4 LO4 FR4 E41 E42 E43 E44 RL4 HC4'.
  all: change (w4s_rl5 o4 o4' b4 b4' c4 c4' st4) in RL4; clear G4.
  all: assert (MUa : munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm4)
         by (eapply munch_trans; [eapply munch_trans; [eapply munch_trans; [exact MU1 | exact MU2] | exact MU3] | exact MU4]).
  all: assert (WMa : wmono bsegs mm mm4)
         by (eapply wmono_trans; [eapply wmono_trans; [eapply wmono_trans; [exact WM1 | exact WM2] | exact WM3] | exact WM4]).
  all: pose proof (w4s_rl5_b _ _ _ _ _ _ _ RL1) as SB1; pose proof (w4s_rl5_b _ _ _ _ _ _ _ RL2) as SB2;
       pose proof (w4s_rl5_b _ _ _ _ _ _ _ RL3) as SB3; pose proof (w4s_rl5_b _ _ _ _ _ _ _ RL4) as SB4.
  all: try (eapply w4s_end3; [intros HLOR | intros HLOR]).
  all: try (lazymatch goal with HLOR : Z.lor _ _ = 0 |- _ =>
      rewrite !Z_to_bv_unsigned in HLOR; unfold bv_wrap, bv_modulus in HLOR; try change (2 ^ Z.of_N 64) with (2^64) in HLOR;
      rewrite !(Z.mod_small _ (2^64)) in HLOR by lia;
      destruct (w4s_st_zero st1 st2 st3 st4 (w4s_rl5_st _ _ _ _ _ _ _ RL1) (w4s_rl5_st _ _ _ _ _ _ _ RL2)
                  (w4s_rl5_st _ _ _ _ _ _ _ RL3) (w4s_rl5_st _ _ _ _ _ _ _ RL4) HLOR) as (Z1 & Z2 & Z3 & Z4);
      destruct (w4s_rl5_0 _ _ _ _ _ _ _ RL1 Z1) as (A1 & A1o & A1b);
      destruct (w4s_rl5_0 _ _ _ _ _ _ _ RL2 Z2) as (A2 & A2o & A2b);
      destruct (w4s_rl5_0 _ _ _ _ _ _ _ RL3 Z3) as (A3 & A3o & A3b);
      destruct (w4s_rl5_0 _ _ _ _ _ _ _ RL4 Z4) as (A4 & A4o & A4b);
      eapply KL; try eassumption; try lia end).
  all: try (eapply w4s_exit; [eassumption | eassumption | eapply rng_sub'; [exact WF | lia] | lia | lia | ]).
  all: try (eapply r1_evtF_eq; [eapply KF | r2meq]).
  all: try eassumption.
  all: try (lazymatch goal with |- (_ < 8 /\ _) \/ _ =>
      first [ exact (w4s_rl5_f _ _ _ _ _ _ _ RL1) | exact (w4s_rl5_f _ _ _ _ _ _ _ RL2)
            | exact (w4s_rl5_f _ _ _ _ _ _ _ RL3) | exact (w4s_rl5_f _ _ _ _ _ _ _ RL4) ] end).
Time Qed.

End CANSEC1.
