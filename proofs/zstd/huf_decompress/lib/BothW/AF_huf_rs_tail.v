(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_st RF_huf_rs_pure
  RF_huf_rs_dl RF_huf_rs_cl RF_huf_rs_fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in let v10 := reg_val 10%Z in let v14 := reg_val 14%Z in let v15 := reg_val 15%Z in
    let v16 := reg_val 16%Z in let v8 := reg_val 8%Z in let v9 := reg_val 9%Z in let v18 := reg_val 18%Z in
    let v19 := reg_val 19%Z in let v20 := reg_val 20%Z in let v24 := reg_val 24%Z in let v25 := reg_val 25%Z in
    idtac "ra=" v1 " t0=" v5 " t1=" v6 " t2=" v7 " s0=" v8 " s1=" v9;
    idtac " a0=" v10 " a1=" v11 " a2=" v12 " a3=" v13 " a4=" v14 " a5=" v15 " a6=" v16 " a7=" v17;
    idtac " s2=" v18 " s3=" v19 " s4=" v20 " s5=" v21 " s6=" v22 " s7=" v23 " s8=" v24 " s9=" v25 " s10=" v26 " s11=" v27;
    idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_rs_cl AF_huf_rs_fin AF_fse_rd_mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_rs_tail () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7gran_okI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_rs_pure7rs_tailC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_rs_fin5rresAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC47Corelib5Lists7ListDef3mapC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3ArrArw_cells_of_u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_rs_tail?unp_of_zshadowAC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_mem=amemsetZ_postC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablk_app_blkC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_mem=amemset_specZC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib3ArrAu8arr_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u32sC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit<zshadow_appWC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib5Lists4ListClength_zero_iff_nilC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z3oppI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes3orbK5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC56Stdlib6ZArith6BinInt1Z7eqb_neqI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_rs_cl5cl_okC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_rs_cl7clA_invC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<collect_loopK47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit?unpoisoned_appWC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=stk_transportC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_rs_fin4finAC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_rs_cl8clA_loopC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib9micromega;ZifyClasses5mkappK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWI5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_Zc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_rs_tail<u32s_zero13AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C46Stdlib5Lists4List8nil_consC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStatsCHUF_SYMBOLVALUE_MAX".

Section CANSEC1. Context {rc : runConstT}.

Lemma u32s_zero13A : u32s (map (Z_to_bv 64) (repeat 0 13)) = repeat (Z_to_bv 8 0) (Z.to_nat 52).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_rs_tail ()) ["CANSEC1"] "p;1p;2p;3g0000j10Tg000Uj19Tg0013j13Tg001Vj12Tg0026j28Tg002\j11Tg003Aj17Tg003_j14Tg004?j35Tg004^j26Tg0058R0#0#0#0#9R1#3R2#2g005],81%10#0#1#0#0#7#4552'6o"). Qed.

(* [comment removed for export] *)
Lemma unp_of_zshadowA : forall m A n, zshadow m A n -> 0 <= A -> A + n <= 2^64 -> 0 < n -> unpoisoned m A (A + n).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_rs_tail ()) ["CANSEC1"] "h04__x1h14__x2h21Zh37__arithh44__ffh54__p1h68__varmaph75__with84__x3h94__x4h:1Gh;1Hh<2H3h=2Hah>4__x5h?5heq_ah@1zhA1AhB2H0hC2H1hD3H10hE3H11hF2H2hG2H4hH2H5hI2H6hJ2H7hK2H8hL2H9hM3HG1hN3HG2hO3HLThP2HnhQ7__sat12hR7__sat13hS1ahT1bhU1mhV1nhW1qhX2q0hY1rhZ2r0h[3z11h\2z3p&0p;1p;3p;2p;4p;6p;7p;8p1006;p4p7210g006gR0p4p710p8g0000j1BTg000Uj1hTg0013j1_Tg007Ej1pTg007gk30ATg008jj20Tg003Aj1PTg009Gj2xTg009dj23Tg00:@j21Tg00:\j25Tg002\j1STg00;9j1ATg00;hj2gTg00<Jj37Tg00<dj2eTg00=Aj2dTg00=^j2bTg00>Vj26Tg00?1k206Tg00?Kk105Tg001Vk101Tg00?kj2LTg00@Ij1~Tg00@gj1wTg00ARj2OTg00B5j2JTg00BXj1qTg00C:j2mTg004^j2MTg00C\j2lTg00DHj3kTg00Dgj4jTg00EYj1iTg00F7j3QTg00FZk30@Tg0026k20?Tg00G=j2KTg00GZj2fTg00H<j2RTg00HVk10>Tg00I4k20<Tg00IUj1ITg00J4j3WTg00J]j2cTg00KFj3XTg00Kij1YTg00Laj2<Tg00M>k104Tg00N7k603Tg00NSj2^Tg00O4k100Tg00OMj2:Tg00Omj2]Tg00PTj2ZTg00Q;j2\Tg00Qaj2[Tg00RGj2}Tg00Roj3yTg00SSj2UTg00T?j2zTg00Thj3vTg00UQj6{TP0j6|Tg00V5j1uTg00Vjk302Tg00WDj4TTg00W_j4tTg00X9j3sTg00Y4j4VTg00Y_j7rTg00ZCk807Tg00Zgk408Tg00[Ek309Tg00[nk20:Tg00\Zk30;Tg00]:j7oTg00]^j6nTg00^Bk70=Tg005]R0f0R1'3p=9g00^fR2f1R3g00_DP1CVp=DP3g00_kR4g00`JR5P5g00`jR6P1g00aJFrp=2f3R7P4P5P5P6f2R8P3P1L07p=8P2P8P3P1H08p=EA7231p=;A7231,68p=>1531,K8p=?1c21p=FB09231p=4g00aj-0:1p=Hg00bVR9@0;31p==P2P3g00cBP1CVp=GP2P3g00ciP1CVp=@P8P4P5P5P6P3P1Fop=CP3P4P5P5P6P1Enp=aP8P4P5P5P6P3P1K0=p=`A7210p=Ng0058R:#BR;#BR<#BR=#B#B#BR>#hR?#_%h=R@#_RA#pRB[B0A831%981078%P;RC%P>R>'xRD'31107f5RE#9f4RF,0ERG/3DRHf6RI10IE'1RJf7RK%P=R=/53%S:RL#S#PRM'0'3RN15=8f8RO/0K'1RPf;RQg00dPRR/0F#AO11gA157B15=FRS/0=f:RTf9RU'0RV'e/dS/b1'6XTARW-06A[[[^:2RX'6&059RY&019R91L23%~2RZ%w2R[1O20R\1J2:R]'D,2[R^%q5R_P^C81m[6R^P1P8g00eJR`g00ejRa'M1l18=7`adAk203CjRab4b6b7X02%91%93[^02P1PIP7O2b3PHPXPYP91L28%i2RX7E3PZP[1J2;RH9Q2]1O2C>0@2?'D,2[R?P_P?C8P^Pab4b6b7X02X121013/3D1038/3D[^02^12P1PEPIP8O3b3PAPW20?@0R@PT10R7#AO11gA@RA57B15=7RW/0=10UO'e/dWR?/b@1KUWP2POP11KTSR`,M21;1`R`eP`15=ER`,fQ11Q`1KQ`Rb;>`13`Q?>bQ'Rf<Rb??=IR`P2p-0Rc&0>:-0<2R:g00fJRd#IRe#IRf#IRg#FRh5W21c2dRd'4Ri#H%FeRe/4d,4h#H%FfRf/4d,4h#H%IgRg#FRj/4i#H/=Y'='='=P91L2FRi?E8X1L277E3PZP[1O2=Rk1J2<5X2R<,G],2[1@H<,2[5C[1a[I1@H],2[5C[5`[P_P[1J2LRl9Q2]Rm,G<,2[P_P[1G]m,2[P_1D]H,2[1GHm,2[5C[C8C8C8P^Pab4b6b7X02X12X82X92W5111W?>3WA>F31'R1037,1S108F,18137F107E,1F'6[[[^02^12^82^92^5cP115=ORmf>R<'3POf=ROP3P<P8PEPKO8b3b\b<b?13T1111V'6eO2PQ%Y1#AO1=7BAP2%Y3PO%A1O1=7BAX@2P11<3=,0RRV&043J03Pb%AVO1=7BA1^`=%N=R`$00RVA?O=KRn1<n=,5=1:n='0';[1]n=110=Rn1K<mRm/:=Ro#911o='6[1Zm=11=0Rmf?Ro??=URp/:=Rq,1=13q0'6[1\p=f@Rp??=TRq/<=#N\`1[q=fA??=QRq/:=/;q\`1<q=P2fBRq??=b/:=P21^U=1<T=,5=1:T='0,;T\V1]T=1:Q=RT#911T='6\n1ZQ=1:b=RQ,1=13Q0'6\m1\b=1<O=#N\`1[O=1:<=/;<\`1<<=P21:o=P2fJRbfD7?=Rm,M21;pmRmePmfKRmfE,5=Rp'f11mp1KmpRQ;>p13pm?>Qm'RfLfF7?=P21}C>110C%9>110D[[%9CRQg00fiRmAyC>3UW=%9D\m^=Q%IgRg#I#F%FgRg9W2:14hf'4Rh'414de#HRQ'UAW2:fRf/4e,4j,4g/UQ1z2==v2d,4f,4j,4g#H1UhQ/=Y'='='=P91L2E9EX8AEi7X7E3PZP[1a[K%S;,J2R;AX2k]RZ'@,2[5C[1DZl,2[1@;l,2[5C[5`[P_P[P[1G\k,2[P_%BL,J2RL,D\,2[1GLk,2[5C[C8P_P[P[P[P4P5P5P61@k\,2[E{P_AX2kH=Q2L,@;,2[C8P_P[1O2M9Q2Z,Dl,2[P_1@]H,2[C8C8C8C8P^Pab4b6b7X02X12X82X92X>2X5c15=1Ra9>E713a8?>78'R%9I11I='6\ng00gE\`10SK,;I[10WM,3E1;FE[[[[^02^12^82^92^>2^5cP1fPRc15=b'1POP7PcP<PbPFPqfCfHO:b3bQbRb[bEb?bZbXbDbLbKbJbIbYbWbHbGb<bFb;1<8=,;IR8eP8P21<7=Po10R1#AO1=7BAX@2P3PKP1E|P<10RK#AO1=7BAP1b2b;b2b2bS%u@R@#N13?@13@M'61M20402CTCtXNPXMNXOJX:2CTCTAsIEGeWPWCWBW2XV2XA2WUo"). Qed.

Lemma ablk_appA : forall a b, ablk a b -> b <= KLOW \/ KHIGH <= a.
Proof. intros a b H. unfold ablk in H. pose proof ATOP_hi. unfold KLOW, KHIGH, AIMG_HI, KLS in *. lia. Qed.

Section TLA.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (m0 : amem) (RNG : footprint) (HW RK NSP TLP iS lo RLO2 RHI2 : Z) (ws : list Z) (jr junk : list byte) (nsv tlv : word).
  Variable Q : machine_state -> Prop.
  Hypothesis HWS : 0 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HIS : 0 <= iS <= 128.
  Hypothesis HJK : zlen junk = 256 - zlen ws.
  Hypothesis HJR : zlen jr = 52.
  Hypothesis HHW : ablk HW (HW + 256).
  Hypothesis HRK : ablk RK (RK + 52).
  Hypothesis RK4 : RK mod 4 = 0.
  Hypothesis HNS : ablk NSP (NSP + 4).
  Hypothesis HTL : ablk TLP (TLP + 4).
  Hypothesis NS4 : NSP mod 4 = 0.
  Hypothesis TL4 : TLP mod 4 = 0.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.
  Hypothesis DHN : HW + 256 <= NSP \/ NSP + 4 <= HW.
  Hypothesis DHT : HW + 256 <= TLP \/ TLP + 4 <= HW.
  Hypothesis DRN : RK + 52 <= NSP \/ NSP + 4 <= RK.
  Hypothesis DRT : RK + 52 <= TLP \/ TLP + 4 <= RK.
  Hypothesis DNT : NSP + 4 <= TLP \/ TLP + 4 <= NSP.
  (* [comment removed for export] *)
  Hypothesis RKA : u8arr bsegs m0 RK jr.
  Hypothesis HWA : u8arr bsegs m0 HW (map (Z_to_bv 8) ws ++ junk).
  Hypothesis NSC : rw_cells bsegs m0 NSP [C4 nsv].
  Hypothesis TLC : rw_cells bsegs m0 TLP [C4 tlv].
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis STK : stk bsegs m0 lo SP.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP - 2208.
  Hypothesis SPH : SP + 64 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis ZHW : zshadow m0 HW 256.
  Hypothesis ZRK : zshadow m0 RK 52.
  Hypothesis UNS : unpoisoned m0 NSP (NSP + 4).
  Hypothesis UTL : unpoisoned m0 TLP (TLP + 4).
  (* [comment removed for export] *)
  Hypothesis HULL : RLO2 <= RK /\ RK + 52 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND.
  Hypothesis HWR : wr_at bsegs m0 (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis HRR : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RHW : rng RNG HW 256.
  Hypothesis RHWs : rng RNG (shad HW) (nshad (256 + HW mod 8)).
  Hypothesis RRK : rng RNG RK 52.
  Hypothesis RRKs : rng RNG (shad RK) (nshad (52 + RK mod 8)).
  Hypothesis RNS : rng RNG NSP 4.
  Hypothesis RNSs : rng RNG (shad NSP) 1.
  Hypothesis RTL : rng RNG TLP 4.
  Hypothesis RTLs : rng RNG (shad TLP) 1.

  Notation WT := [(SP - 2208, SP); (HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)].
  Notation EXIT mm a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 :=
    (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a0v) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 x23 x24 x25 x26 x27
             y28 y29 y30 y31)
        F (Z_to_bv 64 0x9780c) fc None mm (seg_rom bsegs)).

  Local Ltac post_callK segs m :=
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO;
    destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
    destruct PO as [E [MUc [WMc PO]]];
    first [ destruct PO as [MIc PO] | rename PO into MIc ];
    subst ms';
    lazymatch type of MUc with
    | munch _ m ?m' =>
        let MUK := fresh "MUK" in let WMK := fresh "WMK" in
        pose proof MUc as MUK; pose proof WMc as WMK;
        transport_after_call segs m m' MUc WMc;
        clear MUc WMc
    end;
    try destruct_ands PO;
    try (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end).
  Local Ltac callK SPEC :=
    lazymatch goal with
    | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) =>
        eapply evtF_cut; [ eapply SPEC | post_callK segs m ];
        try (lazymatch goal with |- rng _ _ _ => solve_rng end)
    end.

  Lemma tlA : forall (x1 x5 x6 x7 x10 x11 x15 x16 x17 x19 x21 x22 x28 : word),
    (forall m2 a0v (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word),
       munch WT m0 m2 -> wmono bsegs m0 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo SP ->
       AF_huf_rs_fin.rresA HW RK NSP TLP (RF_huf_rs_pure.rs_tail ws (zlen ws) iS) m2 a0v ->
       evtF bsegs RNG Q (EXIT m2 a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31)) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 RK) (Z_to_bv 64 (zlen ws)) x10 x11 (Z_to_bv 64 HW) (Z_to_bv 64 NSP) (Z_to_bv 64 TLP)
               x15 x16 x17 (Z_to_bv 64 iS) x19 (Z_to_bv 64 2147450880) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x974f8) fc None m0 (seg_rom bsegs)).
Proof.
intros x1 x5 x6 x7 x10 x11 x15 x16 x17 x19 x21 x22 x28 KX.
pose proof (ablk_lin _ _ HHW) as (HWa & HWb & HWc & HWd).
pose proof (ablk_lin _ _ HRK) as (RKa & RKb & RKc & RKd).
pose proof (ablk_lin _ _ HNS) as (NSa & NSb & NSc & NSd).
pose proof (ablk_lin _ _ HTL) as (TLa & TLb & TLc & TLd).
wk_step. wk_step. wk_step. wk_step. wk_step. wk_step. wk_step.
assert (UNR : unpoisoned m0 RK (RK + 52)) by (apply unp_of_zshadowA; [exact ZRK|lia|lia|lia]).
pose proof (rw_cells_of_u8arr _ _ _ _ RKA) as RKC.
replace (length jr) with (Z.to_nat 52) in RKC by (rewrite ?Zlength_correct in HJR; lia).
pose proof RTC as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
callK (AF_fse_rd_mem.amemset_specZ RK 52 0 SP).
all: first [ lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ RK _ => exact RKC
| |- rw_cells _ _ _ _ => assumption
| |- app_blk _ _ => apply ablk_app_blk; [exact HRK| lia]
| |- unpoisoned _ _ _ => exact UNR
| |- wr_at _ _ _ _ => eassumption
| |- rng _ _ _ => eassumption
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
| |- _ => unfold KHIGH, KEND, AIMG_HI in *; lia
end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
lazymatch goal with P : rw_cells bsegs ?mm RK [CB _ (repeat _ _)] |- _ => rename mm into m1; rename P into P0 end.
assert (AW1 : appW [(SP - 2208, SP); (RK, RK + 52)]).
{ apply appW_cons; [right; unfold KHIGH in *; lia|]. apply appW_cons; [apply ablk_appA; exact HRK|]. apply appW_nil. }
pose proof (zshadow_appW _ _ _ _ _ ZHW MUK AW1 ltac:(lia) ltac:(lia)) as ZHW1.
pose proof (zshadow_appW _ _ _ _ _ ZRK MUK AW1 ltac:(lia) ltac:(lia)) as ZRK1.
pose proof (unpoisoned_appW _ _ _ _ _ UNS MUK AW1 ltac:(lia) ltac:(lia)) as UNS1.
pose proof (unpoisoned_appW _ _ _ _ _ UTL MUK AW1 ltac:(lia) ltac:(lia)) as UTL1.
pose proof (u8arr_of_rw_cells _ _ _ _ _ P0) as RK0.
assert (RKZ : u32arr bsegs m1 RK (map (Z_to_bv 64) (repeat 0 13))).
{ unfold u32arr. rewrite u32s_zero13A. destruct RK0 as [RB RW]. split; [exact RB|]. exact RW. }
assert (MUW : munch WT m0 m1).
{ eapply munch_weaken; [|exact MUK]. intros a Ha. cbn [outside] in *. tauto. }
wk_step.
destruct (Z.eq_dec (zlen ws) 0) as [Z0|ZP].
{ wk_step. wk_step.
  eapply (KX m1 (-20)); [exact MUW|exact WMK|assumption|assumption|].
  destruct ws as [|w ws']; [|cbn in Z0; lia].
  unfold RF_huf_rs_pure.rs_tail. cbv zeta. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. cbn.
  repeat split; try lia. }
assert (HW0 : 0 < HW) by (unfold AIMG_HI in HWa; lia).
wk_step. wk_step. wk_step. wk_step.
wk_go [0x97548].
lazymatch goal with |- context [Z_to_bv 64 (Z.lxor HW ?k)] =>
  replace (Z_to_bv 64 (Z.lxor HW k)) with (Z_to_bv 64 (18446744073709551615 - HW))
  by (rewrite (lnot_mod64 HW) by lia; rewrite Z_to_bv_mod64, Z.lnot_eq_pred_opp; apply Z_to_bv_eqm;
      replace (18446744073709551615 - HW) with ((- HW - 1) + 1 * 2^64) by lia; rewrite Z_mod_plus_full; reflexivity) end.
assert (HWS1 : 1 <= zlen ws <= 255) by lia.
assert (AWR : appW [(RK, RK + 52)]) by (apply appW_cons; [apply ablk_appA; exact HRK|]; apply appW_nil).
assert (HWB0 : bytes_at bsegs m1 HW (map (Z_to_bv 8) ws)) by (destruct HWA as [HB _]; apply bytes_at_app in HB; tauto).
eapply (AF_huf_rs_cl.clA_loop _ gp tp F fc _ _ _ _ _ _ _ x23 x24 x25 x26 x27 m1 RNG HW RK ws Q HWS1 HWB HHW HRK DHR ZHW1 ZRK1 AWR RHW RHWs RRK RRKs
  (Z.to_nat (zlen ws)) 0 (repeat 0 13) 0 m1).
- lia.
- lia.
- split; [reflexivity|split; [repeat constructor; lia|lia]].
- split; [exact RKZ|split; [exact HWB0|split; [apply munch_refl|split; [apply wmono_refl|assumption]]]].
- intros m2 rank' wt' y13 y14 y28 y29 y30 y31 CL CO INV.
  destruct INV as (RKA2 & HWB2 & MU2 & WM2 & MI2).
  change (skipn (Z.to_nat 0) ws) with ws in CL.
  assert (HWA2 : u8arr bsegs m2 HW (map (Z_to_bv 8) ws ++ junk)).
  { eapply u8arr_transport; [exact HWA|exact MU2|exact WM2|]. cbn [disjoint_from]. rewrite length_app, length_map. lia. }
  assert (NSC2 : rw_cells bsegs m2 NSP [C4 nsv]) by (eapply rw_cells_transport; [exact NSC|exact MU2|exact WM2|cbn; lia]).
  assert (TLC2 : rw_cells bsegs m2 TLP [C4 tlv]) by (eapply rw_cells_transport; [exact TLC|exact MU2|exact WM2|cbn; lia]).
  assert (MUF : munch [(HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)] m1 m2).
  { eapply munch_weaken; [|exact MU2]. intros a Ha. cbn [outside] in *. tauto. }
  assert (AWF : appW [(HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)]).
  { repeat (apply appW_cons; [apply ablk_appA; assumption|]). apply appW_nil. }
  eapply (AF_huf_rs_fin.finA (Z_to_bv 64 SP) gp tp F fc x23 x24 x25 x26 x27 y29 y30 y31 m1 RNG HW RK NSP TLP iS ws junk nsv tlv Q); try eassumption.
  intros m3 a0v y1 y5 y6 y7 y8 y9 y11 y12 y13' y14' y15 y16 y17 y18 y19 y20 y21 y22 y28' MU3 WM3 MI3 RR.
  eapply KX.
  + eapply munch_trans; [exact MUW|]. eapply munch_weaken; [|exact MU3]. intros a Ha. cbn [outside] in *. tauto.
  + eapply wmono_trans; [exact WMK|exact WM3].
  + exact MI3.
  + eapply stk_transport_disjoint; [exact PC|exact MU3|exact WM3|]. cbn [disjoint_from]. lia.
  + exact RR.
- intros m2 rank' y13 y14 y17 y28 y29 y30 y31 CE INV.
  destruct INV as (RKA2 & HWB2 & MU2 & WM2 & MI2).
  change (skipn (Z.to_nat 0) ws) with ws in CE.
  eapply (KX m2 (-20)).
  + eapply munch_trans; [exact MUW|]. eapply munch_weaken; [|exact MU2]. intros a Ha. cbn [outside] in *. tauto.
  + eapply wmono_trans; [exact WMK|exact WM2].
  + exact MI2.
  + eapply stk_transport_disjoint; [exact PC|exact MU2|exact WM2|]. cbn [disjoint_from]. lia.
  + unfold RF_huf_rs_pure.rs_tail. cbv zeta. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CE. cbn.
    repeat split; exact eq_refl.
Qed.
End TLA.
End CANSEC1.
