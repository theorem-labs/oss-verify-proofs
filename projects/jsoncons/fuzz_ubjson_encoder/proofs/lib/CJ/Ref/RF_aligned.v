(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import F_syscalls RMallocRep RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc Monad.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_aligned () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Peano2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C46Stdlib5Lists4List9nth_errorI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateCZ_to_bv_bv_unsignedC13~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C47Corelib4Init5Logic3notK46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAwrite_to_mem_specC13~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep?ref_mrd_overlayC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned@bytes_at_overlayC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le4C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec9mstep_detC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec6msteps00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec5mstepC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes7at_nodeC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree01C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned>evt_after_stepC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4nretC13~~~C47Corelib4Init5Logic9False_indI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4respC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad1MC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned?impl_after_stepC13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5implMC13~~~I47Corelib4Init9Datatypes4prod00I:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc00C13~~~C47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5epostC13~~~K:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc01C13~~~K:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc02C13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree9itree_indC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned=impl_post_evtC13~~~K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4aregC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node02C13~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List6concatC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes;iovec_bytesC13~~~I46Stdlib5Lists4List7Forall200K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node03C13~~~C56Stdlib6ZArith6BinInt1Z5ldiffC46Stdlib5Lists4List2InK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node04C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node05C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node06C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node08C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node09C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0:C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0;C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0<C13~~~K45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic5False00C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9O_CLOEXECC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;O_LARGEFILEK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node07C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned<raa_pre_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_carveC13~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C47Corelib5Lists7ListDef6firstnK4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z4landC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2K4ELinuxProcessSemantics5Riscv5Instr5instr09C56Stdlib6ZArith6BinInt1Z6shiftrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z4lxorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_xoriC13~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_xoriC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge7zr_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge7zr_lxorC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned7RAA_SYMC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned7RAA_RETC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned<RMALLOC_IMPLC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C45stdpp9bitvector;definitions@Z_to_bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le1C13~~~I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned<raa_fin_postC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_mulC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5m_mulC13~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge>zb_land_mask_lC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateAunsigned_lit_wrapC13~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr0=C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_subwC13~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_subwC13~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z9mod_smallC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;swrap32_eq'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_andiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_andiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_orC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6alu_orC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7mul_0_lC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_1'C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_alignedAwrite_to_mem_sameC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned6le1_wzC13~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep?signed_wz_smallC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_4'C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned7lor_hdrC13~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell03C13~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le2C13~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep@size_class_rangeC13~~~C47Corelib4Init9Datatypes9andb_propC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge;zr_land_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4zx16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@zext_extract_le2C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_subC13~~~C56Stdlib6ZArith6BinInt1Z7mod_addC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free3sxvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sllwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_sllwC13~~~C56Stdlib6ZArith6BinInt1Z=pow_lt_mono_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sxv_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_metaAland_pow2_testbitC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RF_aligned<raa_fin_walkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeAunsigned_lit_landC13~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;land_pgmaskC13~~~C46Stdlib4Bool4Bool<andb_false_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7zx16_wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sxv_smallC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_fast8sxv_landC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;sx32_wz_sxvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_meta;sllw1_word'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge<zb_land_maskC13~~~K46Stdlib9micromega=RingMicromega5Psatz01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=RSIZE_CLASSESC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02K47Corelib4Init9Datatypes:comparison03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_to_mem_same : forall bs m a,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i) ->
  write_to_mem m (wa a) bs = m.
Proof.
  intros bs m a Ha Hl H. extensionality x.
  rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  rewrite <- (H (Z.to_nat (bv_unsigned x - a))) by lia.
  replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) by lia.
  unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_overlay : forall m a bs,
  bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0xec000 <= a) ->
  forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m a bs (A0 & Ahi & BA) OUT i Hi. rewrite <- (BA i Hi). symmetry. apply ref_mrd_overlay.
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_overlay1 : forall m a b,
  rw_cells rsegs m a [C1 b] -> (a + 1 <= 0x10000 \/ 0xec000 <= a) -> m (wa a) = Some b.
Proof.
  intros m a b [[_ BA] _] OUT. cbn [cells_bytes cbytes app] in BA.
  pose proof (bytes_at_overlay m a [b] BA OUT 0%nat ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma rw_cells_overlay4 : forall m a (w : word),
  rw_cells rsegs m a [C4 w] -> (a + 4 <= 0x10000 \/ 0xec000 <= a) ->
  forall i, (i < 4)%nat -> m (wa (a + Z.of_nat i)) = nth_error (le4 w) i.
Proof.
  intros m a w [[_ BA] _] OUT. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  intros i Hi. apply (bytes_at_overlay m a (le4 w) BA); rewrite ?length_le4; [exact OUT| exact Hi].
Qed.

(* [comment removed for export] *)
Section AFTER.
Lemma evt_after_step : forall (P : machine_state -> Prop) ms ms1,
  evt rsegs P ms -> mstep rsegs ms ms1 -> (P ms -> P ms1) -> evt rsegs P ms1.
Proof.
  intros P ms ms1 (ms' & Hs & HP) ST HPP. inversion Hs; subst.
  - apply evt_done. apply HPP. exact HP.
  - pose proof (mstep_det rsegs _ _ _ ST H) as ->. exists ms'. split; assumption.
Qed.

Lemma impl_after_step : forall {R} (t : itree node R) Q ms ms1,
  impl rsegs (at_node rsegs) t Q ms -> mstep rsegs ms ms1 ->
  (forall r, Q r ms -> Q r ms1) -> (forall n, ~ at_node rsegs n ms) ->
  impl rsegs (at_node rsegs) t Q ms1.
Proof.
  intros R t Q ms ms1 H ST HQ HN. destruct t as [r|n k]; cbn [impl] in *.
  - eapply evt_after_step; [exact H| exact ST| apply HQ].
  - eapply evt_after_step; [exact H| exact ST|]. intros [Hat _]. exfalso. exact (HN n Hat).
Qed.

Lemma implM_after_step : forall {TS A : Type} (c : Monad.M TS A) (s : TS) Q ms ms1,
  implM rsegs c s Q ms -> mstep rsegs ms ms1 ->
  (forall a s', Q a s' ms -> Q a s' ms1) -> (forall n, ~ at_node rsegs n ms) ->
  implM rsegs c s Q ms1.
Proof.
  intros TS A c s Q ms ms1 H ST HQ HN. unfold implM in *. eapply impl_after_step; [exact H| exact ST| | exact HN].
  intros [|[a s']]; cbn [epost]; [trivial| apply HQ].
Qed.

(* [comment removed for export] *)
Lemma impl_post_evt : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl rsegs (at_node rsegs) t Q ms -> (forall r ms', Q r ms' -> evt rsegs (Q' r) ms') -> impl rsegs (at_node rsegs) t Q' ms.
Proof.
  intros R t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn [impl] in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma implM_post_evt : forall {TS A : Type} (c : Monad.M TS A) (s : TS) (Q Q' : A -> TS -> machine_state -> Prop) ms,
  implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
  intros TS A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn [epost fst snd]; [intros _; apply evt_done; exact I| apply HQ].
Qed.
End AFTER.

(* [comment removed for export] *)
Lemma at_node_svc_none : forall n R F pc fc m ro, ~ at_node rsegs n (MS R F pc fc None m ro).
Proof.
  intros n R F pc fc m ro H. destruct n; cbn [at_node ms_svc_pending MS] in H;
    repeat match type of H with _ /\ _ => destruct H as [H _] | _ \/ _ => destruct H as [H|H] end; discriminate H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RAA_SYM : Z := 0x9dde0.       (* [comment removed for export] *)
Definition RMALLOC_IMPL : Z := 0x9ea4c.  (* [comment removed for export] *)
Definition RAA_RET : Z := 0x9de80.       (* [comment removed for export] *)

Definition raa_pre_post (sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (n : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (junk : list byte) m',
    ms' = MS (mkR (wz RAA_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz 16) (wz n) (wz n) (wz n) (wz 16) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 RMALLOC_IMPL) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra].

Lemma raa_pre_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo n : Z),
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv rsegs m ->
  rw_cells rsegs m (RCTX + 928) [C4 (wz 0); C4 (wz 0)] ->   (* [comment removed for export] *)
  a0 = wz 16 -> a1 = wz n -> 0 <= n <= 2^32 ->
  evt rsegs (raa_pre_post sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra n F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_SYM) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros ST CLO LO MI REPL -> -> Hn. unfold RAA_SYM. pose_ceil. unfold RCTX in REPL. replace (963664 + 928) with 964592 in REPL by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  step. step. step. step.

  step. step. step. if_false.

  step. step. if_false.

  step. step. if_cases K; zify_cond K.
  { exfalso. revert K. rewrite !wz_unsigned by lia. change (Z.lxor 16 18446744073709551615) with 18446744073709551599. lia. }

  step. step. step. if_true.

  step. step. if_false. step. step. step. step. step. step.
  replace (16 + n + -16) with n by lia. unfold raa_pre_post. finish. exact FR.
Qed.

(* [comment removed for export] *)
Lemma raa_null_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (junk : list byte) (s1o s0o rao : word) (n : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs (fun ms' => ms' = MS (mkR rao (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rao) fc None m (seg_rom rsegs))
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros FR. unfold RAA_RET at 2.
  step. if_true. step. step. step. step. step. apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.


Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


Lemma lor_hdr : forall r idx, 0 <= idx < 32 -> 0 <= r -> Z.lor (r * 32) idx = idx + 32 * r.
Proof.
  intros r idx Hi Hr.
  assert (D : Z.land (r * 32) idx = 0).
  { apply Z.bits_inj'. intros i Hi0. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 5) as [L|L].
    - change 32 with (2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite andb_false_iff. right.
      destruct (Z.eq_dec idx 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. pose proof (Z.add_nocarry_lxor _ _ D). lia.
Qed.

Lemma le1_wz : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.
End CEIL_WRAP_2.


(* [comment removed for export] *)
Local Ltac mem_after_store_opt ::= idtac.

(* [comment removed for export] *)
Ltac restore_mem E :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      replace (write_to_mem m a bs) with m;
      [| symmetry; replace a with (wa E) by (unfold wa; f_equal; lia);
         apply write_to_mem_same; [lia| cbn [length]; rewrite ?length_le4; lia|] ]
  end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition raa_fin_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR rao (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rao) fc None m (seg_rom rsegs).

Lemma raa_fin_walk : forall (sp gp tp t0 t1 a1 a3 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 : word) F fc m
   (junk : list byte) (s1o s0o rao : word) (n P B EE QQ stride res b3 off16 idx : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> P <= EE + 4 ->
  rw_cells rsegs m (bv_unsigned a0 + -4) [C1 (b8 0); C1 (b8 b3); C2 (wz off16)] ->
  0 <= b3 < 256 -> 0 <= idx < 32 -> idx = Z.land b3 31 -> 0 <= stride ->
  EE = B + 16 + stride * (idx + 1) - 4 -> 0 <= B -> QQ = P + n -> res = EE - QQ ->
  0 <= n -> 0 <= res < 2^31 -> EE + 4 <= alloc_ceiling ->
  b3 = idx + 32 * Z.min res 5 ->
  (0 < res -> res <> 5 -> rw_cells rsegs m QQ [C1 (b8 0)]) ->
  (5 <= res -> rw_cells rsegs m (EE + -5) [C1 (b8 0); C4 (wz res)]) ->
  (* [comment removed for export] *)
  m (wa (P - 3)) = Some (b8 b3) ->
  (0 < res -> m (wa (EE - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (EE - 5)) = Some (b8 0)) ->
  (5 <= res -> forall i, (i < 4)%nat -> m (wa (EE - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 (Z_to_bv 64 (0 + - bv_unsigned a0)) (wz 16) (wz n)
               a0 a1 (wz n) a3 (wz B) a5 (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9dfa8) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros FR CSP SPH HP P0 AL PEE HDR B3 IDX HIDX STR0 HEE HB0 HQQ HRES Hn RES EEH HB3 TZ T5 O3 OZ O5 O4.
  pose_ceil.
  assert (STR : 0 <= stride * (idx + 1) <= EE) by nia.
  assert (ONE1 : forall (a : Z) (b : byte), m (wa a) = Some b -> forall i, (i < length [b])%nat -> m (wa (a + Z.of_nat i)) = nth_error [b] i).
  { intros a b Hb i Hi. destruct i; [rewrite Z.add_0_r; exact Hb| cbn in Hi; lia]. }

  st1. st1. st1. st1. st1. st1.
  replace (Z.land 15 (bv_unsigned (Z_to_bv 64 (0 + - bv_unsigned a0)))) with 0.
  2:{ rewrite HP. rewrite unsigned_lit_wrap by lia. change 15 with (2^4 - 1). rewrite zb_land_mask_l by lia. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^4) with 16. clear -AL P0. Z.div_mod_to_equations. lia. }
  replace (B + 16 + stride * (idx + 1) + -4) with EE by lia.
  replace (B + 16 + stride * (idx + 1)) with (EE + 4) by lia.
  st1. if_cases K13; zify_cond K13. 2:{ exfalso. rewrite ?wz_unsigned in K13 by lia. lia. }

  st1. st1. rewrite <- HP in HQQ. replace (n + bv_unsigned a0) with QQ by lia.
  replace (bv_swrap 32 (EE - QQ)) with res. 2:{ rewrite <- HRES. symmetry. rewrite swrap32_eq'. rewrite Z.mod_small; lia. }
  st1. if_cases K14; zify_cond K14.
  -
    rewrite ?wz_unsigned in K14 by lia.

    st1. st1. st1. st1.
    rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32. rewrite <- HIDX.
    replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
    replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
    replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3, K14, Z.mul_0_l, Z.lor_0_l; lia).
    st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }

    st1. st1. st1. st1. st1. st1.
    unfold raa_fin_post. finish.
  -
    rewrite ?wz_unsigned in K14 by lia.
    st1. replace (bv_swrap 32 (EE - QQ)) with res by (rewrite <- HRES; symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
    st1. st1. st1.
    replace (bv_swrap 32 (0 - res)) with (- res) by (symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
    destruct (Z.eq_dec res 5) as [R5|R5].
    +
      specialize (T5 ltac:(lia)). clear TZ.
      replace (EE + - res) with (EE + -5) by lia.
      st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
      st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }

      st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
      st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
      st1.

      st1. st1. st1. st1. rewrite <- HIDX.
      replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
      replace (Z.lor 160 idx) with b3 by (rewrite HB3, R5; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
      st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
      st1. st1. st1. st1. st1. st1.
      unfold raa_fin_post. finish.
    + replace (EE + - res) with QQ by lia.
      specialize (TZ ltac:(lia) R5).
      destruct (Z_lt_le_dec res 5) as [R4|R6].
      *
        clear T5.
        st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
        st1. if_cases K15; zify_cond K15. 2:{ exfalso. rewrite signed_wz_small in K15 by lia. lia. }

        st1. st1. st1. st1. st1. rewrite <- HIDX.
        rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32.
        replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
        replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
        replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3; rewrite lor_hdr by lia; lia).
        st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
        st1. st1. st1. st1. st1. st1.
        unfold raa_fin_post. finish.
      *
        specialize (T5 R6).
        st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
        st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }
        st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
        st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
        st1.
        st1. st1. st1. st1. rewrite <- HIDX.
        replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
        replace (Z.lor 160 idx) with b3 by (rewrite HB3; replace (res `min` 5) with 5 by lia; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
        st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
        st1. st1. st1. st1. st1. st1.
        unfold raa_fin_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma raa_tail_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (junk : list byte) (s1o s0o rao : word)
   (n P G B AR EE QQ stride res : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P ->
  B = P - 16 * off16 - 16 -> AR = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned a0 + -4) [C1 (b8 0); C1 (b8 b3); C2 (wz off16)] ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa AR) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63 /\ last_idx = 0 /\ maplen <> 0) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
  EE = B + 16 + stride * (idx + 1) - 4 -> QQ = P + n -> res = EE - QQ ->
  0 <= n -> 0 <= res < 2^31 -> EE + 4 <= alloc_ceiling -> P <= EE + 4 ->
  b3 = idx + 32 * Z.min res 5 ->
  (0 < res -> res <> 5 -> rw_cells rsegs m QQ [C1 (b8 0)]) ->
  (5 <= res -> rw_cells rsegs m (EE + -5) [C1 (b8 0); C4 (wz res)]) ->
  m (wa (P - 3)) = Some (b8 b3) ->
  (0 < res -> m (wa (EE - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (EE - 5)) = Some (b8 0)) ->
  (5 <= res -> forall i, (i < 4)%nat -> m (wa (EE - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword FR CSP SPH HP P0 AL PLO HB HA GLO GHI HDR RG MM RA RC RS B3 O16 AV FRD SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml HST HEE HQQ HRES Hn RES EEH PEE HB3 TZ T5 O3 OZ O5 O4. unfold RAA_RET at 2.
  pose proof CSP as CSP'. pose proof EEH as EEH'. pose_ceil.
  assert (PHI : P + 16 <= 2^64) by nia.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  pose proof (size_class_range sc) as SZR.
  assert (STR : 0 <= stride).
  { rewrite HST. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
    - apply andb_prop in E as [_ E]. destruct (maplen =? 0) eqn:M0; [discriminate|]. apply Z.eqb_neq in M0. lia.
    - destruct (Z_lt_le_dec sc 48); [specialize (SZR ltac:(lia)); lia|].
      destruct (Hsc63 ltac:(lia)) as (-> & E1 & E2). rewrite E1 in E. cbn in E. destruct (maplen =? 0) eqn:M0; [|discriminate]. apply Z.eqb_eq in M0. lia. }

  st1. if_cases K0; zify_cond K0. { exfalso. lia. }

  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }

  st1. st1. st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1. clear RG'.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. fold idx. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (MW3 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MW4 : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }

  assert (FIN : forall (t0' t1' a1' a3' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
    m' = m ->
    evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0' t1' (Z_to_bv 64 (0 + - bv_unsigned a0)) (wz 16) (wz n)
               a0 a1' (wz n) a3' (wz B) a5' (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x9dfa8) fc None m' (seg_rom rsegs))).
  { intros t0' t1' a1' a3' a5' t3' t4' t5' t6' m' ->.
    eapply (raa_fin_walk sp gp tp t0' t1' a1' a3' a5' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' a0 F fc m junk s1o s0o rao
              n P B EE QQ stride res b3 off16 idx); try eassumption; try lia; try reflexivity. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. st1. st1. if_cases K8; zify_cond K8.
  -
    destruct (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)) as (Hsc63' & HLI0 & HML0).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }

    st1. rewrite MW3. st1. st1. if_cases K10; zify_cond K10. { exfalso. rewrite ?wz_unsigned in K10 by lia. lia. }

    st1. st1. st1. if_cases K11; zify_cond K11.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K11 by lia. change (2^8) with 256 in K11. change 18446744073709551615 with (Z.ones 64) in K11.
        rewrite Z.land_ones, ?wz_unsigned in K11 by lia. rewrite Z.mod_small in K11 by lia. specialize (Hml HML0). lia. }

    st1. if_cases K12; zify_cond K12. 2:{ exfalso. rewrite ?wz_unsigned in K12 by lia. lia. }

    st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
    assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, HLI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
    replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
  -
    assert (SC48 : sc < 48) by (rewrite ?wz_unsigned in K8 by lia; lia).
    specialize (RS SC48). specialize (Hsc SC48). specialize (SZR ltac:(lia)).

    st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (110520 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (110520 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1.

    st1. rewrite MW3. st1. st1. if_cases K12; zify_cond K12.
    +
      rewrite ?wz_unsigned in K12 by lia.
      assert (HSTR : stride = 16 * size_class sc). { rewrite HST, K12. cbn [Z.eqb negb andb]. rewrite andb_false_r. reflexivity. }

      st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
      apply FIN. reflexivity.
    +
      rewrite ?wz_unsigned in K12 by lia.
      st1. st1. st1. if_cases K13; zify_cond K13.
      2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K13 by lia. change (2^8) with 256 in K13. change 18446744073709551615 with (Z.ones 64) in K13.
          rewrite Z.land_ones, ?wz_unsigned in K13 by lia. rewrite Z.mod_small in K13 by lia. specialize (Hml K12). lia. }

      st1. if_cases K14; zify_cond K14.
      *
        rewrite ?wz_unsigned in K14 by lia.
        st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
        assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, K14. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
        replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
      * rewrite ?wz_unsigned in K14 by lia.
        assert (HSTR : stride = 16 * size_class sc). { rewrite HST. destruct (Z.eqb_spec last_idx 0); [lia|]. reflexivity. }
        st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
        apply FIN. reflexivity.
Qed.
End CEIL_WRAP_3.

