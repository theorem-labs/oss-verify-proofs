(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the auxv as a list of pairs; addresses and numbers; new lemmas; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Tgt/RF_am_E.v, 198 lines within its lines 42-349. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_am_E () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8F_memcpy;memcpy_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C45stdpp9bitvector;definitions;bv_unsignedK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8F_memcpy;memcpy_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~I47Corelib4Init9Datatypes3nat00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:F_syscalls5rsegsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8F_memcpy5rsegsC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3mulC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr:u64s_splitC13~~~C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@bytes_at_ov_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free?rw_cells_prefixC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells<cells_wf_appC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells?cells_bytes_appC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem<bytes_at_appC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells>cells_size_appC13~~~C46Stdlib9micromega;ZifyClasses3injC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9wr_at_subC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree8rauxv_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:secret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=rmrep_globalsC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_E>ram_entry_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree9auxv_listC13~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_carveC13~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7w_addiwC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_mulC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5m_mulC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_E:ru64s_readC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_ECrrw_cells_app_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac>rw_cells_mergeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_E>rmemcpy_callZ3C13~~~K46Stdlib9micromega5Tauto8GFormula01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame=disjoint_fromC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameBbytes_at_transportC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameFstk_transport_disjointC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6sub_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame<munch_weakenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_evenC13~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2InC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepDrmrep_transport_highC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_4'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:set_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=set_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~I35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_B@rmrep_ctx_frameWC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_EBrrw_cells_app_joinC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A9ram_frameC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7sx32_wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemDbytes_at_write_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C45stdpp9bitvector;definitions:bv_extractC47Corelib4Init9Datatypes4negbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameBrw_cells_transportC13~~~K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_E:am_init_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep4RCTXC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;RNEED_LOCKSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RPAGE_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep8RGOT_SSPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RSSP_GUARDC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RAUXV_CELLC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep6RMLOCKC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
#[using="Type"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at rsegs m S src -> length src = Z.to_nat n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xae008) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

#[using="Type"] Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition aux_cur (pre : list (Z * Z)) (b0 : list byte) : list byte :=
  if existsb (fun p => fst p =? 25) pre then le8 (wz secret_val) else b0.

#[using="Type"] Lemma aux_cur_25 : forall pre v b0, aux_cur (pre ++ [(25, v)]) b0 = le8 (wz secret_val).
Proof.
  intros pre v b0. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(25, v)]) with true by reflexivity.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

#[using="Type"] Lemma aux_cur_skip : forall pre k v b0, k <> 25 -> aux_cur (pre ++ [(k, v)]) b0 = aux_cur pre b0.
Proof.
  intros pre k v b0 Hk. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(k, v)]) with false
    by (symmetry; cbn [existsb fst]; rewrite Bool.orb_false_r; apply Z.eqb_neq; exact Hk).
  rewrite Bool.orb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma aux_cur_last : forall L b0 r, last_assoc 25 L = Some r -> aux_cur L b0 = le8 (wz secret_val).
Proof.
  intros L b0 r H. apply last_assoc_In in H. unfold aux_cur.
  replace (existsb (fun p : Z * Z => fst p =? 25) L) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists (25, r). split; [exact H| reflexivity].
Qed.

Local Ltac aux_br :=
  lazymatch goal with |- context [bv_eqb ?x ?y] =>
    first [ replace (bv_eqb x y) with true
              by (symmetry; unfold bv_eqb; apply Z.eqb_eq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia)
          | replace (bv_eqb x y) with false
              by (symmetry; unfold bv_eqb; apply Z.eqb_neq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia) ]
  end;
  try change (negb true) with false; try change (negb false) with true; cbv iota.

Definition raux_post (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 0xece50) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0384) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 (aux_cur L b0)].

#[using="Type"] Lemma raux_walk : forall (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av rnd : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte),
  rw_cells rsegs m0 RAUXV_CELL [C8 (wz av)] ->
  bytes_at rsegs m0 av (u64s (map wz (flat_pairs L ++ [0; 0]))) ->
  bytes_at rsegs m0 (rnd + 8) (le8 (wz secret_val)) ->
  Forall (fun p => fst p <> 0) L -> Forall (fun p => fst p = 25 -> snd p = rnd) L ->
  Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L ->
  RAUXV_CELL + 8 <= bv_unsigned sp + -64 -> bv_unsigned sp <= av -> av + 16 * (Z.of_nat (length L) + 1) <= 2^64 ->
  bv_unsigned sp <= rnd + 8 -> rnd + 16 <= 2^64 -> 64 <= bv_unsigned sp ->
  forall post pre (m : word -> option byte) (x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  L = pre ++ post -> bv_unsigned s1 = 16 * Z.of_nat (length pre) ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 (aux_cur pre b0)] ->
  evt rsegs (raux_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av L b0 m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 0xece50) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0374) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av rnd L b0 m0 AVC AVL RND NZ R25 RNG HC HAV HAVH HR HRH HSP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAUXV_CELL in HC, AVC.
  assert (WZAV : bv_unsigned (wz av) = av) by (apply wz_unsigned; lia).
  induction post as [|[k v] post IH]; intros pre m x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EL HS1 MU WM MI FR.
  - (* [comment removed for export] *)
    rewrite app_nil_r in EL. subst L.
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs pre ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz 0) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_end pre) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1. aux_br.
    st1. aux_br.
    apply evt_done. unfold raux_post. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact FR.
  - assert (IN : In (k, v) L) by (rewrite EL; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) NZ _ IN) as NZk.
    pose proof (proj1 (Forall_forall _ _) R25 _ IN) as R25k.
    pose proof (proj1 (Forall_forall _ _) RNG _ IN) as RNGk.
    cbn [fst snd] in NZk, R25k, RNGk.
    assert (LL : Z.of_nat (length L) = Z.of_nat (length pre) + 1 + Z.of_nat (length post))
      by (rewrite EL, length_app; cbn [length]; lia).
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    assert (AVCm : rw_cells rsegs m 0xece58 [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]]).
    assert (RNDm : bytes_at rsegs m (rnd + 8) (le8 (wz secret_val)))
      by (eapply bytes_at_transport; [exact RND| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz k) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_key L pre k v post EL) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1.
    destruct (Z.eq_dec k 25) as [K25|K25].
    + (* [comment removed for export] *)
      subst k. specialize (R25k eq_refl). subst v.
      aux_br.
      pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre) + 1) (wz rnd) (wa (av + 8 * (2 * Z.of_nat (length pre) + 1)))
                    AVLm (flat_pairs_nth_val L pre 25 rnd post EL) ltac:(lia) eq_refl) as RD.
      st1. clear RD. st1. st1. st1. st1.
      call rmemcpy_callZ3.
      1:{ exact RNDm. } 1:{ reflexivity. } 1:{ exact FR. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end. }
      lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (le8 (wz secret_val))] |- _ => rename H into DST end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mY _) =>
        assert (AVCy : rw_cells rsegs mY 0xece58 [C8 (wz av)])
          by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]])
      end.
      st1. st1.
      eapply (IH (pre ++ [(25, rnd)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end.
      * rewrite aux_cur_25. exact DST.
    + (* [comment removed for export] *)
      aux_br.
      st1. aux_br.
      st1.
      eapply (IH (pre ++ [(k, v)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * exact MI.
      * rewrite (aux_cur_skip pre k v b0 K25). exact FR.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa03a4) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

#[using="Type"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = secret_val -> 0 <= c_secret (ctx st) < 2^64 ->
  evt rsegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa02f0) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold ctx_head_cells in C1.
  (pose_ceil; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *). unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & L & rnd & AVC & AVL & RND & (AB & BAV & AVH & BR & RH & XR) & NZ & LA & R25 & RNG).
  pose proof (conj AVC (conj AVL RND)) as AUX0.
  unfold RAUXV_CELL in AVC.

  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

  st1. st1. st1. st1. st1. st1.

  st1. rewrite sx32_wz by lia. st1. st1.

  st1.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }

  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.

  st1. st1. st1. st1. st1. st1. st1. st1. st1.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge rsegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  destruct AUX0 as (AVC0 & AVL0 & RND0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (AVCx : rw_cells rsegs mX RAUXV_CELL [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC0| exact MUh| exact WM| cbn [disjoint_from cells_size csize]; split; [unfold RAUXV_CELL; lia| exact I]]);
    assert (AVLx : bytes_at rsegs mX av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    assert (RNDx : bytes_at rsegs mX (rnd + 8) (le8 (wz secret_val)))
      by (eapply bytes_at_transport; [exact RND0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    lazymatch type of FRm with rw_cells _ _ _ [CB _ ?bz] =>
      eapply evt_cut;
      [ eapply (raux_walk sp gp tp _ _ _ _ _ _ _ _ _ F fc av rnd L bz mX AVCx AVLx RNDx NZ R25 RNG
                  ltac:(unfold RAUXV_CELL; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L []);
        [ reflexivity | first [reflexivity | vm_compute; reflexivity] | apply munch_refl | apply wmono_refl | assumption | exact FRm ]
      | post_call rsegs mX ]
    end end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (aux_cur _ _)] |- _ => rename H into DST end.
  rewrite (aux_cur_last L _ rnd LA) in DST.

  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz secret_val)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.

  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; pose_ceil; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.

  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret secret_val c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells rsegs ?mX 970704 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.

  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
End CEIL_WRAP_1.

