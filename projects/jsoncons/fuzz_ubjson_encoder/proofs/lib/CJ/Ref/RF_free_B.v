(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_free_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_free_B () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:rarea_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~K47Corelib4Init5Logic2eq01C35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9conc_aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rarea_lr_loC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B?rfree_fp_regionC13~~~C35stdpp4base6lookupI47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3bitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_set_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3lorC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9mask_uptoC13~~~C45stdpp9bitvector;definitions;bv_unsignedK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BArmeta_slot_boundsC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_B;rftriv_postC13~~~C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sxv_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free3sxvC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_orC13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6alu_orC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;lor_range64C13~~~C56Stdlib6ZArith6BinInt1Z4landC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free8sxv_zeroC13~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr0=C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addwC13~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_addwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=free_all_testC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_4'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le4C13~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~K46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>free_store_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>rw_cells_congrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BDrmrep_put_meta_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<upd_meta_putC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepDrmrep_transport_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;stk_releaseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rfree_fp_stackC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_B>rfree_fp_meta0C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BIrpres_except_of_munch_covC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C45stdpp9bitvector;definitions8bv_swrapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9addw_wordC13~~~C56Stdlib6ZArith6BinInt1Z8add_commC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>free_assert_okC13~~~C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z8lor_commC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;sx32_wz_sxvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C56Stdlib6ZArith6BinInt1Z2geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~K46Stdlib9micromega5Tauto8GFormula03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~K47Corelib4Init9Datatypes4bool02I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;RNEED_LOCKSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RPAGE_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep8RGOT_SSPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5msize04I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RMLOCKC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateCZ_to_bv_bv_unsignedC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init5Logic5proj2". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


#[using="Type"] Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
  conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof.
  intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

(* [comment removed for export] *)
Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ rpres_except C m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rmrep st' m'.

#[using="Type"] Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
  rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
  s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt rsegs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0xeb1c0) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e1c4) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  (pose_ceil; unfold RNEED_LOCKS in *).

  step. step. rewrite !sx32_wz_sxv by lia.

  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

  step. if_true.

  st1.

  step. if_cases K2; zify_cond K2.
  { exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
  clear K2.

  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
  pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
  step. if_cases K3; zify_cond K3.
  { exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
  clear K3 RSUM.

  step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
  rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
  step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia]. }
  clear K4 RL.

  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep st' mX) end.
  { unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    rewrite HG in MM.
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
    - reflexivity.
    - cbn. tauto. }
  clear MUg MM.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
    pose proof (wmono_refl rsegs mX) as WMs end.
  step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply rfree_fp_stack. lia.
      - intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
  finish.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  (m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
  evt rsegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
       ms' = MS (mkR (Z_to_bv 64 0x9e234) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                     (Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e39c) fc None m (seg_rom rsegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0xeb1c0) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e1c4) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  (pose_ceil; unfold RNEED_LOCKS in *).

  step. step. rewrite !sx32_wz_sxv by lia.

  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

  step. if_true. st1.

  step. if_cases K2; zify_cond K2.
  -
    st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia]. }
    st1. st1.
    apply evt_done. do 6 eexists. reflexivity.
  -
    step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
    rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
    rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
    pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
    step. if_cases K3; zify_cond K3.
    + st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia]. }
      st1. st1.
      apply evt_done. do 6 eexists. reflexivity.
    + exfalso. destruct HNT as [Hz|Hall].
      * apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
      * apply K3. rewrite ?wz_unsigned by apply sxv_range.
        apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        unfold bit, mask_upto in Hall. exact Hall.
Qed.
End CEIL_WRAP_1.

