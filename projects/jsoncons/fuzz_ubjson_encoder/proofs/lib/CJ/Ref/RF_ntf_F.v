(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_ntf_F () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapI35stdpp4gmap4gmap00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B35mw_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_B8fm_factsC13~~~C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~K47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_A:rntf_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3?meta_word_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B=rntf_ret_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~K47Corelib4Init9Datatypes3nat02K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le1C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_1'C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMallocKit_B3=rmrep_set_seqC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B37le1_litC13~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=mem_inv_storeC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_F6seq_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc?sc_in_seq_rangeC13~~~C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_unmap_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:record_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3=record_seq_eqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C56Stdlib6ZArith6BinInt1Z3mulK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z4landC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B5fm_stC13~~~K46Stdlib9micromega7EnvRing5PExpr05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7set_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_F<fm_facts_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_A7rntf_fmC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rfree_fp_stackC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B<rfree_fp_ctxC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BIrpres_except_of_munch_covC13~~~C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B=rfree_fp_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeArpres_except_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeBrpres_except_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_A<meta_word_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;land_pgmaskC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C56Stdlib6ZArith6BinInt1Z3ltbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeAunsigned_lit_landC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_F>seq_range_testC13~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BAunmap_seqs_lengthC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr>u8arr_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMallocKit_B3Crmrep_set_unmap_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6s_tickC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions:bv_extractK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C35stdpp4base6insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocAset_unmap_seq_mapC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp4base6lookupK47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K46Stdlib9micromega=RingMicromega3Op201I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~K47Corelib7Numbers7BinNums8positive03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3@meta_word_maplenC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rmrep_seq_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8step_seqC13~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyC47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3;step_seq_eqC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_F8rntf_seqC13~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3ArrArw_cells_of_u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C47Corelib5Lists7ListDef5skipnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>rw_cells_congrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3ArrAu8arr_of_rw_cellsC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_F@unmap_seqs_emptyC13~~~K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B@rmrep_ctx_frameWC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK46Stdlib9micromega5Tauto8GFormula07C47Corelib5Lists7ListDef6firstnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_F=zeros32_cellsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
#[using="Type"] Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e658) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  (pose_ceil; unfold RCTX, rntf_frame in *).

  st1. rewrite ?(unsigned_lit sc) by lia. st1.

  pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
  pose proof (rw_cells_store_ok_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (963664 + 912)) C6 eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as SOK.
  clear C6.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish (963664 + 912) [b8 ns] FR ST MU WM SOK.
  set (st1 := upd_ctx (set_seq ns) st) in MR1.

  st1.
  assert (JOIN : forall m2 (a1' : word),
    rmrep (seq_st ns sc st) m2 -> mem_inv rsegs m2 ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (963664, 963664 + 928)] m0 m2 -> wmono rsegs m0 m2 ->
    stk rsegs m2 lo (bv_unsigned sp + -96) -> rw_cells rsegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 (wz canary_val); C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
    evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
                 (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 963664) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e670) fc None m2 (seg_rom rsegs))).
  { intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
    assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
    rmeta_chunk MR2 MS2 CH.
    assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
    rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.

    st1. st1. st1. st1. clear CH.
    rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
    replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
    eapply evt_mono.
    { eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
        first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | pose_ceil; lia | lia | idtac].
      unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
    intros ms' PO. unfold rntf_ret_post in PO |- *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
    do 14 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans.
      - apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
        cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
      - eapply rpres_except_mono; [exact PE|]. intros a Ha.
        eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
          unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
    split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
  if_cases K; zify_cond K.
  -
    assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
    eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
  - assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }

    st1.
    pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
    pose proof (u8arr_store_ok rsegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (963664 + (sc + -7) + 848)) US
                  ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    clear US.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish (963664 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
    eapply JOIN; try eassumption.
    unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
    match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
    unfold upd_ctx. cbn. reflexivity.
Qed.

#[using="Type"] Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. vmc_refl. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
  0 <= c_seq (ctx st) < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e5f8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  (pose_ceil; unfold RCTX, rntf_frame in *).

  st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.

  pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
  st1. clear RDS. st1.

  st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  -
    st1.
    replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
    2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
      first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | pose_ceil; lia].
  -
    pose proof MR as (_ & (_ & _ & _ & US & _) & _).
    pose proof (rw_cells_of_u8arr rsegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
    replace (963664 + 848) with 964512 in UB by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(963664 + 848, 963664 + 880)]%Z mX) as MUz; pose proof (wmono_refl rsegs mX) as WMz end.
    st1. st1. st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (UA' : u8arr rsegs mX (RCTX + 848) (zeros 32))
        by (apply (u8arr_of_rw_cells rsegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
    clear UB.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
    { eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
        unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }

    st1. st1.
    replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
    2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
    replace (conc st p) with (conc stz p) by reflexivity.
    change (get_meta_rec st g) with (get_meta_rec stz g).
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
      first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | pose_ceil; lia
            | apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.
End CEIL_WRAP_1.

