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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B F_ntf_C MallocKit_B MallocKit_B3 F_am_A F_am_D.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C RF_am_A.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_am_D () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C47Corelib4Init5Logic3iffK47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A9ram_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A<ram_ret_postC13~~~C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RF_ntf_C>rconc_meta_injC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~I35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_B@rmrep_ctx_frameWC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B7deq_midC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C47Corelib4Init9Datatypes4negbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=optr_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B;dequeue_midC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BDmeta_slot_same_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A8ram_tailC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A6ram_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A<ram_fp_stackC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A;ram_fp_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A:ram_fp_ctxC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BIrpres_except_of_munch_covC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A;ram_fp_sameC13~~~C47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTreeArpres_except_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTreeBrpres_except_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_transC13~~~K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~C47Corelib4Init5Logic5proj2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>rw_cells_congrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BDrmrep_put_meta_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BBmeta_slot_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BCmeta_cells_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B=conc_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BFget_meta_rec_put_otherC13~~~C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<ctx_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<upd_meta_putC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<aptr_eqb_neqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7dequeueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B9clr_linksC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums8positive03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RSSP_GUARDC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep6RMLOCKC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_A7am_tookC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt7RF_am_A6ram_b0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
  rmrep st m -> mem_inv rsegs m ->
  c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
  meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa03a4) fc None m (seg_rom rsegs)).
Proof.
  intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _). pose_ceil.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _). pose_ceil.
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _). pose_ceil.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (970704, 970704 + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.

  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.

  rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
  st1. clear CH.

  st1. if_cases K; zify_cond K.
  -
    assert (Enx : nx = h).
    { rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
    { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 970704 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 970288) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
        [exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
  -
    assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
    assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).

    rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.

    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR MSp CH.
    st1.
    rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
    set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

    rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. st1. clear CH.

    rmeta_open (conc st nx) MUn WMn.
    rmeta_chunk MR1 MSn1 CH.
    st1.
    rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
    set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).

    st1. st1.
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.

    rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.

    clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
    replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
    { eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
        unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 970704 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.

    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
      rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 970288) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
        [exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv rsegs m ->
  c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
  c_avail_meta (ctx st) = Some q -> meta_slot st q ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
               (am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa03a4) fc None m (seg_rom rsegs)).
Proof.
  intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _). pose_ceil.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).

  st1. st1.
  rewrite bv_eqb_refl. cbv iota.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
  rewrite CF; clear CF.
  st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
  replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
  change (Z_to_bv 64 970288) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 970696) with (Z_to_bv 64 RMLOCK).
  eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
    [exact MR | exact MI | exact MSq | lia | exact FR | exact ST | pose_ceil; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                   s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa03f8) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa03a4) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR FMH CNT.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.

