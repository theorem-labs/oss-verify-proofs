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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocModel_B F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | tauto ]]);
    clear MUq WMq CH end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_ntf_C () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~K47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~I47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:rarea_concC13~~~C56Stdlib6ZArith6BinInt1Z2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~K47Corelib4Init5Logic2eq01C35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9conc_aaddC13~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rarea_lr_loC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic9False_indC35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_C8qa_factsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_C8qpath_stC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_C;rqpath_postC13~~~C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI4ELinuxProcessSemantics5Riscv7Prelude4tree00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BArmrep_active_readC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z2gec99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_C>rconc_meta_injC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeArpres_except_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=optr_eqb_reflC13~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic8eq_transC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<aptr_eqb_neqC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>rw_cells_congrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BDrmrep_put_meta_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BBmeta_slot_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BCmeta_cells_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B=conc_put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BFget_meta_rec_put_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BEget_meta_rec_put_sameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BFput_meta_put_meta_sameC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B7fm_linkC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B9fm_singleC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<upd_meta_putC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8queue_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rfree_fp_stackC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B=rfree_fp_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BIrpres_except_of_munch_covC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B>actives_lengthC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr?u64arr_store_okC13~~~C56Stdlib6ZArith6BinInt1Z9add_assocC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_set_activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:set_activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem>wr_at_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=mem_inv_storeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B<rfree_fp_ctxC13~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK46Stdlib9micromega5Tauto8GFormula06K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a0 a2 a3 a5 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e71c) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

#[using="Type"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  (active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
  qa_facts st sc g ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e500) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
  (pose_ceil; unfold RCTX in *).

  st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.

  pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
  st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
  replace (Z_to_bv 64 (963664 + sc * 8 + 80)) with (wa (963664 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
  st1. clear RDA.

  st1. if_cases K; zify_cond K.
  {
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. pose_ceil. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
    unfold qpath_st. rewrite HA, optr_eqb_refl.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
  assert (HA : active st sc <> Some g).
  { intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
  destruct (GNP HA) as [GN GP].
  assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
  { unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
    replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
  rewrite QS. clear QS K.

  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  clear CH.

  st1. destruct (active st sc) as [hd|] eqn:HD.
  -
    destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
    assert (NEh : hd <> g) by congruence.
    pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.

    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
    set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
    assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).

    rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1. clear CHh.

    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
    assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).

    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
    st1. clear CH. st1.

    rmeta_open (conc st hd) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
    assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
      rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
      unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
  -
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (963664, 963664 + 928)]%Z m) as MU.

    st1.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.

    pose proof MRb as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (actives stB) sc (Z_to_bv 64 (963664 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
        by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
      pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
    end.
    assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3 SOK.

    pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
      pose proof (length_le8 (pw stB (Some g))) as L8;
      apply (rw_cells_frame rsegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
      apply (stk_write rsegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
      apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
      apply (wmono_write rsegs _ mX (wa A) bs) in WM;
      lazymatch goal with HI : mem_inv rsegs mX |- _ =>
        apply (mem_inv_store rsegs mX (wa A) bs) in HI;
        [| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok rsegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
      end;
      remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
    end.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.
End CEIL_WRAP_1.

