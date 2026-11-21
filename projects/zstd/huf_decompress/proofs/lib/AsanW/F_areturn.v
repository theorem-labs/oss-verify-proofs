(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (outside_In8, sub_fp_cover8, rta_copy_loop_spec and 2 more); rta_copy_loop_spec and rta_spec are zstd/simple_decompress's AsanT/F_areturn.v proofs (its file at main), rta_spec's return pc moved by the function's own offset (0x2218, the same at its three statement pcs): the recorded walks stepped the old store-conditional; junk_of_cells' keeps its recorded proof, which names the unit's interp_eff_accesses and stepF shims, proved equal to the model's). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase AKit AKit2 AKitR ARep ARepKit ARepFrame RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_agetfrom F_amaybe.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_areturn () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List=Exists_existsc59OSSVerify5KrLib5AsanW9F_areturn;outside_In8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C47Corelib5Lists7ListDef:Forall_indC59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3addC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u32arr_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC59OSSVerify5KrLib3Lib6MStateKinterp_eff_accesses_nv_shimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_gnvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF=rng_acc_litZ'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib3Arr?u32arr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u32arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3minC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List9app_assocI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:skipn_all2C59OSSVerify5KrLib5AsanW:F_agetfrom=firstn_S_snocC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;skipn_skipnC46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat6min_idC46Stdlib5Lists4List=firstn_firstnC46Stdlib5Lists4List:firstn_appC47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib3Lib3Arr<u32arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib5Lists4List;firstn_all2C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_agetfrom:sx32_smallC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega=RingMicromega5Psatz05I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepKit=junk_of_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlIcls_set_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aclass01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8SysStepF?implF_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aensure;ensure_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlAensure_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aensure8m3_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4iclrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9F_areturn7rta_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7F_ammap:rmap_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5AsanW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_frameC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib3Lib8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec4v_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib3Lib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AKitBamo_alignedD_introC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff07K4ELinuxProcessSemantics5Riscv3Sem3eff08C56Stdlib6ZArith6BinInt1Z8eqb_reflK4ELinuxProcessSemantics5Riscv3Sem3eff01C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aensure>m3_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5azeroC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib4LibA5StepF=stk_lo_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aensure:ensure_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA9rng_fp_leC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib5AsanW5AKitR:junk_of_cbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepKit:junk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5AKitR:junk_at_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5AKitR>u32arr_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib5AsanW4ARep7fill_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9F_areturnBrta_copy_loop_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_amaybe:maybe_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_amaybeBmaybe_release_specC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List6Exists01c59OSSVerify5KrLib5AsanW9F_areturn=sub_fp_cover8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame:fill_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_agetfrom;aclass_eta0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9F_areturn:set_mfa_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrameBget_cls_put_cls_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9F_areturn>junk_of_cells'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5AKitR>u32arr_app_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zb_shl_shrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EC59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ATSDC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr6awidth02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9F_areturn9rta_entryC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib5AsanW5ABase7AIMG_LOC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop07C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition rta_entry : Z := 0x34278.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr asegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> (forall k, 0 <= k < n -> rng RNG (DST + 4 * k) 4) ->
  evtF asegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1' a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34408) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x343f4) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  zstep.                                                 (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK. clear RD1.
  zstep.                                                 (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_areturn ()) ["CANSEC2"] "h01nh11Ah21Hh32H0h42csh51mp;1p;4p;3p;6g00C`j10Tg00XKj14Tg00Xij13Tg00YLj15Tg0030j1;Tg02[Ej4:Tg02\;j11Tg00[Kj12Tg008ej36Tg02]4j37Tg02]kj48Tg000kj69Tg00Td#0#0#0R0#0#0#0#4#3%40#3#5[g00;SR0g02^k#;g02Ljf3R1f2R2f1R3C:%12#2=603P0%11#2f6f5R4f0R537X00P4f4P1P3C8P2P5E9W3W2X00W4W1W5o"). Qed.

Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n SRC lo : Z) (src : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let nf2 := nf + n in
  fp_le RNG RNG' /\
  exists mfa' sj',
     (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ get_cls st2 c = mkAClass (c_mapped_user r) (c_allocated_user r) nf mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
  /\ munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp);
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf2); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ u32arr asegs m' (FA + 4 * nf) src
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n SRC lo : Z) (sj src : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RTA_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c -> a4 = Z_to_bv 64 SRC -> a5 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  u32arr asegs m SRC src -> length src = Z.to_nat n -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof.
  intros until src. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.
  (* [comment removed for export] *)
  destruct (junk_split m (aregion_info L c + 72) 8 48 J72 ltac:(lia) ltac:(lia)) as [J72a J80].
  destruct (junk_split m (aregion_info L c + 72 + 8) 8 40 J80 ltac:(lia) ltac:(lia)) as [J80a J88].
  destruct (junk_split m (aregion_info L c + 72 + 8 + 8) 8 32 J88 ltac:(lia) ltac:(lia)) as [J88a J96].
  replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) in J80a by lia.
  replace (aregion_info L c + 72 + 8 + 8) with (aregion_info L c + 88) in J88a by lia.
  replace (aregion_info L c + 72 + 8 + 8 + 8) with (aregion_info L c + 96) in J96 by lia.
  destruct (c8_of_junk m _ J72a) as [stn STN]. destruct (c8_of_junk m _ J80a) as [w80 W80]. destruct (c8_of_junk m _ J88a) as [w88 W88].
  destruct J96 as [j96 J96].
  clear J72 J72a J80 J80a J88 J88a.
  iprefix.
  carve_frame 128%nat ST.
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box STN. box W80. box W88. box J96. box STATS. box CH. box FJ. box AZF.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.                                                  (* [comment removed for export] *)
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC RIE NF MFA; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |]
  end.
  clear AZF.
  box MU01.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  destruct ER as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZF2 & MC2).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).   (* [comment removed for export] *)
  { rewrite !shad_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF. Z.div_mod_to_equations. lia. }
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF TIC TB SHFL; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W80 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W88 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport J96 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF CHK0 CHK1 N Y TIC TB SHFL; lia).
  eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia].
  clear ST MI REG STATS MC1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC MC.
  (* [comment removed for export] *)
  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  destruct (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) as (ws0 & U0 & L0). clear JD JD4.
  set (DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) in *.
  replace (ret_pc (Z_to_bv 64 213980)) with (Z_to_bv 64 213980 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * 0)) ltac:(subst DST; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 10 (Z_to_bv 64 (SRC + 4 * n)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 22 (Z_to_bv 64 (SRC + 4 * 0)) ltac:(f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (rta_copy_loop_spec RNG' _ 0 n SRC DST src ws0); try reflexivity.
    - clear -N; lia.
    - exact LCH.
    - rewrite L0. clear -N; lia.
    - exact CH.
    - exact CH31.
    - cbn [Z.to_nat firstn skipn app]. exact U0.
    - exact MI2.
    - clear -CHK0 T0 TIC TB; lia.
    - clear -CHK1 T1 N TIC TB; lia.
    - subst DST. clear -SP1 HC NF; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). clear -SP2 HC NF N NEWB MFA; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). ub TSP. clear -Y CHK0 CHK1 T0 T1 SP1 SP2 HC NF N NEWB MFA TIC TB. destruct Y as [Y|Y]; [left; lia| right; lia].
    - intros kk Hkk. eapply rng_sub'; [exact RT|]. clear -CHK0 CHK1 Hkk N; lia.
    - intros kk Hkk. subst DST. destruct (Z_lt_le_dec (4 * nf + 4 * kk) mfa) as [LT|GE].
      + eapply rng_sub'; [exact RFA|]. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia).
        destruct M4 as [q Hq]. clear -LT Hkk NF Hq. lia.
      + ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & _ & _ & R1 & _)].
        * exfalso. clear -E GE Hkk NEWB. lia.
        * eapply rng_sub'; [exact R1|]. clear -GE Hkk NEWB. lia. }
  cbv beta. intros ms' (a1x & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
  xport FR MU3 WM3 ltac:(subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  xport MTX MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STN MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W80 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W88 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport J96 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport REG2 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; subst DST; ub TSP; clear -SP1 SP2 HC T0 T1 NF N NEWB Y TIC TB; lia).
  eapply junk_frame in JR; [| exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; subst DST; clear -NF N; lia].
  pose proof (stk_transport_disjoint asegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia)) as ST3.
  assert (AZF3 : azero m3 (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new))).
  { eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 |]. intros _; cbn [disjoint_from].
    rewrite shad_div, shlen_div; unfold ASHOFF; subst DST; clear -SP1 SP2 HC NF N NEWB; Z.div_mod_to_equations; lia. }
  assert (MC3 : m3_cells L m3).
  { eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. ub SCX; unfold AIMG_HI, AIMG_LO.
    apply Forall_cons; [cbn [fst snd]; subst DST; clear -CX0 CX1 SP1 SP2 HC NF N NEWB Y CXI; lia |]. apply Forall_nil. }
  clear ST2 MI2 AZF2 MC2 U0. box MU3. box MU2.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.
  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MTX. box STN. box W88. box J96. box REG2. box W80.
  snapshot [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z MUm WMm.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of REG2 with boxed (rw_cells _ _ _ [C8 _; C8 _; C8 (Z_to_bv 64 ?auv); C8 _; C8 (Z_to_bv 64 ?muv); C8 _]) =>
    lazymatch type of W80 with boxed (rw_cells _ _ _ [C8 ?w80v]) =>
      call_sp (maybe_release_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm L c lo (nf + n) new auv muv w80v w88);
      [ exact ST3 | atop_facts; exact CEIL | clear -LO; lia | assumption | reflexivity | reflexivity | reflexivity
      | exact MC4 | unboxed REG2 | unboxed W80 | unboxed W88 | unfold K_NUM_CLASSES; exact HC | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | ]
    end end end.
  rename POST into ST5.
  carry SR3 MUm WMm ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry DS3 MUm WMm ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  carry STATS2 MUm WMm ltac:(rewrite LSJ2; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry MTX MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG2 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  eapply junk_frame in JR; [| exact MUm | exact WMm | intros _; cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MC5 : m3_cells L mm); [eapply m3_cells_frame; [exact MC4 | exact MUm | exact WMm |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI; lia |]; apply Forall_nil |];
    assert (MU35 : munch [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                          (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z m3 mm);
    [ eapply munch_trans; [eapply munch_weaken; [| unboxed MUs] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |];
    pose proof WMs as WM35;
    assert (AZF5 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF3 | exact MU35 | exact WM35 |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |]
  end.
  clear MC4 AZF3.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MUx4 : munch [(aregion_info L c, aregion_info L c + 8)]%Z x14 mm) by (eapply munch_weaken; [| exact MUu]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia);
    eapply junk_frame in JR; [| exact MUx4 | exact WMu | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia];
    assert (AZF6 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF5 | exact MUx4 | exact WMu |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |];
    assert (MC6 : m3_cells L mm); [eapply m3_cells_frame; [exact MC5 | exact MUx4 | exact WMu |]; unfold AIMG_HI, AIMG_LO; ub SCX;
      apply Forall_cons; [cbn [fst snd]; clear -SP1 SP2 HC RIE CX0 CX1 Y CXI; lia |]; apply Forall_nil |]
  end.
  clear MC5 AZF5 MUu.
  apply evtF_done. eapply KONT.
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mu au nf mfa. rewrite FAE.
  split; [exact FPLE|].
  exists new, sj'.
  (* [comment removed for export] *)
  lazymatch goal with |- context [munch ?W m ?mm] =>
    assert (MUT : munch W m mm);
    [ ub MU01; ub MU3; ub MU35; ub MU2; subst DST;
      eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y2] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y1] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |]
  end.
  assert (WMT : wmono asegs m _) by (eapply wmono_trans; [exact WM01 | eapply wmono_trans; [exact WM2 | exact WM3]]).
  split.
  { ub UD. destruct Y as [(_ & E & _ & _)|(LT & E & _ & _ & FILL & R1 & R2 & BW)]; [left; exact E| right].
    split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
    ub MU3; ub MU35; subst DST.
    eapply (fill_frame [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * n);
                        (aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                        (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128); (aregion_info L c, aregion_info L c + 8)]%Z);
      [exact FILL | | exact WM3 |].
    - eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia.
    - intros _. cbn [disjoint_from]. rewrite shad_div, shlen_div; unfold ASHOFF. clear -SPR CEIL LO SP1 SP2 HC NF N NEWB NEWGE MFA RIE. Z.div_mod_to_equations; lia. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
  assert (GC2 : get_cls st2 c = mkAClass mu au nf new (c_count (get_cls st c))).
  { ub UD. destruct Y as [(_ & E & -> & _)|(_ & _ & -> & _)].
    - rewrite E. subst mu au nf mfa. symmetry. apply aclass_eta0.
    - rewrite get_cls_put_cls_eq. subst mu au nf mfa. apply set_mfa_eq. }
  split; [exact GC2|].
  split. { ub UD. destruct Y as [(_ & _ & -> & _)|(_ & _ & E & _)]; [left; reflexivity| right]. rewrite GC2. rewrite E at 1. f_equal; subst mu au nf mfa; apply set_mfa_eq. }
  split; [exact MUT|]. split; [exact WMT|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact REG2|].
  split. { replace 56 with (8 + (8 + (8 + 32))) by reflexivity.
           apply junk_merge; [eapply junk_of_cells'; [exact STN| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W80| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 80 + 8) with (aregion_info L c + 88) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W88| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 88 + 8) with (aregion_info L c + 96) by (clear; lia). exists j96. exact J96. }
  split; [exact STATS2|]. split; [exact LSJ2|].
  split; [exact (proj1 (u32arr_app_inv _ _ _ _ DS3))|].
  split; [eapply junk_at_eq; [exact JR | subst DST; clear; lia | clear; lia]|].
  split; [exact AZF6| exact MC6].
Qed.
End CANSEC2.
