(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (implM_of_enode, stack_pieces, argv_cstring and 3 more); stack_pieces, argv_cstring restated for the revision's model; the launch values and the entry stack layout; stack_pieces, argv_cstring are zstd/simple_decompress's proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup F_atexit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RDriver_kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2eq00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib7InitMem9raw_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib7InitMem7pad_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib3Lib7InitMem9rnd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib7InitMemDbuild_stack_bytes_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib7InitMem:auxv_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9argv_ptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9envp_ptrsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC59OSSVerify5KrLib3Lib3Arr8u64s_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib3Lib7InitMem>raw_len_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;struct_sizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib7InitMemFflatten_strings_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib7InitMem4envcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib7InitMem8str_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8env_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8rnd_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8str_ptrsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib7InitMem?str_ptrs_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic5proj2C46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan4UImg7u_phdrsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib7InitMem<str_ptrs_nthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3oppC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib7InitMemHbuild_stack_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem7raw_lenC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib6Common8DrvAgree8ceil8_leC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List=nth_error_mapC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C59OSSVerify5KrLib3Lib7InitMem>bytes_at_sliceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic5False00c59OSSVerify5KrLib5Ubsan;RDriver_kit<stack_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common;Startup_kit9auxv_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RMalloc_ifaceP@RHEAP_init_proofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5Ubsan7Startup<pcrt_writtenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree:rauxv_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;draw_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;draw_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rnd_bytes_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RAUXV_CELLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan;RDriver_kit9heap_initC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z3injC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_image0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg;UREAD_STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan7RunDraw:PSTAGE_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan7RunDraw<PSTAGE_LEN_ZC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib5Ubsan;RDriver_kit?atx_state0_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface6PEMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrK46Stdlib9micromega7EnvRing3Pol03I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan;RDriver_kit>libc_head_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan;RDriver_kit<le4_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocHINV9HINV_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8F_atexit;PNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation pph := UImg.u_phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl usegs (at_node usegs) (enode n pl) (epost P) ms ->
  implM usegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Context {lx : launchT}.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis IMG : bytes_at usegs m usp IMGB.
  Hypothesis PADOK : (usp + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.

  Lemma stack_pieces :
    bytes_at usegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at usegs m (usp + 8) (u64s (argv_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (usp + 8 * (argc argv + envc envp + 3))
      (u64s (auxv_words L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) uid L_GID hw sp L_TOP argv envp L_EXECFN)) /\
    bytes_at usegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) /\
    bytes_at usegs m (env_base L_TOP argv envp L_EXECFN) (flatten_strings envp) /\
    bytes_at usegs m (rnd_addr sp (la_rseq L_LA) argv envp) (rnd_bytes draw).
  Proof.
    destruct (InitMem.stack_pieces usegs m L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw IMG PADOK)
      as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
    (* InitMem's order: ..., random bytes, argv strings, envp strings; [repeat split] would open bytes_at *)
    exact (conj B0 (conj B1 (conj B2 (conj B3 (conj B5 (conj B6 B4)))))).
  Qed.

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs L_TOP argv envp L_EXECFN) i = Some (Z_to_bv 64 p) /\ str_base L_TOP argv envp L_EXECFN <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length IMGB) /\
      bytes_at usegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base L_TOP argv envp L_EXECFN) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (build_stack_bytes_length_top L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw PADOK) as BL.
    pose proof (layout_bounds L_LA sp L_TOP argv envp L_EXECFN PADOK) as (LB1 & LB2 & LB3 & LB4).
    pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq L_LA) argv envp)) as HS0. unfold hsz in LB1.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base L_TOP argv envp L_EXECFN + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length IMGB)).
    { subst p e k. unfold env_base, execfn_base in *. split; lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) IMGB)).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) IMGB)) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice usegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base L_TOP argv envp L_EXECFN + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice usegs m usp IMGB (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app usegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (InitMem.rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 usegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section CANSEC2. Context {rc : runConstT}.
Section InitFacts.
  Context {lx : launchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x2a000 <= bv_unsigned a < 0x5d000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells usegs m 0x5bb30 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells usegs m 0x5bb38 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells usegs m 0x2a528 [C8 (Z_to_bv 64 0x5bb10)].
  Hypothesis GUARD : rw_cells usegs m 0x5bb10 [C8 CAN].
  Hypothesis MI : mem_inv usegs m.
  Hypothesis IMG : bytes_at usegs m usp0 (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis SPLO : sp_window_lo <= usp0.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.   (* [comment removed for export] *)
  Hypothesis HATOP : ATOP = usp0 - 8388608.
  Hypothesis PADOK : (usp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.
  Hypothesis TOPHI : (bv_unsigned L_TOP <= 0x800000000000)%Z.

  Lemma heap_init : RHEAP (ps_init (reservedZ usegs) ATOP) [] m /\ rw_cells usegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    intros a Ha. apply NONE; [lia|]. unfold pcrt_written. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rauxv_ok_init : rauxv_ok m usp0.
  Proof.
    destruct (stack_pieces sp0 argv envp uid hw draw m IMG PADOK) as (_ & _ & _ & AUXW & _ & _ & RND).
    pose proof (hsz_eq (la_rseq L_LA) argv envp) as HS. pose proof (gap_len_bound argv envp) as GB.
    pose proof (Nat2Z.is_nonneg (gap_len argv envp)).
    pose proof (bv_unsigned_in_range 64 sp0) as [R0 _]. unfold sp_window_lo in SPLO.
    unfold lstr in PADOK. pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp L_EXECFN)).
    atop_facts.
    exists (auxv_addr sp0 argv envp), (rnd_addr sp0 (la_rseq L_LA) argv envp), L_LA, (Z_to_bv 64 (Z.of_N u_init_pc)),
      uid, L_GID, hw, (Z_to_bv 64 (execfn_ptr L_TOP L_EXECFN)).
    split; [apply (proj2 heap_init)|].
    split. { unfold auxv_addr. exact AUXW. }
    split. { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
             rewrite HSEC. unfold wz. exact R. }
    unfold auxv_addr, rnd_addr, argc, envc in *.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stage_init : STG m.
Proof.
    exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold UREAD_STAGE.
    assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (InitMem.rw_cells_image0 usegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
    - vm_compute. reflexivity.
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_state0_init : atx_state false m.
Proof.
    unfold atx_state, atx_cells, PATX, PAEF_INCB. cbn [Z.add].
    pimg_chunk0 NONE m 0x5b8e8 [C1 (Z_to_bv 8 0)] X1.
    pimg_chunk0 NONE m 0x5b8ec [C4 (Z_to_bv 64 0)] X2.
    pimg_chunk0 NONE m 0x5b8f0 [C4 (Z_to_bv 64 0)] X3.
    pimg_chunk0 NONE m 0x5b8f8 [C8 (Z_to_bv 64 0)] X4.
    pimg_chunk0 NONE m 0x5b900 [C8 (Z_to_bv 64 0)] X5.
    pimg_chunk0 NONE m 0x5b908 [C8 (Z_to_bv 64 0)] X6.
    pimg_chunk0 NONE m 0x5ba08 [C8 (Z_to_bv 64 0)] X7.
    pimg_chunk0 NONE m 0x3b7a4 [C1 (Z_to_bv 8 0)] X8.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rstatx0_init : rw_cells usegs m 0x2b540 [C8 (Z_to_bv 64 0x2b540)] /\ (exists reg : bool, atx_state reg m).
Proof.
    pimg_chunk0 NONE m 0x2b540 [C8 (Z_to_bv 64 0x2b540)] D1.
    split; [exact D1| exists false; apply atx_state0_init].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_cells0_init : trun_cells0 m.
Proof.
    unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, wz.
    pimg_chunk0 NONE m 0x3b7a0 [C1 (Z_to_bv 8 0)] H1.
    pimg_chunk0 NONE m 0x2a4f0 [C8 (Z_to_bv 64 0)] H2.
    pimg_chunk0 NONE m 0x2a4e8 [C8 (Z_to_bv 64 0x2a498)] H7.
    pimg_chunk0 NONE m 0x2a498 [C8 (Z_to_bv 64 0x2b568)] H8.
    pose proof atx_state0_init as AX0.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma empty_cells_init : rw_cells usegs m PEMPTY [CB 16 (repeat (Z_to_bv 8 0) 16)].
Proof. unfold PEMPTY. pimg_chunk0 NONE m 0x3b7b0 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stderr_file0_init : stderr_file0 m.
Proof.
    unfold stderr_file0, file_cells, wz.
    pimg_chunk0 NONE m 0x2b568%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x23eb4 0x5bf70 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
    unfold file_cells in H. exact H.
  Qed.
End InitFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
  exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
  assert (HV : 0 <= v < 2^32) by (subst v; lia).
  replace (bv_wrap 64 v) with v by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small; [reflexivity|]; cbn; lia).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (E0 : Z_to_bv 8 v = b0).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E1 : Z_to_bv 8 (v / 2^8) = b1).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E2 : Z_to_bv 8 (v / 2^16) = b2).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E3 : Z_to_bv 8 (v / 2^24) = b3).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  rewrite E0, E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma libc_head_byte : forall (m : mem) (a : Z), 0x5bb30 <= a < 0x5bb38 ->
  exists b : byte, mrd usegs m (wa a) = Some b /\ wview usegs m (wa a) <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h02b0h11Hh22Hah31bi001bh41Eh51oi011oh64__x1h71ah82H0h93IMGh:2SRh;2WVh<7__arithh=4__ffh>8__varmaph?5__with@1ehA1mhB1xi021xi033segp;1p;2p;4p;7p;8p;3p;6g00K_j16Tg00LDj1TTg00NRj1STg00:lR0j1}Tg00`Wj1=Tg00ecj1dTg00O5j1aTg01@gj2_Tg012dj1|Tg013Bj1{Tg013mj2vTg01=hj4RTg01E>j7qTg00>lj1XTg01D6j8fTg0153j2eTg00@Fj2NTg015Uj2cTg00Fhj30Tg016Aj3bTg016`j4`Tg036`j11Tg00>Jj2DTg01SMR1j29Tg02aFj2zTg02b9j3yTg00UHj6^Tg037Oj2xTg008Ij6Mj7iTg00Lbj2LTg037nj3\Tg0392j1uTg03:4j1tTg03;3j1rTg02?bj1pTg01ZWj2ZTg03<1j1YTg03<Oj2UTg01[Uj1OTg00g8j15Tg01=2j2oTg00a5j2nTg00=oR2j2QTg014Pj2mTg01Bij7WTg01>Sj7kTg01=NR3j2PTg03=Vj2sTg03>Oj3]Tg00@`j4jTg01ilj4wTg03?Lj3hTf0R4#6#6p=K%64#5#5#6p=J%54#5#5#6p=I%54#5#6#6p=Cf3R5f2R6'of1R7/n4'Qp=?g01F@R8/m4p=@P7g01H@R9g01H_R:P:g01I?R;P4g01JFR<FWp=[P6P9P:P:P;P8P7g01I_P4CRP<FWp=B%64#5p=<%54#6p=l%54#6#5#5p=:%64#6#5#5p=H%54#5p=gP6P9P:P:P;P7P4Fkp=EA0856A0874'Pp=Ff4R<=085A0867/P4'Pp=3A0874p=2g00H7R=/s4p=4f6R>f5R?;0<A]=67=054#O'Qp=7A]=67=054#Op=8A0567/Q4p=>P>P?P<P5P6P7P4CjCwp=;P8P?P<P5P6P7P4Fip=AAh=74p=GA0674#Op=Vg01KSR@#6#KRA#6#K#TRB#SRC%TARA#SRD#}RE[%J@#I#C#C#K#=RFP4P4%J@#I#C#I#K#=RGC?RHg01O1RI#d%aI1_87%|8%{8RIP9P:P:P;PIP9P:P:P;P8%@FR9g01QI1v8@RJCR,[IP8PJg01jF%@GCR,[IFq%X:ABIJ9%J@#I#C#C#<#=R9#@9BIJ%J@#I#C#C#l#=R:#@9BIJ%<@#:#:#H#H#=RK#@9BIJ%<@#:#:#H#<#K#=RL#@9BIJ%<@#:#:#H#<#<#=RM#@9BIJ%<@#:#:#H#J#=RN#@9BIJ%<@#:#:#H#<#g#=RO#@9BIJ5EI5EI5EI5EI5EI5EI5EIGf1eI;P4P6g01O]RIg01P=R;'N1c46=0I;dg01EbR;=b87C`b=b>b?X68P7PFP7P9P7P:P7PKP7PLP7PMP7PNP7POCFD3D3D3RJ\H^68P4P6P7O2b<PJP3126FP6P9P6P:P6PKP6PLP6PMP6PN126OD3D3D3PE%1<RJ#41DD4RPPE%XDRQVCRCPJPQF7X0D,9DP4125FPFPE%16RR#4PPPEPCPRPQF7X0D,9DRR^2HX78RHPFPFPFPGC?PDPE%1FRS#4RTPPPEPCPSPQC8RSC>X0D1zA;9yA;R;1DD;RA90ETRTPS1NEARUPTdA0EAQPEPAP0PDp-0P4g0261g01n\RTn10110100021000000X@ERVg020<RWPQP4E^PT1xT4RXb1WBRYPSdF;W2P<P4P5EAW1P4O1P5P9P5P:P5PKP5PLP5PMP5PN125OD3D3D3P312<9P<P:P<PKP<PLP<PMP<PNP<POCFD3D3PE%1>RS#4RZPPPEPCPSPQC8RSC>X0D,9DP412?9P9PHPFP9P9PGC?PDPE%19R9#4R[PPPEPCP9PQC8R9C>X0DP;A0E[AR[P9PUP[dPYP9dF;W2P>P4P?EAW1P4O1P?P:P?PKP?PLP?PMP?PNP?POCFD3D3P312>:P>PKP>PLP>PMP>PN12>OD3D3PEf8R>#1R9#4R[PPPEPCP9PQF7X0D,9DP4f7R\/2:P:PHPFP:P:PGC?PDPE%1:R:#4R]PPPEPCP:PQC8R:C>X0DP;A0E]AR]P:PUP]dPYP:dF;W2P>P4P\EAW1P4O1P\PKP\PLP\PMP\PN12\OD3D3P312>KP>PLP>PMP>PNP>POCFD3PEf:R\#1R:#4PPPEPCP:PQF7X0D,9DP4f9R]/2KPKPHPFPKPKPGC?PDPE%1KRK#4R^PPPEPCPKPQC8RKC>X0DP;A0E^AR^PKPUP^dPYPKdF;W2P\P4P]EAW1P4O1P]PLP]PMP]PNP]POCFD3P312\LP\PMP\PN12\OD3PEf<R\#1RK#4PPPEPCPKPQF7X0D,9DP4f;R^/2LPLPHPFPLPLPGC?PDPE%1LRL#4R_PPPEPCPLPQC8RLC>X0DP;A0E_AR_PLPUP_dPYPLdF;W2P\P4P^EAW1P4O1P^PMP^PN12^OD3P312\MP\PNP\POCFPEf>RL#1R_#4R`PPPEPCP_PQF7X0D,9DP4f=Ra/2MPMPHPFPMPMPGC?PDPE%1MRM#4RbPPPEPCPMPQC8RMC>X0DP;A0EbARbPMPUPbdPYPMdF;W2PLP4PaEAW1P4O1PaPNPaPOCFP312LN12LOPEf@R3#1RM#4RbPPPEPCPMPQF7X0D,9DP4f?Rc/2NPNPHPFPNPNPGC?PDPE%1NRN#4RdPPPEPCPNPQC8RNC>X0DP;A0EdARdPNPUPddPYPNdF;W2P3P4PcEAW1P4O112cOPOPHPFPOPOPGC?PDPE%1ORO#4RGPPPEPCPOPQC8ROC>X0DP;A0EGARGPOPUPGdPYPOdF;W2P3P4PcEAW1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n201100000021100011000b4PRP1PDPE%15R1#4PPPEPCP1PQF7X0DPE1G?JPPPEP?PJPQF7X3D,9DP4PE%1?R?#4PPPEPCP?PQF7P21DD7R290EZPSPE1G]9PPPEP]P9PQF7X3D,9DP41DD590E[PEPC%1]PQC8P^P:O1PE1NE4P\%1^O1=0E4P0PDPL%1aR^O1R\=0E4PE%1cR:,G3RCPPPEP3P:PQC8R[C>X3D,9D]4P7PcP_O1=0EPPDPEfAR9/GMPPPEP9PMPQF7X3DP7A0EC2RCP[PEP2P0PDPEP4PPPbn101102000210100001DD6R650EX5E1NE2P3P:O1R3P4EMPCePEP2P0PDPEP4PPP0g01LoRCPE1LBM%=@R@5\=PIPE%u4RM%t4Rb%19,LB%r4#pR9'Z#Y'UPQn0100000020000PQn10110200021010300n10110200021010000=VEQX5EA0E2QR2PEP6PVPWPQP4E^PTPXb8W1%O2eP3P4EMP[eF;W4X3DP4O1PaPKO1=0EQPDPE1Gc_PPPEPcP_PQF7X3DP>1GL^1DD>50ER>PEPLP^PQC8R^PEPQP0PDPEP4PPP`n101102000210100001DD]50EX5EP<P\P4EMP>ePEPQP0PDPEP4PPP0PCPE1LB_=\=@PIPEPM1LB:/Z9#Y,UbPQn0100000020000PQn10110200021010300n10110200021010000=VEQX5EP5P\P4EMP^eF;W4n10110100021110001P4O1b4b5W;W:P7P4O2n2001000000121000000W1X0DP7P4O2n2001000000121102000b9W2X78WAo"). Qed.

Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells usegs m 0x5bb30 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h02Hih11Hh23tm1h33sech43thrh53cdth67__arithh74__ffh88__varmaph95__with:1bh;1ih<1eh=1ni001nh>3LB0h?4__x1h@1xi011xhA2_HhB3Hi0hC3_H0hD3_H1hE4__p1hF2sthG1whH1zhI1EhJ3HtmhK2LBhL4MREPhM2NLhN3NLBhO3NLWhP2R0hQ2R1hR2R2hS2R3hT2R4hU2R5hV2R6hW2R7hX2W0hY2W1hZ2W2h[2W3h\2W4h]2W5h^2W6h_2W7h`3_H2ha3_H3hb2b0hc2b1hd2b2he2b4hf2b5hg2b6hh2b7hi4cstrhj1lhk1mhl1shm1yp%0p&0p;1p;4p;2p;3p;5p;6p;<p;7p;8g00O5k109Tg02Chk40{Tg03@<j1[Tg01SMR0j20Tg00K_j1?Tg00LDk10ATg00NRk10<Tg00`Wj1;Tg00POk20dTg02b\k10OTg02f;k106Tg00eck105Tg03A2j3kTg03Amk20JTg03Bnj3uTg03Cmj2gTg03E0k300Tg02;?j1~Tg02K3j4ZTg03F1k10ZTg02<7k104Tg03Fik10UTg00=oR1j2<Tg012Fk10tTg012dk10qTg013Bk10pTg0153k20hTg00@Fj2XTg015Uk20fTg00Fhj37Tg016Ak30cTg016`k40bTg01=2j2GTg03G^j3^Tg00:lk10aTg036`j1FTg00>Jj2wTg00>lk10NTg03Hck40^Tg02n[k10LTg03Ifk403Tg02eBk10KTg00c8R2j1PTg02cQk10ITg02dHk10HTg00cXj4jTg00bXk201Tg029Fk20]Tg03J]R3j26Tg01Sgj3hTg018=k30Ek50BTg00jHR4j12Tg00a5S00j2bTg014Pk20DTg017Rk40[Tg00eFj2HTg03K5k40?Tg00@`j4STg00Sfk30>Tg02Imk30YTg00g8j1=Tg00UHk60;Tg01eWk40:Tg011ak10WTg01@gk20VTg013mk20TTg01DZk60STg008Ik60zk70QTg02Z6k30yTg010`k10xTg01@Bm<08Tg02Z\k60vTg01ilj4yTg03Kgk30nTg03LRk10mTg03MGk10kTg03N>k50jTg00XSj3LTg03O>k20iTg03P@k20lTg01=hj4oTg01Bij7pTg01E>k70PTg03?Lj3mTg03>Oj3xTg01[Uj1zTg01Ack30gTg01?]m<0RTg01D6k80eTg01>Sk70uTg01=NR5j2nTg02MXR6f1R7f0R840np=eg03QBR9&0m8777p=Uf3R:g03R;f2R;&0k7P8I0jp=NAk:;7/<8p=f1<78,<;p=E%?8#?p=a%?8#=#=#?p=i%=8#=#=#?p=l%=8#=#?#?p=`g02LcR<AL<787L;p>0M&0O7=L<8p=Ig00H7R=P;P7P8CZp=320i:;20l78'<p=TB00:;7/<8p=cAL<78p=tP=P7g03S=R>P8CZp=rP=P7g03T>P8CZp=qP=P7g03U8P8CZp=sP=P7g03V6R?P8CZp={g01F@R@00D8p=@P;g01H@RAg01H_RBPBg01I?RCP@P7g01jFRDP8Cog01JFREFpp=Qf4RFPAPBPBPCP:PAPBPBPCP@P;g01QIRGP7CoPEFpP8K0Pp=V1b78,<;p=:f7RHf6RIf5RJ5m=;7FAx=;7=7:8#z'<p=8Am=;7=7:8p=CAx=;7=7:8#zp=5%?8#=p=O%=8#?p>0`%=8#?#=#=p=M%?8#?#=#=p=d%=8#=p>0_AL;789LF:p=1P=P7P>P8H0?p>02%P8,H7p>0G1H;7#F9m=:=7F8p>0Fg01EbRK/G8p=Jg01F^RLP@P3P2Q00g03W6RMg01MnRNPKP:P;P7P8N<08p>0\1H;7#F9x=:=7F8#zp=D%F79x=;=7:8#zp>0@g0261ROP7g020<S01P8CSp=v1H78#Fp>0=AL;789LF:9LIJp=>Am=IJAL:;7=hF857Hp>0CP;PAPBPBPCP@P7PGP8CoPEFpp=}B0g@78p=KAL:;7=hF8p=A%P7,H;#F9m=:=7F8p=BP;PAPBPBPCP@P7g01I_P8CoPEFpp=RA7@78p=41H;7/H8p=WPLPLP@P@P4P2P2P:g03WXP;P7P8N<0Rp=YPLP@P3P2Q00PMPJPFP:P;P7P8N<08p>0XP:PAPBPBPCP;P7P8L0ep=|PLP@P@P@P2P2PJPFP:P;P7P8N<0Rp>0wP@P7PDP8Cop>0sP:PAPBPBPCP;P7PAPBPBPCP8PEFpK0Pp>0rP;PAPBPBPCP7P8K0up=]A7@8Kp>07A7@:;A7@78'np=\A7@F:A7@;7/n8'np=91n78,n;p>0oP@PJPFP:P;P7P8K0Qp=_g00Hl&096R6g03X<p,2rcREP;P7P8H0{P0P91e8F%[7RD/UJPEP7P:PEP7PJP8CNCf3EX>6,06XF9g01KSR2#?S02#?S03#?RM$0AR3$0<R4%?M#aRG$0AS04$0<RP%i2#l#`#`#a#;RQ20d3KR3$0OS05&068&05<R<40MS06,I7S07,I;S08,I:RR53IX2P'0X34,04X44,04X54'0P81e8I1UDHPEP7PJPEP7PHP8CNCf3EX>6,06P0P61e8H%[;f8RD'UPEP;PIPEP;PDP8CNCf3EX>6f:RS?3QRX2P,0PX34,04X44,04X54,04P8f9RT,e8%[F/USPEPFPDPEPFPSP8CNCf3EP11e7S%[Jf;RU'UAkEJTPEPJPUP7CN3Ef>RV?3QRX2P,0PX34,04X44,04X54,04P8f<RW,e:%[D/UVAkEDWPEPDPVPFCN3EP1%[Tf?RX'UPEPTf=RYPEPTPXPJCNCffBS09?3QRX2P,0PX34,04X44,04X54,04P8%[UfARZ'UPEPWf@S0:PEPWQ09PDCNCfP1AkEYZPEPYfCR[PTCNfFS0;?3QRX2P,0PX34,04X44,04X54,04P8AkEX[PEQ0:Q0;PWCNP120JEZfER\9uEZ1gE\PEPZP\PZP\PZP\CTCc3EfJS0<?3QRX2P,0PX34,04X44,04X54,04P720JE[fDR[fHRZ5uE1gEZPEP[PZP[PZP[PZCTCc3EP1fIR]9uE\1gE]B00E\]P\P]P\P]CT3EfNS0=?3QRX2P,0PX34,04X44,04X54,04P8fGS0>fKS0?5uEfLR^,gEB00EZ^PZP^PZP^CT3EP1fMR_,gEPEP]P_P]P_P]P_CTCcfRS0@?3QRX2P,0PX34,04X44,04X54,04P8fOS0A,gEP1P=fPR`g03Y6Ra%~K$06/t<RbCZ&0ZK/I<Rc,r`%aG#a#a#;#~$04/t<Rd,q`%~?$04/t<R?,s`&0UE$04/t<Re,{`'<3EPEP_fQRfP_PfP_PfCTCcfVRg?3QRX2P,0PX34,04X44,04X54,04[P8P=Q0@PaPbCZfSRb/rc1qbd1sb?1{be'<3EP1fTRa/rc1qad1sa?1{ae3EPEPffUS0BPfQ0BPfQ0BCTCcfZRh?3QRX2P,0PX34,04X44,04X54,04[P81rgcfWRi/qd1si?1{ie3EPEPafXREPaPEPaPECTCcfYS0Cg01O1Re$05R?&09eRe&0t@Rd&0q@Rj&0p@RkPk%@QRlPl%i2#l#`#l#a#;Rm#@Rn9QklDV20hkCRoP8P;g01O]Rpg01P=Rq'X20f8;=7pqdB0c@K7H0bRqb7b8b91GQQ?:QmP8b67^Q&0a4RpPh%FQRr1w48RsPpPhPr&0N4RtG8X:4,04P0P4Ppf[S0DPrPsPpQ0DPrPtG8X:4f_S0E?3QRX2P,0PX34,04X44,04X54,04P8Ppf]S0FPrPsPpQ0FPrPtG8P1Ppf^S0GPr1w47RuCCPpQ0GPrPtC5fcS0H?3QRX2P,0PX34,04X44,04X54,04P8Ppf`S0IPr1w4:RvCCPpfaS0JPrPtC5fbS0K%i2#l#`#`#O#;RrP?PePdPjPkPkPl%@rRwAQkwnDVPoPqb7b8b91GQr?:rmP8b63^PpQ0H%FrRrPsPpQ0HPrPtG8X:4,04P0P4PpfdS0LPrPsPpQ0LPrPtG8X:4fhRw?3QRX2P,0PX34,04X44,04X54,04P8PpffS0MPrPsPpQ0MPrPtG8P1PpfgS0NPrPuCCPpQ0NPrPtC5flS0O?3QRX2P,0PX34,04X44,04X54,04P8PpfiRxPrPvCCPpfjS0PPrPtC5fkS0Q%i2#l#`#`$0`#;RrP?PePdPjPkPkPl%@rRyAQkynDVPoPqb7b8b91GQr?:rmP8b63^PpQ0O%FrRrPsPpQ0OPrPtG8X:4,04P0P4PpfmS0RPrPsPpQ0RPrPtG8X:4fqRy?3QRX2P,0PX34,04X44,04X54,04P8PpfoS0SPrPsPpQ0SPrPtG8P1PpfpS0TPrPuCCPpQ0TPrPtC5fuS0U?3QRX2P,0PX34,04X44,04X54,04P8PpfrRzPrPvCCPpfsS0VPrPtC5ftS0W%O2#M#M#d#O#a#;RrP?PePdPjPkPkPl%@rR{AQk{nDVPoPqb7b8b91GQr?:rmP8b63^PpQ0U%FrRrPsPpQ0UPrPtG8X:4,04P0P4PpfvS0XPrPsPpQ0XPrPtG8X:4fzR{?3QRX2P,0PX34,04X44,04X54,04P8PpfxS0YPrPsPpQ0YPrPtG8P1PpfyS0ZPrPuCCPpQ0ZPrPtC5f~S0[?3QRX2P,0PX34,04X44,04X54,04P8Ppf{R|PrPvCCPpf|S0\PrPtC5f}S0]%O2#M#M#d#O#O#;RrP?PePdPjPkPkPl%@rR}AQk}nDVPoPqb7b8b91GQr?:rmP8b63^PpQ0[%FrRrPsPpQ0[PrPtG8X:4,04P0P4Ppp+01@S0^PrPsPpQ0^PrPtG8X:4p+01DS0_?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01BS0`PrPsPpQ0`PrPtG8P1Ppp+01CS0aPrPuCCPpQ0aPrPtC5p+01HS0b?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01ES0cPrPvCCPpp+01FS0dPrPtC5p+01GS0e%O2#M#M#d#i#;RrP?PePdPjPkPkPl%@rR}AQk}nDVPoPqb7b8b91GQr?:rmP8b63^PpQ0b%FrRrPsPpQ0bPrPtG8X:4,04P0P4Ppp+01IS0fPrPsPpQ0fPrPtG8X:4p+01MS0g?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01KS0hPrPsPpQ0hPrPtG8P1Ppp+01LS0iPrPuCCPpQ0iPrPtC5p+01QR}?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01NS0jPrPvCCPpp+01OPrPtC5p+01P%O2#M#M#d#O$0_#;RrP?PePdPjPkPkPl%@rR~AQk~nDVPoPqb7b8b91GQr?:rmP8b63^PpP}%FrRrPsPpP}PrPtG8X:4,04P0P4Ppp+01RR}PrPsPpP}PrPtG8X:4p+01V?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01TR}PrPsPpP}PrPtG8P1Ppp+01UR}PrPuCCPpP}PrPtC5p+01Z?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01WPrPvCCPpp+01XPrPtC5P`Q0>PVPJH0^&094Rr&0L8RvP4PfP4PZP4PXP4PI&054R}D1D137XGP,0PP0PPP4Q0@P4P]P4Q0:P4PHP}D1D197rvXGPp+01_?3QRX2P,0PX34,04X44,04X54,04P8P4PaP4Q0?P4Q09P4PTP}D1D197rvP1P=p+01^RvP>PcH03&0Kc#PR0-02vp+01c?3QRX2P,0PX34,04X44,04X54,04Q0XP=p+01`P>PcH03P1&0IcS09P=p+01aP>&0HcRcCjp+01b0020p+01gS0k?3QRX2P,0PX34,04X44,04X54,04[P8Q09P=p+01dP>PcCjp+01e0020%O2#M#M#d#d#;R>2014cR1+0GQ02#;Rv%;G+0]RG'GRu1681Ppp+01hS0lP>%P7RsAh4c7I0F[^;LRm%J>S0m1<um<0E7PN%2NRm,6N%;2Ru,bKS0n1X@KPmPu1X@uH0\P?PePdPj20D@KR~%@uRn5QkS0oPoPqb7b8b9Q0nP8b6H0[16N1eI0BPpp+01f%PNS0p,H>S0q#FAh4cNCC1H>0/GGS0r%J8Rc?:80Ppp+01iR1P>P7PtDD[^;@S0sQ0mQ0rQ0s'<<0E7PKP?PePdPjPkPkP~P~Q0oDVPoPqb7b8b91GKKS0oQ0n'<P8b6Q0o?:K0eI0BPpQ0k1H>KS0kPtH0@P4p+01lS0n?3QRX2P,0PX34,04X44,04X54P{P4p+01kS0mQ0]Q08'I73QX2P,0PX34,04X44PyP4p+01jS08Q0\Q0VQ07'I'I73QX2P,0PX34PwPPQ06,Ix,Iz,I|931QX2PPUP=Q0lPQQ05&06U<0M<,Iw,Iy,I{R<H03P=Q0lPQ&0K<#PH0?S05&0I<S06P=Q0lPQ&0H<CjS071<OOR<,<ORR,<OR0,<OPOPOQ01Q01CS,v<,vR,v0'vQ06ePrP4Q0EP4PgP4P_P4P[P}D1D1S06P=P1PQP4P|P4PzP4PxP4P3B0>48}D1D1CjXjr%JQS01P4P{P4PyP4PwP4P3Q06D1D1-014-0GQ/GGRrP4P|P4PzP4PxP4P3P4Q0IP4PiP4Q0=P4P\P}D1D1D1D1-014,68S0sPpQ0820=QsS0rP4P4Q0\P4Q0VP4Q0PP4P3P4Q0JP4PEP4Q0AP4Q0;P}F>D1D1P7L0C[^;LR\'<P?PePdPjA}k~lPoPqb7b8b9Q01P8b6S0;PrP\P?PePdPj%;MRM#@R\,Kl%@vS0tQ0460Y@5}kPoPqb7b8b91HQM/GGP8b6S04PreQ0sPL%2mRr#2R1#2R[#2R0#2RR#2R<#2RO,68PpQ0nQ0rP4P4Q0[P4Q0UP4Q0OP4P3P4Q0HP4PhP4PfP4PZP}F>D1D1P7L0C]0P716NOQ0ZPpQ0mPQQ0pP4P4Q0]P4Q0WP4Q0QP4P3P4Q0KP4Q0CP4P`P4Q0>P}F>D1D1PNDAI0FeW0PL%28RN/6OPpp+01nS0>PQ%27RZP4P4p+01AS0pP4fwS0mP4fnS0rP4P3P4feS0uP4f\S0vP4PbP4Q0<P}F>D1D1PZDADB]0P816mOPzPpp+01mPQPmP4P4Q0^P4Q0XP4Q0RP4P3P4Q0LP4Q0DP4Q0@P4P]P}F>D1D1PmDADBeW0PL%2NRN/6OPpp+020S0<PQ%2ZRmP4P4Q0aP4Q0ZP4Q0TP4P3P4Q0NP4Q0GP4Q0BP4P^P}F>D1D1PmDADB]0P816rOQ0QPpp+01oS0wPQPrP4P4Q0`P4Q0YP4Q0SP4P3P4Q0MP4Q0FP4PaP4Q0?P}F>D1D1PrDADBeW0PL%2NRN/6OPpp+022S0?PQ%2mRrP4P4Q0cP4P|P4PzP4P3P4PxP4Q0IP4PiP4Q0=P}F>D1D1PrDADB]0P8161OP?PePdPj%@>/K~%=2R>#;Rd#@R^,Kl5RkPoPqb7b8b9Q0k1HQdRl'4S0=P8b6S0xQ0q/4lP@Q0qPpp+023R]%F8S0q1w43CCXH@PUPlP8J0;b1Ppp+021S0yPQP1P4P4Q0_P4P{P4PyP4P3P4PwP4Q0EP4PgP4P_P}F>D1D1P1DADBeW0PL%2NRN/6OPpp+024S0zPQ%2rR1P4P4Q0eP4Q0]P4Q0WP4P3P4Q0QP4Q0KP4Q0CP4P`P}F>D1D1P1DADB]0P816[OQ0MPpP]PQP[P4P4Q0dP4Q0\P4Q0VP4P3P4Q0PP4Q0JP4PEP4Q0AP}F>D1D1P[DADBeW0PL%2NRN/6OPpp+026R[PQ%21R`P4P4Q0fP4Q0^P4Q0XP4P3P4Q0RP4Q0LP4Q0DP4Q0@P}F>D1D1P`DADB]0P8160OQ0EPpp+025S0@PQP0P4P4Q0bP4Q0[P4Q0UP4P3P4Q0OP4Q0HP4PhP4PfP}F>D1D1P0DADBeW0PL%2NRN/6OPpp+028R0PQ%2`R_P4P4Q0hP4Q0`P4Q0YP4P3P4Q0SP4Q0MP4Q0FP4PaP}F>D1D1P_DADB]0P816ROPEPpp+027S0FPQPRP4P4p+01JP4Q0pP4Q0mP4P3P4Q0rP4Q0uP4Q0vP4PbP}F>D1D1PRDADBeW0PL%2NRN/6OPpp+02:RRPQ%2_RbP4P4Q0gP4Q0_P4P{P4P3P4PyP4PwP4Q0EP4PgP}F>D1D1PbDADB]0P816<OPfPpp+029S0EPQP<P4P4Q0iP4Q0aP4Q0ZP4P3P4Q0TP4Q0NP4Q0GP4Q0BP}F>D1D1P<DADBeW0%2N/6O%2bRN/6OAWsuu?Wuu?Wuu?Wuu/bMS0BPN1H8uX@@R<P<P<P<P<P<P<P<PsO1S0GO1S0NO1S0TO1S0ZO1RgO1REO1RaO1P<PbPaP<P_PEP<P`PgP<P1Q0ZP<PrQ0TP<PmQ0NP<PZQ0GP<P7Ps1X@sCYCYCYCYCYCYCYCYPOPM1X@MRsJ0XP8H0:Q0B&0W;%P;#Jp-0R<P?Pe20V@7RZPjPk20T@2R29}k~Rm&0NBRrPk1K2n/Kn/Kn/Kn/Kn/Kn/Kn/Kn=Qk\PrPkPAPBPBPCP:J0SC|C|PoPqb7b8b9X?@WEAW7uu?Wuu?Wuu?Wuu/bMP:[\c^?@^E<P8Ppp+02>PQ%2F#2#2#2#2#2#2#2Ah4}FDB%PFP7P;O4b6bibBPpp+02;RCPQPNP4P4Q0jP4Q0cP4P|P4P3P4PzP4PxP4Q0IP4PiP}F>D1D1PNDADBeW0X;LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020111100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100P8O1W0X;LCSCSP=Q0lPQP4P{P4PyP4PwP4P3Q06>0>4}D1D1Cje&0LUPSJ0zQ07eCSQ01%POR},HQ/GGRGA:c8}R3PpQ0820=Q7RyPtC5[^;@R{'<Q0;PGP{Q04%J7R{1b7}RG'<A:{7MR=P{PGP{P8X@@RGPMO1RN,b71X<{A7<{{e:0y{{P@P@Q00PGQ001b78$0xXm@X@@P7P71X@7P}PNPGPG%P8,X@X@LPOPMPsJ0wN<08J0vP8H0:P=P?PePZPjPkPkPmPk20s2\H0rPrARk2~ARk2nQ0t9Rk2ARk2^Q03#;R^#@9Rk2Q02#=#;Rn#@9Rk2%?>#;R~#@9Rk2%=>#;R>#@9Rk25]k5]k5]k5]k5]k5]k5]kC|PoPqb7b8b9X?@A:c8M&077147uP7PvP7PdP7P^P7PnP7P~P7P>C\D9D940oRM[^?@P8P:P7O2b6bBPMP5&07;P;PuP;PvP;PdP;P^P;PnP;P~14;>D9D9D9PpQ0nPQP:PtDDP8&07:P@PKPpQ0wPyPtC5^03X;@Q0o?:K}P|PpQ0>PQPKPtDDeW0PFP8P:K0QW1P8O1P:PuP:PvP:PdP:P^P:PnP:P~14:>D9D9D9P514FuPFPvPFPdPFP^PFPnPFP~PFP>C\D9D9PpQ0>PQPJPtDDP814JuPuPpQ0yPyPtC5^03X;@%Ju?:u}Q0WPpQ0<PQPuPtDDeW0PIP8PJE_W1P8O1PJPvPJPdPJP^PJPnPJP~PJP>C\D9D9P514IvPIPdPIP^PIPnPIP~14I>D9D9PpQ0<PQPHPtDDP814HvPvPpP]PyPtC5^03X;@%Jv?:v}Q0RPpQ0?PQPvPtDDeW0PDP8PHE_W1P8O1PHPdPHP^PHPnPHP~14H>D9D9P514DdPDP^PDPnPDP~PDP>C\D9PpQ0?PQPTPtDDP814TdPdPpQ0@PyPtC5^03X;@%Jd?:d}Q0xQ0=P@Q0kPpP[Q0qPtC5XH@PYPlP8J0;b1PpQ0zPlPtH0@eW0PSP8PTE_W1P8O1PTP^PTPnPTP~PTP>C\D9P514S^PSPnPSP~14S>D9PpQ0zPQPUPtDDP814U^P^PpQ0FPyPtC5^03X;@%J^?:^}PwPpP[PQP^PtDDeW0PWP8PUE_W1P8O1PUPnPUP~14U>D9P514WnPWP~PWP>C\PpP[PQPYPtDDP814YnPnPpQ0EPyPtC5^03X;@%Jn?:n}Q0JPpP0PQPnPtDDeW0PVP8PYE_W1P8O1PYP~PYP>C\P514V~14V>PpP0PQPXPtDDP814X~P~PpPCPyPtC5^03X;@Ry%J~?:~}PhPpPRPQP~PtDDeW0Q0:P8PXE_W1P8O114X>P>Py%J>?:>}PfPpPRPQP>PtDDeW0Q0:P8PXE_W1P8O1n200100000021000010000W1P8O1n200100000021000011000W1P8O1n200100000021000011000W1P8O1n200100000021100011000W1P8O1n200100000021000011000W1P8O1n200100000021000011000W1P8O1n200100000021000011000bIX03X;@CSCSQ05eCSCyCyCyCyb[bSWOWNWAP7P8O2n2001000000121000000W1P7P8O2n2001000000121000000WJX2PP7P8O2n2001000000121101000b<W_WWP7P8O2n2001000000121000000W1Xh4P7P8O2n2001000000121101000b<W^WVP7P8O2n2001000000121000000W1Xg4P7P8O2n2001000000121101000b<W]WUP7P8O2n2001000000121000000W1Xf4P7P8O2n2001000000121101000b<W\WTP7P8O2n2001000000121000000W1Xe4P7P8O2n2001000000121101000b<WZWRP7P8O2n2001000000121000000W1Xd4P7P8O2n2001000000121101000b<WYWQP7P8O2n2001000000121000000W1Xc4P7P8O2n2001000000121101000b<WXWPP7P8O2n2001000000121000000W1Xb4P7P8O2n2001000000121101000b<WaW`WMP7P8O2n2001000000121000000W1WDP7P8O2n2001000000121000000W1P7P8O2n2001000000121000000W1WCP7P8O2n2001000000121000000W1WAP7P8O2n2001000000121000000WDWLP7P8O2n2001000000121000000W1WCP7P8O2n2001000000121000000W1WAP7P8O2n2001000000121000000W1X>6P7P8O2n2001000000121101000W1XF9P7P8O2n2001000000121101000W1WkWKWlo"). Qed.

(* [comment removed for export] *)
Lemma RHEAP_need_locks : forall s LB m, RHEAP s LB m -> rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h01Hh13LB0h22_Hh33_H0h43_H1h52sth62LBh74MREPh82NLh93_H2h:3_H3h;1mh<1si001xp;1p;4p;2p;3p;5g00O5j1[Tg02Chj4ZTg03@<j15Tg01SMR0j2HTg00K_j1?Tg00LDj1LTg00POj2KTg02b\j1JTg00ecj1UTg03A2j3>Tg03Amj2ITg03Bnj3CTg03Cmj28Tg03E0j3GTg02;?j1FTg02f;j1PTg02K3j46Tg03F1j1OTg00`Wj1NTg02<7j1ETg03Fij1MTg00=oR1j27Tg03Kgj3QTg03LRj1RTg00Fhj3STg03MGj1TTg03N>j5YTg00XSj3XTg03O>j2WTg03P@j2VTg02MXR2f1R3f0R43Qp=;g03QBR5%R47S3p=3f3R6g03R;f2R7%T3P4DYp=2A>673/74p=:1734,77p=0%?4#?p==g02LcR8?X34p=<g00H7R9P3g03Z2P4C6p=11W671V34'7p=4AG673/74p=9P9P3g03S=P4C6p=AP9P3g03T>P4C6p=BP9P3g03U8P4C6p=@P9P3g03V6R:P4C6p=Dg00Hl%[2R2g03X<p,2rcR;P7P3P4CZP0P5f4R<,;4%53R=f5R>'3P;P3P6P;P3P>P4C2C:30X12,H2X55g01KS#?#=R?#Lg01EbR@'K#J%U8R8'<RA,17P4f6RB,;4f7RC,3=P;P3P>P;P3PCP4C2C:30X12,H2P0P21;4C%57f8RC'3P;P7PBP;P7PCP4C2C:30X1211BAP4f9RB,;4%5<f:R0'3P;P<PCP;P<P0P4C2C:30P11;30%5>f;R='3A>;>BP;P>P=P3C230110AP4f<R0,;6%5Cf>R6'3A>;C0P;PCP6P<C230P1%5Bf?R<'3P;PBf=RDP;PBP<P>C2C:116AP4%5=fAR='3P;P0f@R6P;P0fBR>PCC2C:P1A>;D=P;PDfCRDPBC211>AP4A>;<DP;P6fFR6P0C2P11I;=fER09C;=18;0P;P=P0P=P0P=P0C4C930116AP31I;DfDRDfHR65C;18;6P;PDP6PDP6PDP6C4C930P1fIRD9C;018;DAG;0DP0PDP0PDC430fJ/1AP4fGfK5C;fLR0,8;AG;60P6P0P6P0C430P1fMR0,8;P;PDP0PDP0PDP0C4C9fN/1AP4fO,8;P1P9fPRDg03Y6R6%F@#P/<8R=C6%O@#J/<8R@,AD%??#=#=#=#=#N#F#E/<8R?,BD%F:#E/<8R:,@D%M;#E/<8R8,DD'730P;P0fQRDP0PDP0PDC4C9fRR0/1A[P4P9P0P6P=C6fSR=/A@1B=?1@=:1D=8'730P1fTR1/A@1B1?1@1:1D1830P;PDfUR=PDP=PDP=C4C9fVR=/1A[P41A=@fWR=/B?1@=:1D=830P;P1fXR;P1P;P1P;C4C9P7fY/1AeW:W9W8P3P4O2n2001000000120000000W0W4P3P4O2n2001000000121000000W0P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W4W7P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0X12P3P4O2n2001000000121100000W0X55P3P4O2n2001000000121100000W0W;W6W<o"). Qed.

(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
