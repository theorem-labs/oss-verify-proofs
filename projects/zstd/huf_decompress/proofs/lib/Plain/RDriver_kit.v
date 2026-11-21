(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (implM_of_enode, stack_pieces, argv_cstring and 3 more); stack_pieces, argv_cstring restated for the revision's model; the launch values and the entry stack layout; stack_pieces, argv_cstring are zstd/simple_decompress's proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_syscalls StdioFiles Startup F_atexit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RDriver_kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2eq00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib7InitMem9raw_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib7InitMem7pad_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib3Lib7InitMem9rnd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib7InitMemDbuild_stack_bytes_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib7InitMem:auxv_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9argv_ptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9envp_ptrsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC59OSSVerify5KrLib3Lib3Arr8u64s_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib3Lib7InitMem>raw_len_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;struct_sizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib7InitMemFflatten_strings_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib7InitMem4envcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib7InitMem8str_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8env_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8rnd_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8str_ptrsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib7InitMem?str_ptrs_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic5proj2C46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib7InitMem<str_ptrs_nthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3oppC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib7InitMemHbuild_stack_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem7raw_lenC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib6Common8DrvAgree8ceil8_leC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List=nth_error_mapC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C59OSSVerify5KrLib3Lib7InitMem>bytes_at_sliceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic5False00c59OSSVerify5KrLib5Plain;RDriver_kit<stack_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common;Startup_kit9auxv_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RMalloc_ifaceP@RHEAP_init_proofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5Plain7Startup<pcrt_writtenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree:rauxv_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;draw_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;draw_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rnd_bytes_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RAUXV_CELLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain;RDriver_kit9heap_initC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z3injC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_image0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain7RunDraw:PSTAGE_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain7RunDraw<PSTAGE_LEN_ZC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib5Plain;RDriver_kit?atx_state0_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_iface6PEMPTYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrK46Stdlib9micromega7EnvRing3Pol03I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain;RDriver_kit>libc_head_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain;RDriver_kit<le4_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocHINV9HINV_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_atexit;PNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation pph := PImg.p_phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl psegs (at_node psegs) (enode n pl) (epost P) ms ->
  implM psegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
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
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis IMG : bytes_at psegs m usp IMGB.
  Hypothesis PADOK : (usp + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.

  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc argv + envc envp + 3))
      (u64s (auxv_words L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) uid L_GID hw sp L_TOP argv envp L_EXECFN)) /\
    bytes_at psegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) /\
    bytes_at psegs m (env_base L_TOP argv envp L_EXECFN) (flatten_strings envp) /\
    bytes_at psegs m (rnd_addr sp (la_rseq L_LA) argv envp) (rnd_bytes draw).
  Proof.
    destruct (InitMem.stack_pieces psegs m L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw IMG PADOK)
      as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
    (* InitMem's order: ..., random bytes, argv strings, envp strings; [repeat split] would open bytes_at *)
    exact (conj B0 (conj B1 (conj B2 (conj B3 (conj B5 (conj B6 B4)))))).
  Qed.

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs L_TOP argv envp L_EXECFN) i = Some (Z_to_bv 64 p) /\ str_base L_TOP argv envp L_EXECFN <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length IMGB) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base L_TOP argv envp L_EXECFN) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (build_stack_bytes_length_top L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw PADOK) as BL.
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
    pose proof (bytes_at_slice psegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base L_TOP argv envp L_EXECFN + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice psegs m usp IMGB (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app psegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section CANSEC2. Context {rc : runConstT}.
Section InitFacts.
  Context {lx : launchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x26000 <= bv_unsigned a < 0x59000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0x57ac0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0x57ac8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0x264b0 [C8 (Z_to_bv 64 0x57aa0)].
  Hypothesis GUARD : rw_cells psegs m 0x57aa0 [C8 CAN].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMG : bytes_at psegs m usp0 (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis SPLO : sp_window_lo <= usp0.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.   (* [comment removed for export] *)
  Hypothesis HATOP : ATOP = usp0 - 8388608.
  Hypothesis PADOK : (usp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.
  Hypothesis TOPHI : (bv_unsigned L_TOP <= 0x800000000000)%Z.

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs) ATOP) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
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
    exists (auxv_addr sp0 argv envp), (rnd_addr sp0 (la_rseq L_LA) argv envp), L_LA, (Z_to_bv 64 (Z.of_N p_init_pc)),
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
    exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold PREAD_STAGE.
    assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (InitMem.rw_cells_image0 psegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
    - vm_compute. reflexivity.
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_state0_init : atx_state false m.
Proof.
    unfold atx_state, atx_cells, PATX, PAEF_INCB. cbn [Z.add].
    pimg_chunk0 NONE m 0x57878 [C1 (Z_to_bv 8 0)] X1.
    pimg_chunk0 NONE m 0x5787c [C4 (Z_to_bv 64 0)] X2.
    pimg_chunk0 NONE m 0x57880 [C4 (Z_to_bv 64 0)] X3.
    pimg_chunk0 NONE m 0x57888 [C8 (Z_to_bv 64 0)] X4.
    pimg_chunk0 NONE m 0x57890 [C8 (Z_to_bv 64 0)] X5.
    pimg_chunk0 NONE m 0x57898 [C8 (Z_to_bv 64 0)] X6.
    pimg_chunk0 NONE m 0x57998 [C8 (Z_to_bv 64 0)] X7.
    pimg_chunk0 NONE m 0x37734 [C1 (Z_to_bv 8 0)] X8.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rstatx0_init : rw_cells psegs m 0x274c8 [C8 (Z_to_bv 64 0x274c8)] /\ (exists reg : bool, atx_state reg m).
Proof.
    pimg_chunk0 NONE m 0x274c8 [C8 (Z_to_bv 64 0x274c8)] D1.
    split; [exact D1| exists false; apply atx_state0_init].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_cells0_init : trun_cells0 m.
Proof.
    unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, wz.
    pimg_chunk0 NONE m 0x37730 [C1 (Z_to_bv 8 0)] H1.
    pimg_chunk0 NONE m 0x26478 [C8 (Z_to_bv 64 0)] H2.
    pimg_chunk0 NONE m 0x26470 [C8 (Z_to_bv 64 0x26420)] H7.
    pimg_chunk0 NONE m 0x26420 [C8 (Z_to_bv 64 0x274f0)] H8.
    pose proof atx_state0_init as AX0.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma empty_cells_init : rw_cells psegs m PEMPTY [CB 16 (repeat (Z_to_bv 8 0) 16)].
Proof. unfold PEMPTY. pimg_chunk0 NONE m 0x37740 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stderr_file0_init : stderr_file0 m.
Proof.
    unfold stderr_file0, file_cells, wz.
    pimg_chunk0 NONE m 0x274f0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1fe38 0x57f00 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
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
Lemma libc_head_byte : forall (m : mem) (a : Z), 0x57ac0 <= a < 0x57ac8 ->
  exists b : byte, mrd psegs m (wa a) = Some b /\ wview psegs m (wa a) <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h02b0h11Hh22Hah31bi001bh41Eh51oi011oh64__x1h71ah82H0h93IMGh:2SRh;2WVh<7__arithh=4__ffh>8__varmaph?5__with@1ehA1mhB1xi021xi033segp;1p;2p;4p;7p;8p;3p;6g00K_j16Tg00LDj1RTg00NRj1QTg00:lR0j1{Tg00`Wj1;Tg00ecj1bTg00O5j1`Tg01@gj2]Tg012dj1\Tg013Bj1zTg013mj2sTg01=hj4NTg01E>j7mTg00>lj1UTg01D6j8dTg0153j2cTg00@Fj2GTg015Uj2aTg00Fhj30Tg016Aj3_Tg016`j4^Tg036`j11Tg00>Jj2ETg01SMR1j29Tg02aFj2yTg02b9j3xTg00UHj6[Tg037Oj2rTg008Ij6Ij7vTg00Lbj2HTg037nj3XTg0392j1pTg03:4j1oTg03;3j1lTg02?bj1kTg01ZWj2VTg03<1j1TTg03<Oj2PTg01[Uj1JTg00g8j15Tg01=2j2jTg00a5j2iTg00=oR2j2LTg014Pj2nTg01Bij7YTg01>Sj7gTg01=NR3j2OTg03=Vj2qTg03>Oj3ZTg00@`j4tTg01ilj4uTg03?Lj3wTf0R4#6#6p=@%64#5#6#5#5#5#5#6#5#6#5#5#6#6p=>%54#6p=Kf3R5f2R6'jf1R7/i4'Lp==g01F@R8/n4p=?P7g01H@R9g01H_R:P:g01I?R;P4g01JFR<FYp=WP6P9P:P:P;P8P7g01I_P4CNP<FYp=A%64#5p=M%54#5p=h%64#5#6#5p=f%64#5#5#5p=eP6P9P:P:P;P7P4Fgp=DA0856A0874'Op=Cf4R<=085A0867/O4'Op=3A0874p=2g00H7R=/q4p=4f6R>f5R?;0<AZ=67=054#J'Lp=7AZ=67=054#Jp=8A0567/L4p=<P>P?P<P5P6P7P4CtCup=:P8P?P<P5P6P7P4Fvp=BAw=74p=FA0674#Jp=Sg01KSR@#6#@RA#6#@#RRB#QRC%RARA#QRD#{RE[%>@#@#@#;RFP4P4%>@#K#@#;RGC=RHg01O1RI#b%`I1]87%\8%z8RIP9P:P:P;PIP9P:P:P;P8%?FR9g01QI1s8@RJCN,WIP8PJg01jF%?GCN,WIFm%U:AAIJ9%>@#@#M#;R9#?9AIJ%>@#@#K#;R:#?9AIJ%>@#@#h#;RK#?9AIJ%>@#M#@#;RL#?9AIJ%>@#f#;RM#?9AIJ%>@#M#K#;RN#?9AIJ%>@#e#;RO#?9AIJ5DI5DI5DI5DI5DI5DI5DIGd1cI;P4P6g01O]RIg01P=R;'G1a46=0I;dg01EbR;=_87C^b=b>b?X68P7PFP7P9P7P:P7PKP7PLP7PMP7PNP7POCCD3D3D3RJ\H^68P4P6P7O2b<PJP3126FP6P9P6P:P6PKP6PLP6PMP6PN126OD3D3D3PE%1<RJ#41ED4RPPE%UDRQVCRCPJPQF7X0D,9DP4125FPFPE%16RR#4PPPEPCPRPQF7X0D,9DRR^2HX78RHPFPFPFPGC=PDPE%1FRS#4RTPPPEPCPSPQC8RSC<X0D1yA;9xA;R;1ED;RA90ETRTPS1GEARUPTdA0EAQPEPAP0PDp-0P4g0261g01n\RTn10110100021000000X@ERVg020<RWPQP4E[PT1rT4RXb1WBRYPSdF:W2P<P4P5EBW1P4O1P5P9P5P:P5PKP5PLP5PMP5PN125OD3D3D3P312<9P<P:P<PKP<PLP<PMP<PNP<POCCD3D3PE%1>RS#4RZPPPEPCPSPQC8RSC<X0D,9DP412?9P9PHPFP9P9PGC=PDPE%19R9#4R[PPPEPCP9PQC8R9C<X0DP;A0E[AR[P9PUP[dPYP9dF:W2P>P4P?EBW1P4O1P?P:P?PKP?PLP?PMP?PNP?POCCD3D3P312>:P>PKP>PLP>PMP>PN12>OD3D3PEf8R>#1R9#4R[PPPEPCP9PQF7X0D,9DP4f7R\/2:P:PHPFP:P:PGC=PDPE%1:R:#4R]PPPEPCP:PQC8R:C<X0DP;A0E]AR]P:PUP]dPYP:dF:W2P>P4P\EBW1P4O1P\PKP\PLP\PMP\PN12\OD3D3P312>KP>PLP>PMP>PNP>POCCD3PEf:R\#1R:#4PPPEPCP:PQF7X0D,9DP4f9R]/2KPKPHPFPKPKPGC=PDPE%1KRK#4R^PPPEPCPKPQC8RKC<X0DP;A0E^AR^PKPUP^dPYPKdF:W2P\P4P]EBW1P4O1P]PLP]PMP]PNP]POCCD3P312\LP\PMP\PN12\OD3PEf<R\#1RK#4PPPEPCPKPQF7X0D,9DP4f;R^/2LPLPHPFPLPLPGC=PDPE%1LRL#4R_PPPEPCPLPQC8RLC<X0DP;A0E_AR_PLPUP_dPYPLdF:W2P\P4P^EBW1P4O1P^PMP^PN12^OD3P312\MP\PNP\POCCPEf>RL#1R_#4R`PPPEPCP_PQF7X0D,9DP4f=Ra/2MPMPHPFPMPMPGC=PDPE%1MRM#4RbPPPEPCPMPQC8RMC<X0DP;A0EbARbPMPUPbdPYPMdF:W2PLP4PaEBW1P4O1PaPNPaPOCCP312LN12LOPEf@R3#1RM#4RbPPPEPCPMPQF7X0D,9DP4f?Rc/2NPNPHPFPNPNPGC=PDPE%1NRN#4RdPPPEPCPNPQC8RNC<X0DP;A0EdARdPNPUPddPYPNdF:W2P3P4PcEBW1P4O112cOPOPHPFPOPOPGC=PDPE%1ORO#4RGPPPEPCPOPQC8ROC<X0DP;A0EGARGPOPUPGdPYPOdF:W2P3P4PcEBW1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n200100000021100011000W1P4O1n201100000021100011000b4PRP1PDPE%15R1#4PPPEPCP1PQF7X0DPE1F?JPPPEP?PJPQF7X3D,9DP4PE%1?R?#4PPPEPCP?PQF7P21ED7R290EZPSPE1F]9PPPEP]P9PQF7X3D,9DP41ED590E[PEPC%1]PQC8P^P:O1PE1GE4P\%1^O1=0E4P0PDPL%1aR^O1R\=0E4PE%1cR:,F3RCPPPEP3P:PQC8R[C<X3D,9D]4P7PcP_O1=0EPPDPEfAR9/FMPPPEP9PMPQF7X3DP7A0EC2RCP[PEP2P0PDPEP4PPPbn101102000210100001ED6R650EX5E1GE2P3P:O1R3P4EIPCePEP2P0PDPEP4PPP0g01LoRCPE1HBM%;@R@5X=PIPE%p4RM%o4Rb%19,HB%l4#kR9'V#T'PPQn0100000020000PQn10110200021010300n10110200021010000=SEQX5EA0E2QR2PEP6PVPWPQP4E[PTPXb8W1%J2eP3P4EIP[eF:W4X3DP4O1PaPKO1=0EQPDPE1Fc_PPPEPcP_PQF7X3DP>1FL^1ED>50ER>PEPLP^PQC8R^PEPQP0PDPEP4PPP`n101102000210100001ED]50EX5EP<P\P4EIP>ePEPQP0PDPEP4PPP0PCPE1HB_=X=@PIPEPM1HB:/V9#T,PbPQn0100000020000PQn10110200021010300n10110200021010000=SEQX5EP5P\P4EIP^eF:W4n10110100021110001P4O1b4b5W;W:P7P4O2n2001000000121000000W1X0DP7P4O2n2001000000121102000b9W2X78WAo"). Qed.

Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells psegs m 0x57ac0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h02Hih11Hh23tm1h33sech43thrh53cdth67__arithh74__ffh88__varmaph95__with:1bh;1ih<1eh=1ni001nh>3LB0h?4__x1h@1xi011xhA2_HhB3Hi0hC3_H0hD3_H1hE4__p1hF2sthG1whH1zhI1EhJ3HtmhK2LBhL4MREPhM2NLhN3NLBhO3NLWhP2R0hQ2R1hR2R2hS2R3hT2R4hU2R5hV2R6hW2R7hX2W0hY2W1hZ2W2h[2W3h\2W4h]2W5h^2W6h_2W7h`3_H2ha3_H3hb2b0hc2b1hd2b2he2b4hf2b5hg2b6hh2b7hi4cstrhj1lhk1mhl1shm1yp%0p&0p;1p;4p;2p;3p;5p;6p;<p;7p;8g00O5k106Tg02Chk40yTg03@<j1ZTg01SMR0j20Tg00K_j1>Tg00LDk10<Tg00NRk109Tg00`Wj1<Tg00POk20kTg02b\k10NTg02f;k102Tg00eck101Tg03A2j3hTg03Amk20HTg03Bnj3pTg03Cmj2aTg03E0j3zTg02;?j1yTg02K3j4\Tg03F1k10YTg02<7j1xTg03Fik10WTg00=oR1j2=Tg012Fk10xTg012dk10uTg013Bk10qTg0153k20hTg00@Fj2UTg015Uk20gTg00Fhj37Tg016Ak30cTg016`k40bTg01=2j2HTg03G^j3^Tg00:lk10aTg036`j1GTg00>Jj2qTg00>lk10JTg03Hck40^Tg02n[k10ITg03Ifj4~Tg02eBk10GTg00c8R2j1OTg02cQk10FTg02dHk10ETg00cXj4gTg00bXj2|Tg029Fk20\Tg03J]R3j26Tg01Sgj3fTg018=k30Bk50@Tg00jHR4j12Tg00a5S00j2[Tg014Pk20ATg017Rk40ZTg00eFj2ETg03K5k40=Tg00@`j4YTg00Sfk30;Tg02Imk30XTg00g8j1;Tg00UHk608Tg01eWk407Tg011ak10UTg01@gk20STg013mk20RTg01DZk60QTg008Ik60Pk70MTg02Z6k30TTg010`k10wTg01@Bm<05Tg02Z\k60tTg01ilj4rTg03Kgk30oTg03LRk10nTg03MGk10mTg03N>k50lTg00XSj3LTg03O>k20jTg03P@k20iTg01=hj4kTg01Bij7jTg01E>k70LTg03?Lj3iTg03>Oj3sTg01[Uj1uTg01Ack30fTg01?]m<0OTg01D6k80eTg01>Sk70dTg01=NR5j2eTg02MXR6f1R7f0R840op=cg03QBR9&0n8777p=Tf3R:g03R;f2R;&0m7P8I0lp=NAh:;7/=8p=b1=78,=;p=F%>8#>p=M%>8#;#>#;#;#;#;#>#;#>#;#;#>#>p=Pg02LcR<AL<787L;p>0K&0N7=L<8p=Ig00H7R=P;P7P8C\p=320j:;20i78'=p=SAz:;7/=8p=dAL<78p=oP=P7g03S=R>P8C\p=tP=P7g03T>P8C\p=mP=P7g03U8P8C\p=vP=P7g03V6R?P8C\p=lg01F@R@00A8p=@%;8#>p>03P;g01H@RAg01H_RBPBg01I?RCP@P7g01jFRDP8Ckg01JFREFjp=Rf4RFPAPBPBPCP:PAPBPBPCP@P;g01QIRGP7CkPEFjP8K0Lp=V1[78,=;p=9f7RHf6RIf5RJ5i=;7FAs=;7=7:8#u'=p=8Ai=;7=7:8p=AAs=;7=7:8#up=4%>8#;p>00%>8#;#>#;p>0`%>8#;#;#;p>0_AL;789LF:p=1P=P7P>P8H0=p=}%;8#;p>0]%O8,E7p>0D1E;7#G9i=:=7F8p>0Cg01EbRK/H8p=Jg01F^RLP@P3P2Q00g03W6RMg01MnRNPKP:P;P7P8N<05p>0[1E;7#G9s=:=7F8#up=D%G79s=;=7:8#up>0>g0261ROP7g020<S01P8CYp=n1E78#Gp>0?AL;789LF:9LIJp=?Ai=IJAL:;7=fF857Hp>0:P;PAPBPBPCP@P7PGP8CkPEFjp={B0f@78p=KAL:;7=fF8p=B%O7,E;#G9i=:=7F8p=CP;PAPBPBPCP@P7g01I_P8CkPEFjp=QA7@78p=51E;7/E8p=XPLPLP@P@P4P2P2P:g03WXP;P7P8N<0Op=WPLP@P3P2Q00PMPJPFP:P;P7P8N<05p>0VP:PAPBPBPCP;P7P8L0ep=wPLP@P@P@P2P2PJPFP:P;P7P8N<0Op>0vP@P7PDP8Ckp>0sP:PAPBPBPCP;P7PAPBPBPCP8PEFjK0Lp>0rP;PAPBPBPCP7P8K0dp=]A7@8Kp>04A7@:;A7@78'ep=`A7@F:A7@;7/e8'ep=:1e78,e;p>0pP@PJPFP:P;P7P8K0Mp=_g00Hl&066R6g03X<p,2rcREP;P7P8H0yP0P91c8F%Z7RD/TJPEP7P:PEP7PJP8CNCb3FX>6,06XF9g01KSR2#>S02#>S03#>RM$0<R3$09R4%>M#MRG$0<S04$09RP%P2#M#M#<RQ20k3KR3$0NS05&028&01<R<40KS06,I7S07,I;S08,I:RR53IX2P'0X34,04X44,04X54'0P81c8I1TDHPEP7PJPEP7PHP8CNCb3FX>6,06P0P61c8H%Z;f8RD'TPEP;PIPEP;PDP8CNCb3FX>6f:RS?3QRX2P,0PX34,04X44,04X54,04P8f9RT,c8%ZF/TSPEPFPDPEPFPSP8CNCb3FP11c7S%ZJf;RU'TAhEJTPEPJPUP7CN3Ff>RV?3QRX2P,0PX34,04X44,04X54,04P8f<RW,c:%ZD/TVAhEDWPEPDPVPFCN3FP1%ZTf?RX'TPEPTf=RYPEPTPXPJCNCbfBS09?3QRX2P,0PX34,04X44,04X54,04P8%ZUfARZ'TPEPWf@S0:PEPWQ09PDCNCbP1AhEYZPEPYfCR[PTCNfFS0;?3QRX2P,0PX34,04X44,04X54,04P8AhEX[PEQ0:Q0;PWCNP120HEZfER\9pEZ1aE\PEPZP\PZP\PZP\CSCd3FfJS0<?3QRX2P,0PX34,04X44,04X54,04P720HE[fDR[fHRZ5pE1aEZPEP[PZP[PZP[PZCSCd3FP1fIR]9pE\1aE]AzE\]P\P]P\P]CS3FfNS0=?3QRX2P,0PX34,04X44,04X54,04P8fGS0>fKS0?5pEfLR^,aEAzEZ^PZP^PZP^CS3FP1fMR_,aEPEP]P_P]P_P]P_CSCdfRS0@?3QRX2P,0PX34,04X44,04X54,04P8fOS0A,aEP1P=fPR`g03Y6Ra%yK$02/o<RbC\&0YK/I<Rc,t`%MG#M#M#<#y#x/o<Rd,m`%y?#x/o<R?,v`&0WE#x/o<Re,l`'=3FPEP_fQRfP_PfP_PfCSCdfVRg?3QRX2P,0PX34,04X44,04X54,04[P8P=Q0@PaPbC\fSRb/tc1mbd1vb?1lbe'=3FP1fTRa/tc1mad1va?1lae3FPEPffUS0BPfQ0BPfQ0BCSCdfZRh?3QRX2P,0PX34,04X44,04X54,04[P81tgcfWRi/md1vi?1lie3FPEPafXREPaPEPaPECSCdfYS0Cg01O1Re$01R?&06eRe&0x@Rd&0u@Rj&0q@RkPk%@QRlPl%P2$03#M#<Rm#@Rn9RklDV20hkCRoP8P;g01O]Rpg01P=Rq'U20g8;=7pqdB0c@K7H0bRqb7b8b91HQQ?9QmP8b67^Q&0a4RpPh%GQRr1q48RsPpPhPr&0J4RtG8X:4,04P0P4Ppf[S0DPrPsPpQ0DPrPtG8X:4f_S0E?3QRX2P,0PX34,04X44,04X54,04P8Ppf]S0FPrPsPpQ0FPrPtG8P1Ppf^S0GPr1q47RuCAPpQ0GPrPtC4fcS0H?3QRX2P,0PX34,04X44,04X54,04P8Ppf`S0IPr1q4:RvCAPpfaS0JPrPtC4fbS0K%P2#M$00#<RrP?PePdPjPkPkPl%@rRwARkwnDVPoPqb7b8b91HQr?9rmP8b63^PpQ0H%GrRrPsPpQ0HPrPtG8X:4,04P0P4PpfdS0LPrPsPpQ0LPrPtG8X:4fhRw?3QRX2P,0PX34,04X44,04X54,04P8PpffS0MPrPsPpQ0MPrPtG8P1PpfgS0NPrPuCAPpQ0NPrPtC4flS0O?3QRX2P,0PX34,04X44,04X54,04P8PpfiRxPrPvCAPpfjS0PPrPtC4fkS0Q%P2#M$03#<RrP?PePdPjPkPkPl%@rRyARkynDVPoPqb7b8b91HQr?9rmP8b63^PpQ0O%GrRrPsPpQ0OPrPtG8X:4,04P0P4PpfmS0RPrPsPpQ0RPrPtG8X:4fqRy?3QRX2P,0PX34,04X44,04X54,04P8PpfoS0SPrPsPpQ0SPrPtG8P1PpfpS0TPrPuCAPpQ0TPrPtC4fuS0U?3QRX2P,0PX34,04X44,04X54,04P8PpfrRzPrPvCAPpfsS0VPrPtC4ftS0W%P2$00#M#<RrP?PePdPjPkPkPl%@rR{ARk{nDVPoPqb7b8b91HQr?9rmP8b63^PpQ0U%GrRrPsPpQ0UPrPtG8X:4,04P0P4PpfvS0XPrPsPpQ0XPrPtG8X:4fzR{?3QRX2P,0PX34,04X44,04X54,04P8PpfxS0YPrPsPpQ0YPrPtG8P1PpfyS0ZPrPuCAPpQ0ZPrPtC4f~S0[?3QRX2P,0PX34,04X44,04X54,04P8Ppf{R|PrPvCAPpf|S0\PrPtC4f}S0]%P2$0`#<RrP?PePdPjPkPkPl%@rR}ARk}nDVPoPqb7b8b91HQr?9rmP8b63^PpQ0[%GrRrPsPpQ0[PrPtG8X:4,04P0P4Ppp+01@S0^PrPsPpQ0^PrPtG8X:4p+01DS0_?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01BS0`PrPsPpQ0`PrPtG8P1Ppp+01CS0aPrPuCAPpQ0aPrPtC4p+01HS0b?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01ES0cPrPvCAPpp+01FS0dPrPtC4p+01GS0e%P2$00$03#<RrP?PePdPjPkPkPl%@rR}ARk}nDVPoPqb7b8b91HQr?9rmP8b63^PpQ0b%GrRrPsPpQ0bPrPtG8X:4,04P0P4Ppp+01IS0fPrPsPpQ0fPrPtG8X:4p+01MS0g?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01KS0hPrPsPpQ0hPrPtG8P1Ppp+01LS0iPrPuCAPpQ0iPrPtC4p+01QR}?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01NS0jPrPvCAPpp+01OPrPtC4p+01P%P2$0_#<RrP?PePdPjPkPkPl%@rR~ARk~nDVPoPqb7b8b91HQr?9rmP8b63^PpP}%GrRrPsPpP}PrPtG8X:4,04P0P4Ppp+01RR}PrPsPpP}PrPtG8X:4p+01V?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01TR}PrPsPpP}PrPtG8P1Ppp+01UR}PrPuCAPpP}PrPtC4p+01Z?3QRX2P,0PX34,04X44,04X54,04P8Ppp+01WPrPvCAPpp+01XPrPtC4P`Q0>PVPJH0^&064Rr&0I8RvP4PfP4PZP4PXP4PI&014R}D1D137XGP,0PP0PPP4Q0@P4P]P4Q0:P4PHP}D1D197rvXGPp+01_?3QRX2P,0PX34,04X44,04X54,04P8P4PaP4Q0?P4Q09P4PTP}D1D197rvP1P=p+01^RvP>PcC~&0Gc#OR0,}vp+01c?3QRX2P,0PX34,04X44,04X54,04Q0XP=p+01`P>PcC~P1&0FcS09P=p+01aP>&0EcRcCgp+01b/}0p+01gS0k?3QRX2P,0PX34,04X44,04X54,04[P8Q09P=p+01dP>PcCgp+01e/}0%P2#M$0]#<R>1|4cR1+0DQ02#<Rv%<G+0\RG'HRu1681Ppp+01hS0lP>%O7RsAf4c7I0C[^;LRm%J>S0m1=um<0B7PN%2NRm,6N%<2Ru,[KS0n1U@KPmPu1U@uH0[P?PePdPj20A@KR~%@uRn5RkS0oPoPqb7b8b9Q0nP8b6H0Z16N1eI0@Ppp+01f%ONS0p,E>S0q#GAf4cNCA1E>0/HGS0r%J8Rc?980Ppp+01iR1P>P7PtDD[^;@S0sQ0mQ0rQ0s'=<0B7PKP?PePdPjPkPkP~P~Q0oDVPoPqb7b8b91HKKS0oQ0n'=P8b6Q0o?9K0eI0@PpQ0k1E>KS0kPtH0>P4p+01lS0n?3QRX2P,0PX34,04X44,04X54P{P4p+01kS0mQ0]Q08'I73QX2P,0PX34,04X44PyP4p+01jS08Q0\Q0VQ07'I'I73QX2P,0PX34PwPPQ06,Ix,Iz,I|931QX2PPUP=Q0lPQQ05&02U<0K<,Iw,Iy,I{R<C~P=Q0lPQ&0G<#OH0=S05&0F<S06P=Q0lPQ&0E<CgS071=OOR<,=ORR,=OR0,=OPOPOQ01Q01CY,n<,nR,n0'nQ06ePrP4Q0EP4PgP4P_P4P[P}D1D1S06P=P1PQP4P|P4PzP4PxP4P3B0;48}D1D1CgXjr%JQS01P4P{P4PyP4PwP4P3Q06D1D1,|4-0DQ/HGRrP4P|P4PzP4PxP4P3P4Q0IP4PiP4Q0=P4P\P}D1D1D1D1,|4,68S0sPpQ0820?QsS0rP4P4Q0\P4Q0VP4Q0PP4P3P4Q0JP4PEP4Q0AP4Q0;P}F?D1D1P7L0:[^;LR\'=P?PePdPjA{k~lPoPqb7b8b9Q01P8b6S0;PrP\P?PePdPj%<MRM#@R\,Kl%@vS0tQ0460X@5{kPoPqb7b8b91EQM/HGP8b6S04PreQ0sPL%2mRr#2R1#2R[#2R0#2RR#2R<#2RO,68PpQ0nQ0rP4P4Q0[P4Q0UP4Q0OP4P3P4Q0HP4PhP4PfP4PZP}F?D1D1P7L0:]0P716NOQ0ZPpQ0mPQQ0pP4P4Q0]P4Q0WP4Q0QP4P3P4Q0KP4Q0CP4P`P4Q0>P}F?D1D1PNDBI0CeW0PL%28RN/6OPpp+01nS0>PQ%27RZP4P4p+01AS0pP4fwS0mP4fnS0rP4P3P4feS0uP4f\S0vP4PbP4Q0<P}F?D1D1PZDBDC]0P816mOPzPpp+01mPQPmP4P4Q0^P4Q0XP4Q0RP4P3P4Q0LP4Q0DP4Q0@P4P]P}F?D1D1PmDBDCeW0PL%2NRN/6OPpp+020S0<PQ%2ZRmP4P4Q0aP4Q0ZP4Q0TP4P3P4Q0NP4Q0GP4Q0BP4P^P}F?D1D1PmDBDC]0P816rOQ0QPpp+01oS0wPQPrP4P4Q0`P4Q0YP4Q0SP4P3P4Q0MP4Q0FP4PaP4Q0?P}F?D1D1PrDBDCeW0PL%2NRN/6OPpp+022S0?PQ%2mRrP4P4Q0cP4P|P4PzP4P3P4PxP4Q0IP4PiP4Q0=P}F?D1D1PrDBDC]0P8161OP?PePdPj%@>/K~%;2R>#<Rd#@R^,Kl5QkPoPqb7b8b9Q0k1EQdRl'5S0=P8b6S0xQ0q/5lP@Q0qPpp+023R]%G8S0q1q43CAXH@PUPlP8J08b1Ppp+021S0yPQP1P4P4Q0_P4P{P4PyP4P3P4PwP4Q0EP4PgP4P_P}F?D1D1P1DBDCeW0PL%2NRN/6OPpp+024S0zPQ%2rR1P4P4Q0eP4Q0]P4Q0WP4P3P4Q0QP4Q0KP4Q0CP4P`P}F?D1D1P1DBDC]0P816[OQ0MPpP]PQP[P4P4Q0dP4Q0\P4Q0VP4P3P4Q0PP4Q0JP4PEP4Q0AP}F?D1D1P[DBDCeW0PL%2NRN/6OPpp+026R[PQ%21R`P4P4Q0fP4Q0^P4Q0XP4P3P4Q0RP4Q0LP4Q0DP4Q0@P}F?D1D1P`DBDC]0P8160OQ0EPpp+025S0@PQP0P4P4Q0bP4Q0[P4Q0UP4P3P4Q0OP4Q0HP4PhP4PfP}F?D1D1P0DBDCeW0PL%2NRN/6OPpp+028R0PQ%2`R_P4P4Q0hP4Q0`P4Q0YP4P3P4Q0SP4Q0MP4Q0FP4PaP}F?D1D1P_DBDC]0P816ROPEPpp+027S0FPQPRP4P4p+01JP4Q0pP4Q0mP4P3P4Q0rP4Q0uP4Q0vP4PbP}F?D1D1PRDBDCeW0PL%2NRN/6OPpp+02:RRPQ%2_RbP4P4Q0gP4Q0_P4P{P4P3P4PyP4PwP4Q0EP4PgP}F?D1D1PbDBDC]0P816<OPfPpp+029S0EPQP<P4P4Q0iP4Q0aP4Q0ZP4P3P4Q0TP4Q0NP4Q0GP4Q0BP}F?D1D1P<DBDCeW0%2N/6O%2bRN/6OAXsuu?Xuu?Xuu?Xuu/[MS0BPN1E8uX@@R<P<P<P<P<P<P<P<PsO1S0GO1S0NO1S0TO1S0ZO1RgO1REO1RaO1P<PbPaP<P_PEP<P`PgP<P1Q0ZP<PrQ0TP<PmQ0NP<PZQ0GP<P7Ps1U@sCWCWCWCWCWCWCWCWPOPM1U@MRsJ0VP8H07Q0B&0U;%O;#Jp-0R<P?Pe20S@7RZPjPk20R@2R29{k~Rm&0JBRrPk1K2n/Kn/Kn/Kn/Kn/Kn/Kn/Kn=Rk\PrPkPAPBPBPCP:J0QCwCwPoPqb7b8b9X?@WEAX7uu?Xuu?Xuu?Xuu/[MP:[\c^?@^E<P8Ppp+02>PQ%2F#2#2#2#2#2#2#2Af4}FDC%OFP7P;O4b6bibBPpp+02;RCPQPNP4P4Q0jP4Q0cP4P|P4P3P4PzP4PxP4Q0IP4PiP}F?D1D1PNDBDCeW0X;LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020111100X=LP8O1n0110000020011100X=LP8O1n0110000020011100X=LP8O1n0110000020011100P8O1W0X;LCYCYP=Q0lPQP4P{P4PyP4PwP4P3Q06>0;4}D1D1Cge&0IUPSJ0PQ07eCYQ01%OOR},EQ/HGRGA9c8}R3PpQ0820?Q7RyPtC4[^;@R{'=Q0;PGP{Q04%J7R{1[7}RG'=A9{7MR=P{PGP{P8X@@RGPMO1RN,[71U<{A7<{{e:0T{{P@P@Q00PGQ001[78$0wXm@X@@P7P71U@7P}PNPGPG%O8,U@X@LPOPMPsJ0vN<05J0tP8H07P=P?PePZPjPkPkPmPk20s2\H0rPrAQk2~AQk2nQ0t9Qk2AQk2^Q03#<R^#@9Qk2Q02#;#<Rn#@9Qk2%>>#<R~#@9Qk2%;>#<R>#@9Qk25]k5]k5]k5]k5]k5]k5]kCwPoPqb7b8b9X?@A9c8M&047157uP7PvP7PdP7P^P7PnP7P~P7P>C`D:D:40pRM[^?@P8P:P7O2b6bBPMP5&04;P;PuP;PvP;PdP;P^P;PnP;P~15;>D:D:D:PpQ0nPQP:PtDDP8&04:P@PKPpQ0wPyPtC4^03X;@Q0o?9K}P|PpQ0>PQPKPtDDeW0PFP8P:K0MW1P8O1P:PuP:PvP:PdP:P^P:PnP:P~15:>D:D:D:P515FuPFPvPFPdPFP^PFPnPFP~PFP>C`D:D:PpQ0>PQPJPtDDP815JuPuPpQ0yPyPtC4^03X;@%Ju?9u}Q0WPpQ0<PQPuPtDDeW0PIP8PJE_W1P8O1PJPvPJPdPJP^PJPnPJP~PJP>C`D:D:P515IvPIPdPIP^PIPnPIP~15I>D:D:PpQ0<PQPHPtDDP815HvPvPpP]PyPtC4^03X;@%Jv?9v}Q0RPpQ0?PQPvPtDDeW0PDP8PHE_W1P8O1PHPdPHP^PHPnPHP~15H>D:D:P515DdPDP^PDPnPDP~PDP>C`D:PpQ0?PQPTPtDDP815TdPdPpQ0@PyPtC4^03X;@%Jd?9d}Q0xQ0=P@Q0kPpP[Q0qPtC4XH@PYPlP8J08b1PpQ0zPlPtH0>eW0PSP8PTE_W1P8O1PTP^PTPnPTP~PTP>C`D:P515S^PSPnPSP~15S>D:PpQ0zPQPUPtDDP815U^P^PpQ0FPyPtC4^03X;@%J^?9^}PwPpP[PQP^PtDDeW0PWP8PUE_W1P8O1PUPnPUP~15U>D:P515WnPWP~PWP>C`PpP[PQPYPtDDP815YnPnPpQ0EPyPtC4^03X;@%Jn?9n}Q0JPpP0PQPnPtDDeW0PVP8PYE_W1P8O1PYP~PYP>C`P515V~15V>PpP0PQPXPtDDP815X~P~PpPCPyPtC4^03X;@Ry%J~?9~}PhPpPRPQP~PtDDeW0Q0:P8PXE_W1P8O115X>P>Py%J>?9>}PfPpPRPQP>PtDDeW0Q0:P8PXE_W1P8O1n200100000021000010000W1P8O1n200100000021000011000W1P8O1n200100000021000011000W1P8O1n200100000021100011000W1P8O1n200100000021000011000W1P8O1n200100000021000011000W1P8O1n200100000021000011000bIX03X;@CYCYQ05eCYCrCrCrCrb[bSWOWNWAP7P8O2n2001000000121000000W1P7P8O2n2001000000121000000WJX2PP7P8O2n2001000000121101000b<W_WWP7P8O2n2001000000121000000W1Xh4P7P8O2n2001000000121101000b<W^WVP7P8O2n2001000000121000000W1Xg4P7P8O2n2001000000121101000b<W]WUP7P8O2n2001000000121000000W1Xf4P7P8O2n2001000000121101000b<W\WTP7P8O2n2001000000121000000W1Xe4P7P8O2n2001000000121101000b<WZWRP7P8O2n2001000000121000000W1Xd4P7P8O2n2001000000121101000b<WYWQP7P8O2n2001000000121000000W1Xc4P7P8O2n2001000000121101000b<WXWPP7P8O2n2001000000121000000W1Xb4P7P8O2n2001000000121101000b<WaW`WMP7P8O2n2001000000121000000W1WDP7P8O2n2001000000121000000W1P7P8O2n2001000000121000000W1WCP7P8O2n2001000000121000000W1WAP7P8O2n2001000000121000000WDWLP7P8O2n2001000000121000000W1WCP7P8O2n2001000000121000000W1WAP7P8O2n2001000000121000000W1X>6P7P8O2n2001000000121101000W1XF9P7P8O2n2001000000121101000W1WkWKWlo"). Qed.

(* [comment removed for export] *)
Lemma RHEAP_need_locks : forall s LB m, RHEAP s LB m -> rw_cells psegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_RDriver_kit ()) ["CANSEC2"] "p'0h01Hh13LB0h22_Hh33_H0h43_H1h52sth62LBh74MREPh82NLh93_H2h:3_H3h;1mh<1si001xp;1p;4p;2p;3p;5g00O5j1[Tg02Chj4ZTg03@<j15Tg01SMR0j2HTg00K_j1?Tg00LDj1LTg00POj2KTg02b\j1JTg00ecj1UTg03A2j3>Tg03Amj2ITg03Bnj3CTg03Cmj28Tg03E0j3GTg02;?j1FTg02f;j1PTg02K3j46Tg03F1j1OTg00`Wj1NTg02<7j1ETg03Fij1MTg00=oR1j27Tg03Kgj3QTg03LRj1RTg00Fhj3STg03MGj1TTg03N>j5YTg00XSj3XTg03O>j2WTg03P@j2VTg02MXR2f1R3f0R43Qp=;g03QBR5%R47S3p=3f3R6g03R;f2R7%T3P4DYp=2A>673/74p=:1734,77p=0%?4#?p==g02LcR8?X34p=<g00H7R9P3g03Z2P4C6p=11W671V34'7p=4AG673/74p=9P9P3g03S=P4C6p=AP9P3g03T>P4C6p=BP9P3g03U8P4C6p=@P9P3g03V6R:P4C6p=Dg00Hl%[2R2g03X<p,2rcR;P7P3P4CZP0P5f4R<,;4%53R=f5R>'3P;P3P6P;P3P>P4C2C:30X12,H2X55g01KS#?#=R?#Lg01EbR@'K#J%U8R8'<RA,17P4f6RB,;4f7RC,3=P;P3P>P;P3PCP4C2C:30X12,H2P0P21;4C%57f8RC'3P;P7PBP;P7PCP4C2C:30X1211BAP4f9RB,;4%5<f:R0'3P;P<PCP;P<P0P4C2C:30P11;30%5>f;R='3A>;>BP;P>P=P3C230110AP4f<R0,;6%5Cf>R6'3A>;C0P;PCP6P<C230P1%5Bf?R<'3P;PBf=RDP;PBP<P>C2C:116AP4%5=fAR='3P;P0f@R6P;P0fBR>PCC2C:P1A>;D=P;PDfCRDPBC211>AP4A>;<DP;P6fFR6P0C2P11I;=fER09C;=18;0P;P=P0P=P0P=P0C4C930116AP31I;DfDRDfHR65C;18;6P;PDP6PDP6PDP6C4C930P1fIRD9C;018;DAG;0DP0PDP0PDC430fJ/1AP4fGfK5C;fLR0,8;AG;60P6P0P6P0C430P1fMR0,8;P;PDP0PDP0PDP0C4C9fN/1AP4fO,8;P1P9fPRDg03Y6R6%F@#P/<8R=C6%O@#J/<8R@,AD%??#=#=#=#=#N#F#E/<8R?,BD%F:#E/<8R:,@D%M;#E/<8R8,DD'730P;P0fQRDP0PDP0PDC4C9fRR0/1A[P4P9P0P6P=C6fSR=/A@1B=?1@=:1D=8'730P1fTR1/A@1B1?1@1:1D1830P;PDfUR=PDP=PDP=C4C9fVR=/1A[P41A=@fWR=/B?1@=:1D=830P;P1fXR;P1P;P1P;C4C9P7fY/1AeW:W9W8P3P4O2n2001000000120000000W0W4P3P4O2n2001000000121000000W0P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W4W7P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0X12P3P4O2n2001000000121100000W0X55P3P4O2n2001000000121100000W0W;W6W<o"). Qed.

(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
