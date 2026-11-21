(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader premise; the munmap answers; mremap's maps_subtract cut; the reserved ledger; the VM budget; the recorded proofs of eager_munmap_exact, lazy_in_maps_munmap', munmap_ok replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout RT_iface RT_frmkit D_defs RT_state RT_rep RT_init RT_sys_stmt RT_sys_fixed.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_sys_munmap () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List6filterK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I46Stdlib7Sorting;Permutation;Permutation00K46Stdlib7Sorting;Permutation;Permutation01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00C46Stdlib5Lists4List7existsbI46Stdlib5Lists4List6Exists00I46Stdlib5Lists4List>ForallOrdPairs00K46Stdlib5Lists4List>ForallOrdPairs01I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic5proj1K46Stdlib5Lists4List>ForallOrdPairs02C46Stdlib5Lists4ListBForallOrdPairs_indI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53B238RT_state4vposC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib2K53B23=RT_sys_munmapAzcount_map_removeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC46Stdlib7Sorting;Permutation>Permutation_inC47Corelib4Init5Logic9False_indC46Stdlib7Sorting;Permutation?Permutation_symK47Corelib5Lists7ListDef6Forall02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53B236RT_rep8iv_apartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K52AS>BackingAlgebra1BC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra1SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K52AS>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra8iv_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib2K52AS>BackingAlgebra7S_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib2K52AS>BackingAlgebra:zcount_extC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K52AS>BackingAlgebra=zcount_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra6zcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra@sum_count_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib2K52AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm:mdl_munmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib2K52AS>BackingAlgebra=ivs_wf_filterC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C69OSSVerify5KrLib2K53Lib9NodesA_mmAmdl_munmap_vmmapsC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC69OSSVerify5KrLib2K53Lib7RelSpec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmap<FOP_In_apartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib2K52AS>BackingAlgebra6in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;andb_true_rC69OSSVerify5KrLib2K53Lib9NodesA_mm@covered_subtractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra;covered_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmap@sum_count_ext_onC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c69OSSVerify5KrLib2K53B23=RT_sys_munmap?sum_count_In_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra;zcount_trueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmapCsum_count_partitionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm?mdl_munmap_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm?eager_used_sem'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify5KrLib2K53Lib9NodesA_mm<lazy_in_mapsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53Lib9NodesA_mmEmaps_subtract_pieces'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53B238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state2awC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53B238RT_state3secC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC69OSSVerify5KrLib2K53B238RT_state7rt_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state8rt_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7l_ACEILC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K53Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_al0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state:allow_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep6ARTM_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53B238RT_state5l_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4l_f0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_tidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state8maps0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state>startup_grantsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state>pairwise_apartC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K52AS8AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC69OSSVerify5KrLib2K53B23<RT_sys_fixedAA_bytes_rtA_allowC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib2K53B236RT_rep8artm_sysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep>lazy_in_maps_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep9confined0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep;shadow_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep;maps_zboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib;NodesA_madv<noaccess_posC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7l_maps0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_sys_fixed<artm_in_mapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmap:FOP_filterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmap8FOP_permC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>existsb_existsC69OSSVerify5KrLib2K52AS>BackingAlgebra5in_ivC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmap=FOP_app_crossC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib2K52AS>BackingAlgebra;overlap_sumC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_sys_fixed@overlap_sum_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmapFPermutation_map_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_repAfilter_map_removeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmapBeager_munmap_exactC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53Lib9NodesA_mmCmodel_ivs_wf_munmapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmapDlazy_in_maps_munmap'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC69OSSVerify5KrLib2K53B23<RT_sys_fixedCcovered_subtract_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_modC46Stdlib4Bool4Bool=orb_false_iffC69OSSVerify5KrLib2K53B23<RT_sys_fixedBshadow_lazy_cut_ncC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23=RT_sys_munmapAzbound_map_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib;NodesA_madvCnoaccess_pos_munmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm>mdl_munmap_fdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm=mdl_munmap_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239RT_frmkit<ast_munmap_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ARTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2K53Lib5RzCPS5nretAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state8grant_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasI69OSSVerify5KrLib2K53B238RT_state5secst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6secmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7VMLIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6E0_MAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238RT_state4rtsA00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I69OSSVerify5KrLib2K53B238RT_state7layoutA00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7CREDIT0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC69OSSVerify5KrLib2K53B236D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEc69OSSVerify5KrLib2K53B23=RT_sys_munmap<iv_apart_symC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_sys_stmt;munmap_nodeC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Permutation_map_remove : forall l l' a, Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01ph11lh21bi001bh32l'h42_Hh51xh61Hh72IHh83IH1h93IH2h:3_H0h;1ah<3l''h=1yp;1p;2p;3p;5p;4p;6p;9p-1R0g0000R1p4p710p8P0P1p4p7210p8P0g000MR0p4p710p8g000hj14Tg001Mj1CTg001kj1;Tg002Nj29Tg002nj1BTg003Nj30TP1j35TP0j32Tg0049j1:Tg004dj18Tg005Dj31Tg005dj56Tg006Oj4ATg007:j2@Tg007hj6?Tg008Wl9=Tg009Dj27Tg00:=j3>Tg00:jj1<Tf2R0f1R1f0R23>#<p=3g00;H#4#4#4#4#4#4#CR3#;R4/94R5#BR6A0501R7P5A5442R8f4R9533X05R:=251A25:2505X36X16%:5A3380X05%85525R:=05:eA0512f6R:9338X05R;=250R<A25;1505A5449=33:g00;mR=P=P=P6P2f99338X05R>f5R?525R@915:P@n0100000020000P=P6P2A25>9RA915:PAn0100000020000505P2P5P?f89338X05RB=259RCf3RD925BRBP1D6P1n0110001020100b2f79338X05REA159D525A1590925E505eW7W4X36X16X55A5440RF=339P=P=P=P6A544D=33:RGP=P6P2A25E0RE9159PEn0100000020000RH915DPHn0100000020101P=P6P2P=P6PGA15DEPEn0100000020000RG9159PGn0100000020101505P2A33F?RFP=P=P=P6P2A15?BRG9159PGn0100000020000P=P6P2A159BPBn0100000020000RG915?505P2P5P9PDPECAP5P9PEPE1@5ER9D6n0110001020001b2PFP=P=A05GGP2P5PDPEPEP9D6P9n0110001020100b2n0110001020101b2A338?X05R?A15029151525A15129150925?505eX16X=5X55A25;D=05<A05D0A05CBP5A25>:R>P@PAP0P2E?A05>AeW9W:W8X47X<6X36X16PDP0P2M9=17D11701505eW6X;4X36W1o"). Qed.

Lemma FOP_filter : forall {X} (R : X -> X -> Prop) f l, ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01lh11xh21Ah31Hh42Hyh51fh61Ph72Hlh82Hxh92IHh:1Rh;1Xh<2_Hh=1bi001bh>1yp;1p;3p;2p;4p;6p;7p200R0g00<Mp4p710R1p8P0g00<ip4p710R2p8P0g00=FR3p4p710p8g002nj15TP3j32Tg000Mj31Tg00=kj2;Tg004dj1?Tg00>Pj33Tg005Dj38Tg00?1j30Tg00?Hj37Tg00?jR3j26Tg00@Ej4:Tg00@cj69Tg00A>j6>Tg00Acj7=Tg00BJj3<Tg00;mR4f0R5g00Bd3<p=4f1R6p-0R7[\5P4\6f2R8#5R9f3R:?285f4R;P:%5;f5R<A1<:572;W01;;:%?;91;892;:e%5<f6R=P<P6O1;35f7R>?2=6f8R?A1?=872>P>P;O1P4P4f;R@f:RAP4f<RB#5P5f9RC=1@<RD98@=PDn010000002000032P5PAPCP<A1A?;P7\5R7%56REP3A3865A0;58P;P6O1[^1:RF[A0:56P:P6O1[^18A3:86[RGA3;:8\FA7865P5n2001000000120000000W0W6X22PG^0E^67^22P5P@PAP=O1PDA1BA=90B5P4\5R4P3A1:8590:6A0;86P:P8O1#4'6[RAA0:65P8P6O1#4'6A1;:690;8RD[A0<:8P;P:O1#4'6\DP:P8P6P5C:P6n2001000000120000000X09X16W5X21PA^09^16^54^21P5f>R1PBP8P?P6O5A018?PBP8O1#4'6P3f?R3?0:Cf=R8P:O1#4P3P@P;O2P5fAR4?0<@f@R<P=O1#4fCR=fBP1O1R9;38fDRAfERD?053PDP4P6O2[]1[A0A51PAP<P6O2[^1=P=P3O1=3A1[A7=98PBP>P6E9W<W4P6P5O2n2001000000120000000b4b3W4X>@O4b3P6E>P6n0110000020100b=A8C;:91C>92C?eW9W7W8W0X1;P6P5F=W3W0W5W:X;0o"). Qed.

(* [comment removed for export] *)
Lemma zcount_map_remove : forall (l : list (word * word)) (a : word),
  (length (map_remove l a) + length (List.filter vpos l) <= length l + length (List.filter vpos (map_remove l a)))%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01ph12Evh24__x1h34__x2h44__x3h54__x4h67__arithh74__ffh88__varmaph95__with:1bi001bh;2Ebh<3IH0h=4cstrh>5cstr0h?5cstr1h@5cstr2hA1lhB2IHhC1ahD1ehE1xp%0p;1p;2p;3p;4p;6p;5p;<p;7p;Bp;8g000hj1BTg001Mj1oTg001kj1\Tg002Nj2WTg002nj1UTg0000j3ETg000Mj38Tg00CDj20Tg00CdR0j2<Tg00D>R1j22Tg00DZj2?Tg004dj1PTg00E4j1`Tg00ERj1_Tg00F0j1]Tg00F[j2OTg00G>j2[Tg00G`j2ZTg00HLj3YTg00Hkj4XTg00I]j4FTg00BJj3=Tg005Dj39Tg00JHR2j1ITg00KAR3j1@Tg00K`j25Tg00L7R4j17Tg00LWj1VTg00M5R5j21Tg00MRj4nTg00N9j1KTg00N^j2TTg00O<j4STg00OZj2MTg00P=j1mTg00Pbj1fTg00QDj6QTg00Qbj5aTg009Dj2bTg00:=j3cTg00:jj1dTg00RDl<RTg00Rij4^Tg00STj7hTg00T8l<iTg00T]lBjTg00UCj3kTg00Ufj8lTf2R6f1R7f0R83c#dp=3A8728,06p=6A8728p=;1078,56p=A1567/<8p=4g00VJR2g00ViR9P0P4P1g00WGR:g00WiR;g00XHR<P7P;P<P8M<Rp=gP9P7g00XfP8C^p=CP7g00YMR=g00YlR>P>g00ZLR?P8g00ZlFhp=Dg00;mR@g00BdRA7=8p=N1067/58p=JP2P2P9P9P3P4P4f3R3g00[LP6P7P8M<ip=HP2P2P2P9P9P9g00\0P4P4P4P5g00\Pf5R5f4RBP3P6P7P8MBjp=>P2P9P0P4P1P:P5PBP3P6P7P8M<Rp=GAk978p=:P3P=P>P>P?P6P7P8Glp=L1578,<6p=eg00;HR=#BR:#BR1#B#B#B#B#oR4#\R0/W0R2#URCP2AE008RD=346X02=828RE,02A6228RF1028RG1;2E7A234XAC1<;;12<<R;1?9<RE/gEg00]3RE#PRH%UERE%`9RI%_9RJ%]9RK1O9<RL/CL'D1[K?R?P8P61?@A1Z86#NdAY9<7CXRLb7b8b9P;P8b6CFA34D7X02%P2R;582RM,02A622;A622M9J2;34eA34D3X02=828R;,021;2;9AG274FAE006=343P@1?@8S00AE003=34B==@8P@AE005f6RF534==@8P@PCP7f8RG934DX02=825R;992FP;n0100000020000R;,02P@PC%IFRM1;25RN992FPNn0100000020000,02A92F5A622;5J234];P7AE00B=345R;#N%I5S01P@Q00A=@M8S02P@%IGRM==@8RNf9ROf;RP934DX02=82GRQ592RR,02P@PCP71;2GRS992OPSn0100000020000,02RTA92OG,02RU1;2R7A234]1P7f7RR#IRV#NRWP@PA102QRA#@RX102SRS#@102GRY#@P@PCP81;2QRQ992OPQn01000000200007A2RZ34X:@f:R[934DX02=82RR\,02R]#@R^1;2RR_,02R`#@Ra'5Rb102RRc#@Rd1;2\Re,02Rf#@Rg'5Rh'<%7]Ri%V=Rj'1Rk%7`Rl/1jRm'1Rn%7cRo/1jRp%7fRq/1jRr'1Rs'2PbPnP^Pk118jXE9RnP]Pi1?9iRtCHS03PaPmPnP`Pl1?9lRuCHS04E>PhPsPdPpPnPcPo1?9oRsCHS05PgPrPnPfPq1?9qRnCHE>EG15]`Rr15cfRg'<11ilRh11oqRv'2RwPrPhP]PiPtP`PlPuE>S06PgPvPcPoPsPfPqPnE>EGPFCnRFPw%KYRs%7Y,2<RYf<934DX02=82O9622RO#KRo%7O,2<ROf=Rc934DX02=82[,02R[#KRv%7[,2<R[A622PRP#KRg%7P,2<R<PHPEP9P91T9BP6PICSP71T93CSRIPJPK1M9=RP1M9:R:':Rx%m=,M9R=1M91R1':'C,DKRy%f>R>1O9jRz,:PR{1::zR|':1:=zR=1:1z':'C,DKCLP?PLb7b8b9X29X39X49X5911871163'2Rz117jR}116jR~'1113jR311Bj'1'2[^29^39^49^59P8f@934DX02=82cRj9622#7102c#7A622c#7102j#7P5O5R5b6b@b?b>b=b<CFA92Ge,029ebdePMP8EQA92G\R\,02RbA92G_,02R_A92GR,02RR1;2\7A2R\34eW1g00]_RG9=@VRVP@PGA4XSZX:@15^`RZ15dfRS'<RX11klRe11pqRj'2PZPeP^PkQ03P`PlPuE>PSPjPdPpQ05PfPqPnE>RnEGPFPwPsPYPoPOPvP[PgP<PHPEPIPJPKPyP>1:{:1:=1R='C,DKCLP?PLb7b8b9X29X39X49X5911}6113BR3'2\z^29^39^49^59P5b6b@b?b>b=b<CFPXePMP8EQA4b`\eW1n0110001020101P8O1b1b:W;A=@;GQ01P@Q00Q02P@AAU2Q94AT^1NP715]aRN/<SRA11imRT/2jPNPTP]PiPtPaPmQ04E>PSPjPnEGPFPwPsPYPoPOPvP[PgP<PHPEPIPJPKPyP>1:P|/C=,DKCLP?PLb7b8b9X29X39X49X59117~/23\z^29^39^49^59P5b6b@b?b>b=b<CFPAe15RfRR94]_eX1W1<rSRW12hjPrPhQ06PSPjPnEGPFPwPsPYPoPOPvP[PgP<PHPEPIPJPKPyP>1Cx=,DKCLP?PLb7b8b9X29X39X49X591176/23\z^29^39^49^59P5b6b@b?b>b=b<CFPWe1<rReX1Vn0110001020101P8O1b1b:W;n0110001020101P8O1b;b:A34DBX02A9267R6582RD,02A6226A622D9J2634eWBXACXD2P7Da1b78R8,02A6227A62289J2734eXC0WAo"). Qed.

Lemma zbound_map_remove : forall (l : list (word * word)) (a : word),
  Z.of_nat (length l) <= Z.of_nat (length (List.filter vpos l)) + 1 ->
  Z.of_nat (length (map_remove l a)) <= Z.of_nat (length (List.filter vpos (map_remove l a))) + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "h04__x1h14__x2h24__x3h34__x4h41Ch52C0h61Hh77__arithh84__ffh98__varmaph:5__with;1ah<4cstrh=5cstr0h>5cstr1h?5cstr2h@1lp;1p;2p;4p;3p;Bp;<p;7p;8g000hj15Tg001Mj1aTg001kj1STg002Nj2JTg002nj1FTg00CDj21Tg00L7R0j10Tg00LWj1OTg00M5R1j24Tg00D>R2j22Tg00^?j2HTg009Dj27Tg00K`j2;Tg00CdR3j2ETg00DZj26Tg00MRj4UTg00N9j1:Tg00KAj1BTg00_Jj2>Tg00`3j3ATg00`\j2RTg004dj1QTg005Dj3NTg00N^j2@Tg00E4j1MTg00O<j4?Tg00ERj1LTg00F0j1KTg00OZj29Tg00UCj38Tg00P=j1ITg00Pbj1PTg00F[j2GTg00G>j2TTg00G`j2`Tg00BJj3_Tg00HLj3^Tg00Hkj4]Tg000Mj3\Tg00T]lBYTg00RDl<XTg00Rij4ZTg00STj7[Tg00Ufj8WTf2R4f1R5g00JHf0R63\'1p=3g00VJR7P7P7g00ViR8P8P8g00\0P0P0P0P1g00\Pf5R1f4R9f3R:P4P5P6MBYp=DP7P8P3P0P2g00WGP1P9P:P4P5P6M<Xp=VP8P5g00XfP6CZp==P5g00YMR2g00YlR0P0g00ZLR3P6g00ZlF[p=<P:P2P0P0P3P4P5P6GWp=Cg00;HR2#5R7#5R;#5#5#5#5#a#SR</J<R=#F11=5#0A3==5#0%O2R>'4'21H451745R?,1=A3==4';11=4A3==?';'E17:4R?,1=R@A3==:RA';RB11=:RCA3==?R?';RD'E%0@RE%0ARF'4RG%0CRH%0?RI'4RJ'2RKPBPGP@PE168EPAPF168FEDPDPJPCPH168HP?PI168IEDEVP6CUPK11=9RK#:g00XHRI%0K'2A3==1RK#:%0K,2If6RK/7193==R?#:%0?,2If7R?/7K,1=RK#:%0K,2Ig00]3RKg00WiRH#BRC#B,>81>8C1>8H5A85A8g00aH'R%QK3N%FKP8P81@89P4%M8C?P51@8:C?%L8%K8RK1982RH198;R;588%I2,98R21987R7588'=,<K%P0R0PK1G8>RC988;,=2,<KP0A887C,=H,<KCCCC1TK3P6P4g00;mRKg00BdR3'61`64=_K3dA^8I5C]b8b9b:X08X18X28X38146:1445'2149>,2:14:>,24[[^08^18^28^38P6f9R693==#011=6#0f8,76R693==#011=6#0P1P?O6b7b?b>b=b<b5b4W6X;<W@o"). Qed.

Lemma FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01Hh12H0h21li001lh31eh41xi011xh52Hlh62Hxh72H1h82HFh93Hl'h:2Hyh;3Hylh<3Hyxh=2l'h>2l0h?1ai021ah@1AhA1PhB1yhC2HphD2HshE2HzhF2IHhG3IH1hH3IH2hI1RhJ1XhK2_HhL3_H0hM3l''hN2x0hO1zp;1p;3p;2p;6p;4p;9p200R0g003NR1p4p710p8P0g00b4R2p4p710p8P0g00bPR3p4p710p8P0P3p4p7210p8P0g00>PR4p4p710p8P0g00QDR5p4p710p8P0g00bmR6p4p710p8P0g00<ip4p710R7p8P0g00=FR8p4p710p8g002nR9j11TP1j3@TP8j33Tg004dj16Tg00=kj2KTg005Dj30Tg00BJj32TP2j6?Tg00cYj2>TP4j34Tg00?1j3<Tg00?Hj3CTg00d8j4JTP6j6ITg00@cj6HTg00A>j6ATP5j69Tg00DZj2=Tg00dej6DTg008Wl9FTP3j6GTf4R3f3R5f2R6f1R2f0R13033p=;A0562=231p=Bf7R:f6R;f5R<A0356P2P1EGp=8%16?221p=7A0621903593;<p=5A06219035p=:A06219235p=Ep-0R=\2\1P6P2P1O2P5P2P6O2[^B6^42%16%15A@321P<%1<R>%1;R?A3:;2f8R@?3:2[W=W2%6<93<31K;<W8%1:RAA@@21f9RB?3@6f:RC?3B6[PCPBPCP3P5D;P8f;RDPCf=RE#1RFA0E:;RG722f>RHPEPHP@P;D;RI[P1%1DRJ%6DRKA0D<3RL32f<RM#1RN%6MA0M;<RO32PF%6EP9PHP=P1g00eFRPg00ebRQn10110000020020000000X3Fg00f?RFPGP1E?PQ1>I1b1W0P1O1W0f?RIf@RG#1fARRPGP2O1;41fBRS?3R2fCRT#1RUPTP5P6A0TEMDBfDRV#1RWPVP3P5A0VHEDBfERX#1RYPYP9fFRZfGR[#1R\P1P<P1n10110000020020101100X3YPXP<P3A0XIHP1G8A2Y3H%1ZR]PZP9P[fHR^P1P:P2n10110000020020101100X3]PZP;P<A0ZGIP2G8A2Z;GA2[:RP1A2^@SfIR]PTfJR_?7BTR`fKRaP_P2O1;4CfLRb?3aDfMRcA0c[XRd73b]5]6[X4]%1]Re?2@SP1P`%1aR`PVPaPZO1=4b1A3cb2fNRfPcPfP^PZD;]5]6X2`P_PXO1=4aVA3baXPcPbP[PXP=\1Rg%12Rhg00?jA4621A<316P3P2O1[^45Ri[A<512P5P2O1[^46A4562[RjA4356\iAC621P1n2001000000120000000W2WAX@7Pj^2h^Ag^@7P1PfPcP^O1PZfOR7?<1[fPRgP7P_O1Rh;4]fQRjfRRi?<1aPiPcP2O2[]4[A<j1_PjPbP2O2[^4gPgPaO1=4j_[ACgh]P3P2PgP^P]P2PgP]P^P[CJP1EIEHWEXOfO4b0PTP1O1EAW5W6PCP1E9b7W1PBP1E9b1W0P1O1b1P1O1b1W0P1P6P2O3W0W5W6W>W?P5P6P2P1O4n200210000000020041102100000000A2N1OPEPMPEP:P<D;[X2JPLO1P11=NOO1b0W8WFWCW=X2?X4<P@P:P@P2P@P6P1F5P8PBP@PDP3PDP<P5D:RO92J2PMPDPMP;PMP<P3F5RN[P1%1BRL%6BPBP6PBP5P2D:Rh32%1CRk%6CPCP5PCP3P6D:Rl32PJPKP9PMP=P1PPPQn10110000020020000000X3JPFPOP1E?PQ1>N1b1W0P1O1W0%1HPHP2O1=4I1A3GI2A0R56PRPCPRPDPBD:57RA0S35PSPDPSPMPCD:57SPUPUP9PVPYP1P<P1n10110000020020101100X3UPTP<P3A0TEDRY90TMP1G8A2U3YPWPVP9PXPZP1P:P2n10110000020020101100X3WPVP;P<PVPEPVPHPMD:P2G8A2V;EA2X:HP1A2Z@IP[PGA0^SG97^BRGP^P2O1=4]CA3_]DPaP_PaPXPaPVPTF5]5]:[X4[P\P@P[PRPIDEP1PGPeA0]TRRRP]PTO1=4_1A3a_2PbPaPbPZPbPXPVF5]5]:X2eP^PSO1=4]RP_P]P_PVPSD;P8PaP_%1cR_?22dPfPcPfP^PfP[PZF5R^[P1%6aA0aXTR852`%1bR]%6bA0bZVRV32P_%6cP9PfP=P1PPPQn10110000020020000000X3_PFPdP1E?PQ1>^1b1W0P1O1W0%1gPgP2O1=4j1A3ij2fSR^A0^56A0^ca37fTRaA0a35A0afb37fURd#1R_P_P9fVRRfWRe#1P1P<P1n10110000020020101100X3_PdP<P3A0d7cP1G8A2_3c%1RR_PRP9PefXRGP1P:P2n10110000020020101100X3_PRP;P<A0RgfP2G8A2R;gA2e:jP1A2G@ifYRgP^fZRf?7BiRif[R_PfP2O1;4Cf\RI?3_Df]R\PIP\PeP\PRPdF5]9]6[X4gA7g@jP1Pi%1_RiP^P_PRO1=4I1A3\I2f^RjP\PjPGPjPePRF5]9]6X2iPfPdO1=4_^A3I_aP4P\PIPRO1f_R4#1R_A04geRa722f`R^P4P^PfP^PgPGF5Rf[PT%1\Ri%6\A0\edRd32%1jRH%6jA0jGRRR32P_%64P9P^P=P1PPPQn10110000020020000000X3_PFPaP1E?PQ1>f1b1W0P1O1W0faRffbRQ#1PQPIP2O2fdRIfcRaP\O1;42feRFA0F56A0F4\37ffR\A0\35A0\^j37fgR_#1RPPPP9fhR=fiRW#1P1P<P1n10110000020020101100X3PP_P<P3A0_f4P1G8A2P34%1=RPP=P9PWfjR9P1P:P2n10110000020020101100X3PP=P;P<A0=Q^P2G8A2=;QA2W:aP1A29@IfkR:PFflRQ?7BIRIPQP\P2O2fnR^fmRPP_O1Rf;4DfoRYP^PYPWA0Y=_RUD;];]<[X4:A7:@aP1PI%1PRIPFPPP_P=O2P^P=O1=4Y2fpRFPYPFP9PFPWP=F5];]<X2IPQP\P_O2A4^f\PYP^PWPUPYP^PWO1P=P_PPP=PWP2O3PTEDPYP^P=P_P1PSEAEAW;W<PCP1E9b7W1PBP1E9b1W0P1O1b1P1O1b1W0P1P6P2O3W0W;W<W>WNP5P6P2P1O4n200210000000020040101100000000A2H1RP4PjP4PgP4PGPeF5[X2iPdO1P11=HRO1b0W9W6PCP1E9b7W1PBP1E9b1W0P1O1b1P1O1b1W0P1P6P2O3W0W9W6W>X?7P5P6P2P1O4n200210000000020041102100000000A2]1VPcPbPcP[PcPZPXF5[X2`P8O1P11=]VO1b0W5W:PCP1E9b7W1PBP1E9b1W0P1O1b1P1O1b1W0P1P6P2O3W0W5W:W>X?EP5P6P2P1O4n200210000000020041102100000000A2k1lPDPCPDP<PDP3P5F5[X2LPhO1P11=klO1b0W8X2AXB;X4<A@@62A3B@5A3CB5[A@C56A3DC3A3MD3[A3MD;P2P5P1O1O1W8WHWLWGWKXMAX=?X2>P6P2P1M9FW0W=W2WDWIXJ0o"). Qed.

Lemma FOP_In_apart : forall {X} (R : X -> X -> Prop) l x y, ForallOrdPairs R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "h03Hneh12IHh21Hh32Hyh41xh52Hxh61lh71yh82Hlh92Hph:1Rh;1Xh<1pp;1p;3p;2p;8p;6p;7p200R0g00?1R1p4p710p8P0g00b4R2p4p710p8P0g00?HR3p4p710p8P0g00=FR4p4p710p8g002nj14TP4j3:TP1j30Tg00f[R1j21Tg004dj19Tg00>Pj36Tg005Dj38Tg00BJj33Tg00g5j15Tg00DZj2=Tg00cYj2<TP2j87TP3j3ATg00@cj6;Tg00gNj3@Tg00ghj3?Tg00Acj7>Tf2R3f1R2f0R433#5p=2p-0\2\4%42f3R5f4R6?:53f5R7P6%47f6R8?054f7R9?052f8R:?276P:P8P7O2P:P7P8O2'1R;[[[W6%979073%989083A2965g00ebP;P3n010000000W0W3W5%48P8P2O1=694A::92f9R;?083f:R<?085f;R=?2:9P=P;P:O2P=P:P;O2'1[[[A8<6590<9A8=7690=9f<R>?2;:P1f=R??39<A0?<8P?P=P<O2P?P<P=O2'1P3f>R8?3:=f?R@P;f@RA?04;fARB?0?<RCfBRD?238PDP5P@O2PDP@P5O2'1[[[A2B2?PBP3P8O2PBP8P3O2'1]0]1X4@A0@;:A0A>;REA3B=?RF#5PBP>P8O2PBP8P>O2'1RG[[[A3A<>RH#5P1PFPCPGP7A3D>8fCRGP?fDRC?08?RFfERI?028fFRJ?2A3PJPBP5O2PJP5PBO2'1[[[A2I@2PIPAP3O2PIP3PAO2'1]0]1X7GA0G?>A2I@@PIPAPAO2RJ/1J[\F[A2C88PCP@P@O2RF/1FP41=I@O1'<W0W1P@P4P5P3G7W2P4O1A0D8=PDP?P@O2PDP@P?O2PDP?O1RF=6G>A0I48PIPAP2O2[^4C[RIA0C4?PCP@P2O2[^4GPGP8O1=6C?[RJAAGF>RFP=P@P4E;3@W3P4O1n200100000021000010000W0W1P>P4P7P3G7W2P4O1A08=9P1A3@;=A0@=:P@P?P>O2P@P>P?O2'1P5PBP=A0D@=A0G2>A2CB3PCPDP5O2PCP5PDO2'1[[[A2GA2PGPBP3O2PGP3PBO2'1]0]1X7BA0B8<A0D>=A2GA?PGPBP8O2PGP8PBO2'1[[[A2D@>PDPAP?O2PDP?PAO2PIPJPFP=PAP6E;3?W0W1P?P4P9P6G7X2HP4O1P9P3P4P6O3X3EP4O1n200100000021000010000W5P4O1n200100000021100010000W0W3W5W1W8W9W6X<7P5P4F>W2W7X43W6W:X;0o"). Qed.

Lemma FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01xi001xh12H0h22H1h32Hlh42Hph52l2h61yh72Hxh81eh91li011lh:2l1h;1Hh<2Hyh=2H2h>2IHh?1Rh@1XhA1ai021ahB1pp;1p;3p;6p;2p;5p200R0g00?1R1p4p710p8P0g00b4R2p4p710p8P0g00hBR3p4p710p8P0g00bPR4p4p710p8P0P4p4p7210p8P0g00>PR5p4p710p8P0g00QDR6p4p710p8P0g00QbR7p4p710p8P0g00h`R8p4p710p8P0g00?HR9p4p710p8P0g00=FR:p4p710p8g002nR;j11TP8j30TP:j35TP1j34Tg004dj17Tg005Dj33Tg00BJj32TP2j69Tg00cYj2=TP5j36TP4j68TP9j3<Tg00ghj3;TP3j5ATg00@cj6@TP6j6:Tg00DZj2?TP7j5>Tf0R7f1R6p-0R3[[%16f2R9%19R4f3R5#1R2f4R1A0167755f5R8f6R<f7R=?461R>f8R??461R@P?P5P9O2[[]6]0[]5W:%75=0579559%7<94<6g00ebRAP?P1P5O2P6n010000000X<>W7X68X01W;X54%11A08679581f9R4?461P4P5P9O2[\@^6=^0<[]5%18A3<59=0<795<8A34<89446f:R@?461P:f;R:P@f=R>#1RBA0>4=93>@RC726P>P<P8O2RD[P1%1:RE%7:A0:=893:?RF32f<RG#1RH%7GA0G?<93G4RI32PB%7>P;f>RJP3P7g00eFPAn10110100020020000000X8Bg00f?PCP7E9PA1=D7b2W1P7O1W1f?RDf@RA#1fARCPAP6O1;67fBRB?5C6fCR3#1A3359A03D>933A32fDR>#1A3>15A0>AJ93>C32fERJ#1RKPKP;fFRLfGRM#1P7P8P7n10110100020020100101X8KA3J81A0JCDRC93JBP7E8A2K1C%1LRCPLP;PMfHR;P7P=P6n10110100020020100101X8CA3L<8A0LBA93L3P6E8A2L<3A2M=>P7A2;?JfIR<PLfJRB#1A0BL>724RAfKRCPBP6O1;6@fLRK?5C:PKPJP>O2]3]4[X0<%1<A0<J372?P7PA%1CRAA0CMJR:PCP<O1=6K7fMRD?5K6PDPLPJO2RN]3]4X9APBP;O1=6C:A0K;L95KCg00f[A2DBJA4DJ<PNP3fNR3?2CLfORNPKPNP7PMO2X0NP3PKO1RJA0NC<R;56NfPR:fQRAA0ADC747PAPNP6O2[]0[A0:KBRK94:7P:P3P6O2[^0NPNPDO1=6:K[A<NJ;P5PLPNPCP<PLA4NLCA4NL<;;>DAE@PMP7E9W1P7O1A43LBPBP<P9PMPLP7P>O6W7P7O1n200100000021000010000W3W4P@P7E:b=W2P4P7E:b2W1P7O1b2P7O1b2W1P7P9P6O3W1W3W4W9WAP5P9P6P7O4n200210100000020041102101000000A2H7IPGP8P1O2[X9EPFO1P71?HIO1b1W<W7X6?X0=W;W5W>X:2XB9P7D>W:W?X@0o"). Qed.

Lemma iv_apart_sym : forall p q, iv_apart p q -> iv_apart q p.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "h04__x1h14__x2h24__x3h34__x4h41Hh57__arithh64__ffh78__varmaph85__with91ph:1qp;1p;2p;4p;3p;8p;7g000hj10Tg001Mj1QTg001kj1HTg002Nj2BTg00i=j2>Tg004dj1PTg002nj1LTg00N^j28Tg00E4j1CTg00O<j46Tg00ERj1ATg00F0j1@Tg00P=j1?Tg00OZj24Tg00UCj3=Tg00Rij4<Tg00Pbj1OTg00Ufj8KTg00G>j2JTg00DZj2ITg00G`j2GTg00BJj3FTg00HLj3DTg00Hkj4ETg00M5j22Tg00D>j21Tg00f[j27Tg00j8j3:Tg00jUj23Tg0000j39Tg00STj7MTg00k?j7NTf1R0g00YMR1g00YlR2P2g00ZLR3f0R4g00ZlFMp=;f2R5P1P2P2P3P0P4FNp=5g00;HR6#0R7#0R8#0#0#0#0#QR9#HR:/B:R;1>04g00ViR<g00]3R=#P%L=P<P<f4R=,8<P5%C<C6P0f3R>,8<C6%A<%@<R?P1P2P2P3P<%?6,4<R114<85=<g00XfR814<6R6C<,;?R@P<14<79=<6P8P1C<,;?R155?%O2A5?1@GK1J?3P4P5g00;mR?g00BdR3'I1G45=F?3dg00XH=D<0CEb6b7b8X0<X1<X2<W3125>/141240/15'71205/1>12>=/10'7[^0<^1<^2<^3<P4A:::>,39A9::>,39A:::5,39A9::5,39P0O5b51>05eW4X:;W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_count_ext_on : forall P Q l,
  (forall p, In p l -> forall x, B p <= x < B p + S p -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01xh11ph21Hh31li001lh42Hah52Hxh64__p1h74__x1h81ah91zh:2H0h;2H1h<2Hqh=3Hx0h>2IHh?1Ph@1QhA7__arithhB4__ffhC6__sat2hD6__sat3hE8__varmaphF5__withG1mhH1nhI1qhJ1yhK2z1i012Ini021bi032l'p;1p;2p;3p;4p;<p;6p;7p;8p;5p;Bg000hj18Tg001Mj1pTg001kj1WTg002Nj2MTg002nR0j1ITg00?1j3=Tg00kcj1;Tg00D>j29Tg00l^j15Tg00M5R1j24j1FTg00mYR2j20Tg00?jj22Tg00BJj31Tg00n5j23Tg004dj1GTg00DZj2<Tg005Dj3]Tg00o8j2>Tg010:R3j1@Tg00L7R4j1ATg010Zj1VTg00LWj1DTg011[j2UTg0128j2?Tg012Uj1CTg0133j4STg00RDl<OTg013Vj6KTg00MRj4PTg014?j2QTg00f[j2BTg014aj2JTg015Ij3TTg00N^j2oTg00ERj1nTg00F0j1mTg00F[j2lTg00OZj2kTg00Rij4jTg00STj7hTg015mj6gTg016Qj7fTg00Pbj1_Tg00Ufj8^Tg00G>j2`Tg00G`j2aTg00HLj3bTg00Hkj4cTg0175j2\Tg00b4j6dTg00gNj3eTg017Sj5[Tg018Wj8ETg00ghj3ZTg00QDj6YTg00Qbj6iTg00T8l<HTg00T]lBXTg00ViR5f1R6f0R731p=6g00XHR8/97p=:1<57p=7P5g00VJR9P5P5P3f4R3P4f3R:g0194f2R;P6P7M<Hp=RP9P5P5P5P4P4f5R4P3P:P;P6P7M<Hp=LP5P5P5P5P5P5P1P7P6P;P1P:P3P4f6R<f7R=f8R>f9R?MBXp=Ng00;mR@^05RAg00;HRB#8RC#8#8#8#8#8RD#p#WRE/MERE#IRFA=E76RG%;;RH/97%5;,4H,07'2RHP<P6O1RIP4P6O151@[^05[^1EPEP>P6O1RJP=P6O1RK51@\H^05\G^1E1346RL1336'6]2X3F%GERM9=E7A1@KI\H^05[^1E1<58133M13:M'6eW2P?P6O1R?=1@J\H^05\G^1E13<6/6L]2A]E:;RL9=E7f:P6O1=1@?\H^05[^1EP513<;RH1>>3/471>=313=:'4'6X95P5P51>=:R?#F1><:RG#FPHPHP5P5\5RJP1P1P?PGPJ\5/<1P=P<%;:%5:#@%;3R1/97%53#@#A,41,07'2%V4%54R1#:%DCRC%DDRD'URJ,01'2P5%5<R1#@RM#ARK%;=RI/9:14I7,0:'2X95P6P1%;<RI/9;RN14IKRO,0;RP'21?81,4I,0;,2NRQPNPPPNP7X05RP1?87X05RRP1O1RSO1RT,4IRU,0;%CNP5P5P2PPP21067#CXJ5X05P;P;%7;POPUPPPPPPP5P5g019a1467CS#7XG5XH5PIPI%7IPKPTPPPP%A7#7X09PMPSPPPRP1P1%71DRELM:NM<OEKP6CPPQ%5=RQ,Q8108Q1?8QRR/6Q'219Q8A15R8'2'B%5>,?8P51JCD108C%:D108J[[%:CR>g00eFRRATCD6UW4%:J\R^4>p-0R>g00]3RR#G%IR1o56%n5%m5RRg00YMRDg00YlRCPCg00ZLRQPRPDPCPCPQPRPDPCPCPQP51l58g00Xf1k5BCjg00ZlFhRBPRPDPCPCPQP:EgFf%_CPBG^1`RQP7P;g00BdRQ,<@1a7;=1@QdAb586CcbBbEbFX75W6%:7/26%:6[^75^6>P7f<#5R8/0JP8P<O3bAbCbDbKb;b=,\1Ed14I1,0;,2NP3P=A1E==P>^3F^8EP0PEP>P7g00ebA1E6:P3P:P7O2'Bn10110000020020102103X3FX8Ep?1001101P=P<O21<E=3eP:P7O4b5b:W5X05D[16?GeGE%7HGE13=;P6A=E7:P;P6A1E46A=E63;Z7O2W<XIEO1EY13=L13<L'6eW2W>X3FX1EP6P7EiW2W3X@AW?o"). Qed.

Lemma sum_count_partition : forall P f l,
  sum_count P l = sum_count P (List.filter f l) + sum_count P (List.filter (fun p => negb (f p)) l).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "p'0h01ph14__x1h24__x2h34__x3h41lh57__arithh64__ffh78__varmaph85__with91zh:2IHh;1Ph<1bi001bh=1fp;1p;2p;3p;4p;6p;5p;7g000hj16Tg001Mj1QTg001kj1ITg002Nj2ETg002nj1CTg00n5j20Tg00:jj13Tg00M5j22Tg00DZj2?Tg004dj1;Tg00o8j2:Tg000Mj38Tg005Dj37Tg00N^j2@Tg00O<j4PTg00ERj1OTg00F0j1LTg00OZj29Tg00P=j1KTg00Rij4=Tg00G>j2HTg00G`j2GTg00BJj3ATg00HLj3FTg00Hkj4JTg00QDj6>Tg00Qbj5DTg00UCj3MTg00STj7NTf3R0f2R1f1R2f0R338'0p=4g00ViR412237A1p=11023,21p=BAM423p=5P2g00YMg00YlR5P5g00ZLR5P3g00ZlFNp=<g00;mR6\4g00;HR7#6R8#6#6#6#6#6#Q#IR9/E9R9P6[%C9R:P91003P0P9P1P3C4P0P9P0P3O1#3X09P3C431X4:g00XHR;/2;,?4%;9R<,01P1P9P2P<C4P1P9P1P3O1#3X09P<C431ef4R</03P<P9P0P3C4P<P9P<P3O1#3X09P3C431P<P1O1P6P6f7R=/:<R>?B=0P6P:P3f6R?=890R@979<P@n0100000020000,0=P6P:%33P=P3O1#3X09=890RA979<PAn0100000020000,0=31P3P4f5RB=891RC,0?RDP?P3O1#3X09=891RE7B?RF12>3RG10=@R@,2>10=ARA31X94g00]3R=#;RH%C=R=P41@41P21@40CPRI%O4RJ%L4RKP41947RL1948R8%K7,94R7'5'5RMg01:ERN15L8/57C='<1HK5R5P3P1g00BdRO,?61G31=A6OdAF4;2CJR;b6b7b8X14X24X341221,23RP1232;11^14^24^34P3PAP@P>O3RQb510?1RRP2E>1:?0/2RRSA790C,0?P6P:%3OA790ER0PEn0100000020000,0?31eP4PF12>A91G@X94PHP=PIPJP4PMPN15L7,58C=,<KP5P;b6b7b8X14X24X34123191P2^14^24^34PQb5PRP2E>P6P:g00]_#3P0PEn0100000020000,0?91SDen0110001020101b<A7912R2,0BPBP9P<P2C4PBP9PBP3O1#3X09P2C431eW:X4:X09P3DDW4W=W;o"). Qed.

Lemma sum_count_In_ge : forall P l p, In p l -> iv_count P p <= sum_count P l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sys_munmap ()) [] "h01ph14__x1h24__x2h32Hph41lh52IHh67__arithh74__ffh88__varmaph95__with:4__x3h;1Hh<2H0h=2H1h>1Ph?1qp;1p;2p;3p;4p;6p;5p;7p;8g000hj14Tg001Mj1]Tg001kj1STg002Nj2JTg002nj1GTg00?1j39Tg00o8j23Tg00n5j21Tg00D>j20Tg004dj1CTg005Dj3=Tg00kcj16Tg00l^j15Tg010:j17Tg01:lj3VTg01<3j32Tg01=3j2UTg00BJj3@Tg00M5j28Tg00N^j2ETg00E4j1TTg00O<j4DTg00ERj1RTg00F0j1QTg00F[j2NTg00OZj2<Tg00Pbj1KTg00UCj3BTg00G>j2ITg00DZj2LTg00G`j2MTg00HLj3HTg00Hkj4OTg00b4j6PTg00KAj1ATg00_Jj2>Tg00`3j3FTg00`\j2\Tg00P=j1[Tg00Qbj5ZTg00Rij4WTg00STj7XTg00Ufj8YTg00ViR0f1R1g00Xff0R2CWp=:P1g00YMR3g00YlR4P4g00ZLR5P2g00ZlFXp=;f3R6P3P4P4P5f2R3P1P2GYp=?g00;mR7\0g00;HR8#4R9#4#4#4#4#4#]#SR:/J:R:#GR;P:A9:21R<f4R=/3111=3'0[^0:X4;%C:R>99:2g00eb13=311=>'0P2n010000000W3X0:f5R>/3111>3'0\<^0:A=:6399:2f6R<%6=R?%5=#7R@3Vg00XHRAA2<?@'0f7RB/U=11B=,0Ag00f[A@:<6A9:6>f9RC?2?@%6BR@%5B#7R?52C11C<'8'0P3A@:B=P:f8RDf;RE%62%52#732%6C%5C#752ERF11EDRE'8'0X0:g00]3RG#CRH%GGRIP01E03RJP1%T0CD%R0RK%Q0RL1N0A1<09R9':,;LRM%K4R41<08RNAB0N9':,;LC?1IL5R5P2P3g00BdRO,L71M23=@7OdAH0A1COROb7b8b9X10X2010A1RA1813,01[^10^20P2PEPFP6O3b6P>P2EPW=P2O1A9:=<P<P>P2O2f:RF%6>%5>#73211FB'0g00WiRB#ARE#A,>01>0E1>0B5F05F0g00aH'\==GHPIP0PJP11E06CDPKPLPMP4PL%[8,<0R8,:N,;LP4AB098,:N,;LC?C?P5POb7b8b9X10X20X:01016186=,03[\A^10^20^:0P2f<R0/1C%6F%5F#7520A20@?P>P1O5b6b5W3P2O1n20010000002110001100013D613D<11D>'8'0eb<b;13<1A=:=6,1<'0eW3X0:W5X4;X?:P2DZW4W>o"). Qed.

(* [comment removed for export] *)
(* At LPS 08b1429 munmap rebuilds [vm_maps] with [maps_subtract] (Mmap.v, mmap_fixed_destroyed_next),
   not [map_remove]; these facts carry the ledger invariants across that cut. *)
Lemma FOP_app_intro : forall {X} (R : X -> X -> Prop) l1 l2,
  ForallOrdPairs R l1 -> ForallOrdPairs R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> ForallOrdPairs R (l1 ++ l2).
Proof.
  intros X R l1. induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|? ? Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros x y Hx Hy. apply H12; [right; exact Hx | exact Hy].
Qed.

Lemma FOP_iv_subtract : forall (a sz : word) lo hi, iv_wf (a, sz) -> lo <= hi ->
  ForallOrdPairs iv_apart (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  all: repeat first [apply FOP_nil | apply FOP_cons | apply Forall_nil | apply Forall_cons].
  all: unfold iv_apart; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
Qed.

Lemma FOP_maps_subtract : forall l lo hi, ForallOrdPairs iv_apart l -> ivs_wf l -> lo <= hi ->
  ForallOrdPairs iv_apart (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply FOP_app_intro; [apply FOP_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces' a sz lo hi p Ha Hp) as (P1 & P2 & _).
  destruct (maps_subtract_pieces' l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & _).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_apart in *. cbn [fst snd] in *. lia.
Qed.

(* Cutting out an exact mapping [(a, n)] removes it and keeps every positive interval apart from it. *)
Lemma filter_vpos_munmap_cut : forall l (a n : word), ivs_wf l -> 0 < bv_unsigned n ->
  (forall e, In e l -> vpos e = true -> e = (a, n) \/ iv_apart e (a, n)) ->
  List.filter vpos (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) = map_remove (List.filter vpos l) a.
Proof.
  intros l. induction l as [|[b s] l IH]; intros a n Wl Hn Hcond; [reflexivity|].
  apply ivs_wf_cons_inv in Wl as [Wb Wl'].
  cbn [maps_subtract]. rewrite filter_app. rewrite (IH a n Wl' Hn (fun e He => Hcond e (or_intror He))).
  pose proof (u64_range a) as Ra. pose proof (u64_range b) as Rb. pose proof (u64_range s) as Rs.
  cbn [List.filter]. destruct (vpos (b, s)) eqn:Ev.
  - assert (Hs : 0 < bv_unsigned s) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_lt; exact Ev).
    destruct (Hcond (b, s) (or_introl eq_refl) Ev) as [E|D].
    + injection E as Eb Es. subst b s.
      unfold iv_subtract. cbv zeta.
      rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned a))) by lia.
      rewrite (proj2 (Z.ltb_ge (bv_unsigned a + bv_unsigned n) (bv_unsigned a + bv_unsigned n))) by lia.
      cbn [app List.filter]. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
    + unfold iv_apart in D. cbn [fst snd] in D.
      assert (Hsub : iv_subtract b s (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = [(b, s)]).
      { unfold iv_subtract. cbv zeta. destruct D as [D|D].
        - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned a))) by lia.
          rewrite (proj2 (Z.ltb_ge (bv_unsigned a + bv_unsigned n) (bv_unsigned b + bv_unsigned s))) by lia.
          rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
        - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) (bv_unsigned a))) by lia.
          rewrite (proj2 (Z.ltb_lt (bv_unsigned a + bv_unsigned n) (bv_unsigned b + bv_unsigned s))) by lia.
          rewrite Z.max_l by lia.
          replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia.
          rewrite !Z_to_bv_bv_unsigned. reflexivity. }
      assert (Hne : bv_eqb b a = false).
      { destruct (bv_eqb b a) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb. subst b. lia. }
      rewrite Hsub. cbn [List.filter]. rewrite Ev. cbn [app].
      unfold map_remove. cbn [List.filter fst]. rewrite Hne. reflexivity.
  - assert (HL : forall q, In q (iv_subtract b s (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) -> vpos q = false).
    { intros q Hq. destruct (iv_subtract_pieces' b s _ _ q Wb Hq) as (Q1 & Q2 & _).
      unfold vpos in Ev |- *. cbn [snd] in Ev. apply Z.ltb_ge in Ev. apply Z.ltb_ge. lia. }
    assert (Hnil : forall L : list (word * word), (forall q, In q L -> vpos q = false) -> List.filter vpos L = []).
    { intros L. induction L as [|q L IHL]; intros HL0; [reflexivity|]. cbn [List.filter].
      rewrite (HL0 q (or_introl eq_refl)). apply IHL. intros q' Hq'. apply HL0. right. exact Hq'. }
    rewrite (Hnil _ HL). reflexivity.
Qed.

(* No cut makes a zero-size piece out of a positive interval. *)
Lemma zcount_iv_subtract : forall (a sz : word) lo hi, lo <= hi ->
  (length (iv_subtract a sz lo hi) + (if vpos (a, sz) then 1 else 0) <= 1 + length (List.filter vpos (iv_subtract a sz lo hi)))%nat.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  assert (Hv : forall (b : word) z, 0 < z < 2^64 -> vpos (b, Z_to_bv 64 z) = true)
    by (intros b z Hz; unfold vpos; cbn [snd]; rewrite unsigned_lit by lia; apply Z.ltb_lt; lia).
  unfold iv_subtract. cbv zeta. destruct (vpos (a, sz)) eqn:Ev.
  - assert (Hs : 0 < bv_unsigned sz) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_lt; exact Ev).
    destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app List.filter];
      rewrite ?(Hv a (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia;
      rewrite ?(Hv (Z_to_bv 64 (Z.max (bv_unsigned a) hi)) (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia;
      cbn [length]; lia.
  - assert (Hs : bv_unsigned sz <= 0) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_ge; exact Ev).
    destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app List.filter];
      repeat match goal with |- context [vpos ?q] => destruct (vpos q) end; cbn [length]; lia.
Qed.

Lemma zcount_maps_subtract : forall l lo hi, lo <= hi ->
  (length (maps_subtract l lo hi) + length (List.filter vpos l) <= length l + length (List.filter vpos (maps_subtract l lo hi)))%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract List.filter length].
  pose proof (IH lo hi Hlh) as H2. pose proof (zcount_iv_subtract a sz lo hi Hlh) as H1.
  set (IC := iv_subtract a sz lo hi) in *. clearbody IC.
  rewrite filter_app, !length_app.
  destruct (vpos (a, sz)) eqn:Ev; rewrite ?Ev in H1; cbn [length] in *; lia.
Qed.

Lemma zbound_maps_subtract : forall l lo hi, lo <= hi ->
  Z.of_nat (length l) <= Z.of_nat (length (List.filter vpos l)) + 1 ->
  Z.of_nat (length (maps_subtract l lo hi)) <= Z.of_nat (length (List.filter vpos (maps_subtract l lo hi))) + 1.
Proof. intros l lo hi Hlh H. pose proof (zcount_maps_subtract l lo hi Hlh) as C. lia. Qed.

Lemma eager_munmap_exact : forall mo (a n : word), model_ivs_wf mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  (forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
     covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false) ->
  eager_used (mdl_munmap mo a n) + bv_unsigned n <= eager_used mo.
Proof.
  intros mo a n Hwf Hsep Hin Hpos Hnc. pose proof Hwf as (Wm & Wn & Wl & _). pose proof (u64_range n) as Rn.
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  destruct (maps_subtract_sem (vm_maps (m_vmmaps mo)) lo hi Wm Hlh) as (Wr & Sm & _).
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_munmap mo a n)))).
  { rewrite mdl_munmap_vmmaps. cbn [vm_maps]. rewrite <- Elo, <- Ehi. exact Wr. }
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_munmap_vmmaps, mdl_munmap_lazy.
  cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi. rewrite Sm. cbv beta.
  set (l := vm_maps (m_vmmaps mo)) in *.
  set (Q := fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)).
  (* [comment removed for export] *)
  match goal with |- sum_count ?P l + _ <= _ =>
    assert (E1 : sum_count P l = sum_count (fun x => Q x && negb (in_rng lo hi x)) l) end.
  { apply sum_count_ext. intros x. unfold Q. cbv beta.
    rewrite !covered_app, (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh).
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); reflexivity. }
  rewrite E1.
  assert (Hsplit : forall (P R : Z -> bool) l0,
             sum_count P l0 = sum_count (fun x => P x && R x) l0 + sum_count (fun x => P x && negb (R x)) l0).
  { intros P R l0. induction l0 as [|q l0 IH]; cbn [sum_count]; [reflexivity|]. unfold iv_count in *.
    rewrite (zcount_and_split P R). lia. }
  rewrite (Hsplit Q (in_rng lo hi) l).
  (* [comment removed for export] *)
  assert (Hn : iv_count (fun x => Q x && in_rng lo hi x) (a, n) = bv_unsigned n).
  { unfold iv_count, B, S. cbn [fst snd].
    rewrite zcount_true by (intros x Hx; rewrite Z2Nat.id in Hx by lia; cbv beta; unfold Q; cbv beta;
      rewrite (Hnc x ltac:(lia)); cbn [negb andb]; unfold in_rng;
      rewrite (proj2 (Z.leb_le lo x)) by lia; rewrite (proj2 (Z.ltb_lt x hi)) by lia; reflexivity).
    apply Z2Nat.id. lia. }
  pose proof (sum_count_In_ge (fun x => Q x && in_rng lo hi x) l (a, n) Hin) as Hge.
  lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_in_maps_munmap' : forall mo (a n : word), model_ivs_wf mo -> lazy_in_maps mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  lazy_in_maps (mdl_munmap mo a n).
Proof.
  intros mo a n (Wm & _ & Wl & _) H Hsep Hin Hpos iv Hiv Hsz. rewrite mdl_munmap_lazy in Hiv. rewrite mdl_munmap_vmmaps. cbn [vm_maps].
  destruct (maps_subtract_pieces' _ _ _ iv Wl Hiv) as (r & Hr & P1 & P2 & P3).
  destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2).
  destruct (maps_subtract_contains' _ (bv_unsigned a) (bv_unsigned a + bv_unsigned n) e
              (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv)) Wm He
              ltac:(lia) ltac:(lia) ltac:(lia) P3) as (e' & He' & F1 & F2).
  exists e'. split; [exact He'| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem munmap_ok : munmap_node.
Proof.
  intros Σ Σ' PMc Pm K mb len HPMc _ EL Eaw Hsm Hperm' Heg HL Haw Heg38 Hlen Hlal Hmb0 Hal Hend Hm.
  assert (EA : rtA_allow Σ' = rtA_allow Σ) by (unfold rtA_allow; rewrite Eaw, EL; reflexivity).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  apply (ast_munmap_f asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ' mo /\ PMc mo) mb len).
  - lia.
  - exact Hmb0.
  - unfold page_size. exact Hal.
  - rewrite Hrd. unfold TASK_SIZE. lia.
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4). rewrite Hrd. repeat (split; [assumption|]). exact S4.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd.
    assert (Eua : bv_unsigned (Z_to_bv 64 mb) = mb) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (HinR : In (Z_to_bv 64 mb, Z_to_bv 64 len) (rt_maps Σ)) by (unfold rt_maps; apply in_or_app; left; exact Hsm).
    assert (Hin : In (Z_to_bv 64 mb, Z_to_bv 64 len) (vm_maps (m_vmmaps mo))) by exact (artm_in_maps Σ mo _ HA HinR).
    assert (HsepR : ForallOrdPairs iv_apart (rt_maps Σ)) by exact (FOP_perm _ iv_apart_sym _ _ Hperm (FOP_filter _ vpos _ Hsep)).
    assert (Hnc : forall x, bv_unsigned (Z_to_bv 64 mb) <= x < bv_unsigned (Z_to_bv 64 mb) + bv_unsigned (Z_to_bv 64 len) ->
                  covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false).
    { intros x Hx. destruct (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x) eqn:Hc; [|reflexivity].
      exfalso. pose proof (Hcf x Hc) as H0. unfold covered in H0. apply existsb_exists in H0 as (q & Hq & Hqx).
      unfold rt_maps in HsepR. pose proof (FOP_app_cross _ _ _ HsepR _ q Hsm Hq) as D.
      unfold in_iv, in_rng, B, S in Hqx. apply andb_prop in Hqx as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
      unfold iv_apart in D. cbn [fst snd] in D. lia. }
    assert (Hcut : forall e, In e (vm_maps (m_vmmaps mo)) -> vpos e = true ->
                   e = (Z_to_bv 64 mb, Z_to_bv 64 len) \/ iv_apart e (Z_to_bv 64 mb, Z_to_bv 64 len)).
    { intros [b s] He _. destruct (bv_eqb b (Z_to_bv 64 mb) && bv_eqb s (Z_to_bv 64 len)) eqn:E.
      - apply andb_true_iff in E as [E1 E2]. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst b s. left. reflexivity.
      - right. assert (Hne : (b, s) <> (Z_to_bv 64 mb, Z_to_bv 64 len))
          by (intros Eq; injection Eq as -> ->; rewrite !bv_eqb_refl in E; cbn in E; discriminate E).
        destruct (FOP_In_apart _ _ _ _ Hsep He Hin Hne) as [D|D]; [exact D| exact (iv_apart_sym _ _ D)]. }
    split; [exact Hwf|].
    split.
    { unfold map_has. apply existsb_exists. exists (Z_to_bv 64 mb, Z_to_bv 64 len). split; [exact Hin|].
      cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { rewrite overlap_sum_zero; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
      apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq Hb]. apply negb_true_iff in Hb.
      assert (Hne : q <> (Z_to_bv 64 mb, Z_to_bv 64 len)) by (intros ->; cbn [fst] in Hb; rewrite bv_eqb_refl in Hb; discriminate).
      destruct (FOP_In_apart _ _ _ _ Hsep Hq Hin Hne) as [D|D]; unfold iv_apart in D; cbn [fst snd] in D; rewrite Eua, Eul in D;
        unfold B, S; lia. }
    split.
    + 
      split.
      { rewrite mdl_munmap_vmmaps. cbn [vm_maps].
        rewrite (filter_vpos_munmap_cut _ (Z_to_bv 64 mb) (Z_to_bv 64 len) (proj1 Hwf) ltac:(rewrite Eul; lia) Hcut).
        exact (Permutation_trans (Permutation_map_remove _ _ _ Hperm) (Permutation_sym Hperm')). }
      split.
      { apply (artm_res_step mo _ Eres); [rewrite mdl_munmap_vmmaps; reflexivity|].
        intros e He. left. rewrite mdl_munmap_vmmaps in He. cbn [vm_maps] in He.
        rewrite (filter_vpos_munmap_cut _ (Z_to_bv 64 mb) (Z_to_bv 64 len) (proj1 Hwf) ltac:(rewrite Eul; lia) Hcut) in He.
        unfold map_remove in He. apply List.filter_In in He as [He _]. exact He. }
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_limit]; exact Elim|].
      split.
      { pose proof (eager_munmap_exact mo _ _ Hwf Hsep Hin ltac:(rewrite Eul; lia) Hnc) as Hle. rewrite Eul in Hle. lia. }
      pose proof Hwf as (Wm & Wn & Wl & _).
      split; [apply model_ivs_wf_munmap; exact Hwf|].
      split; [exact (lazy_in_maps_munmap' mo _ _ Hwf Hlz Hsep Hin ltac:(rewrite Eul; lia))|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_maps]; apply FOP_maps_subtract; [exact Hsep| exact Wm| rewrite Eua, Eul; lia]|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
      split.
      { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_munmap_vmmaps, mdl_munmap_lazy in Hz.
        cbn [vm_noaccess] in Hz. rewrite covered_app in Hz |- *. rewrite Eua, Eul in Hz.
        apply orb_true_iff in Hz as [Hz|Hz]; apply orb_true_iff;
          [left; refine (covered_subtract_le _ _ _ _ Wn _ Hz); lia | right; refine (covered_subtract_le _ _ _ _ Wl _ Hz); lia]. }
      split.
      { apply (shadow_lazy_cut_nc mo _ mb (mb + len) Hwf ltac:(lia) Hal ltac:(rewrite Z.add_mod, Hal, Hlal by lia; reflexivity) Hsl).
        - rewrite mdl_munmap_lazy, Eua, Eul. reflexivity.
        - rewrite mdl_munmap_vmmaps. cbn [vm_noaccess]. rewrite Eua, Eul. reflexivity.
        - intros x Hx. pose proof (Hnc x ltac:(rewrite Eua, Eul; lia)) as C. rewrite covered_app in C.
          apply orb_false_iff in C as [_ C]. exact C. }
      split; [unfold maps_zbound; rewrite mdl_munmap_vmmaps; cbn [vm_maps]; apply zbound_maps_subtract; [rewrite Eua, Eul; lia| exact Hzb]|].
      apply NodesA_madv.noaccess_pos_munmap; [exact Hwf| exact Hnp].
    + apply (HPMc mo); [apply mdl_munmap_fds| apply mdl_munmap_fs| apply mdl_munmap_reader| exact HPc].
Qed.
