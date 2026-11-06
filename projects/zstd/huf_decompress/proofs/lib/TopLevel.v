(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_TopLevel () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1c49OSSVerify5KrLib8TopLevel9prog_treeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem3Run<in_is_prefixC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC59OSSVerify5KrLib3Lib9RegsEquiv8mkR_initC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC59OSSVerify5KrLib3Lib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_statec49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC4ELinuxProcessSemantics?LinuxProcessSem3Run@valid_entry_sv48C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib5Nodes9minv_initC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapc49OSSVerify5KrLib8TopLevelJvalid_input_either_va_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:entry_atopC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel9frm0_initC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel7tree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel;tree_tracesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree6ttraceC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel;trees_equivC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_map_iffC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6of_natc49OSSVerify5KrLib8TopLevelFin_map_WriteEv_no_killC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC59OSSVerify5KrLib3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>path_is_dirrefC59OSSVerify5KrLib3Lib5Nodes;open_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesI47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeK59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidK59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes:node_inputC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxC4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRC4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYK59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03C46Stdlib5Lists4List9in_app_orI47Corelib4Init5Logic2or00c49OSSVerify5KrLib8TopLevel=nstep_no_killC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appc49OSSVerify5KrLib8TopLevel>ttrace_no_killC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgI4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_cfg00C4ELinuxProcessSemantics?LinuxProcessSem3RunEreaches_unmodeled_cfgK4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior01I4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior00c49OSSVerify5KrLib8TopLevelCtree_traces_no_killC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree@impl_run_traces2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree>impl_run_safe2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeAimpl_run_modeled2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel3ms0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel8mo0_minvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run<bh_unmodeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>dies_by_signalC59OSSVerify5KrLib3Lib9RegsEquivGinit_behaviour_eqv_scfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv7init_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes;nodes_soundC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree:node_sound00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc49OSSVerify5KrLib8TopLevel>mo0_not_haltedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8TopLevel7ms0_svcC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib4Init5Logic5proj1c49OSSVerify5KrLib8TopLevel6run_eqC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes?RelationClasses=iff_Symmetric".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en).

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph22pch32phh44segsp;1p;2p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710R1p9P0p1002bp4p710p9p1003ZR0p4p710P0p4p711R0p8p1004Qp4p70R2p1005?p4p710p8P2p1005Vp4p7210p8P2p10062p4p710p8P2p1006Np4p710p8P2p1007Dp4p710p8P2P0p8P2P1p8P2p1007ap4p710p8P2p1008Zp4p7210p8g0097j1CTg009Wj1BTg00:Ij14Tg00;Dj10Tg00;ij1ATg00<Nj11Tg00<lj17Tg00=Oj25Tg00>Aj16Tg00>_j22Tg00?Ej13Tg00?gj18Tg00@]j19Tg00ASj1@Tg00BHj1<Tg00C?j1;Tg00D3j7:Tg00Dmj1=Tg00Efj7>Tg00FXj2?Tg00G2#Cg00H1g00HOg00IOg00JGg00KAf1R2#BR1#4g00LH#0R0#A#1%00#0#0#0R0#0#1R3#7R4'5f3#6,23%10g00Lm'2%34f2P1f0R1#8%91%@1%<1%;2F:f4#=F>'?W1W0W3W2W4o"). Qed.

(* [comment removed for export] *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp.

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph23limh32pch42phh54segsp;1p;9p;4p;2g0097j1:Tg009Wj19Tg00C?j10Tg00?gj11Tg00@]j18Tg00ASj12Tg00BHj13Tg00MKl94Tg00NJj45Tg00O;j26Tg00FXj27Tg00G2#:g00H1g00HOg00P0g00IOg00JGg00PNf5R0f4f3f1R1#9%01f0R2#1%82%22%32M94P0f2P1P2C5'6'7W1W0W2W4W3W5o"). Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph23limh34segsp;1p;2g0097j16Tg00;Dj10Tg00<Nj12Tg00<lj11Tg00QCj15Tg00?Ej14Tg00FXj23Tg00G2#6g00P0g00IOg00JGg00LH#0#0#0#0#0#0#2#1R0#5%40'3W1W0W2W3o"). Qed.

(* [comment removed for export] *)
Lemma mo0_minv : forall segs pc ph lim en inp,
  valid_entry (mkImage segs pc ph) en inp -> in_va_size inp = Sv48 -> minv (mo0 segs lim en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "p'0h01Hh13Hveh22_Hh34__x1h44__x2h54__x3h63inph72H0h85Hsv48h91Lh:3Vsph;3_H0h<3_H1h=7__arithh>4__ffh?8__varmaph@5__withA3brkhB2drhC2eni002enhD5lemmahE3limhF2mbhG2pchH2phhI4segsi014segshJ2spi022spi034brk0i041ei056en_brki067en_drawi07<en_mmap_basei085en_spi093imgi0:;img_init_pci0;9img_phdrsi0<5mbasep;1p;3p;4p;2p;7p;8p100Qep4p710p1003Zp4p711p8g0097j1HTg00R[j3ATg00SXj3?Tg00TPj1MTg00UIj3DTg00NJj4=Tg00Ucj1@Tg00;Dj19Tg00<Nj1RTg00<lj1QTg00VVj41Tg00WNj1BTg00XCj2:Tg00Y9j16Tg00?gj17Tg00@]j18Tg00Z5j34Tg00[2R0j20Tg00[Mj2XTg00[fj3WTg00\Wj4VTg00]Tj1UTg00^Rj1TTg00_Ej1STg009Wj1>Tg00`>j22Tg00`hj23Tg00aDj1PTg00abj2;Tg00bBj1LTg00bbj2ETg00c@j4NTg00c^j1KTg00d<j1OTg00dgj2CTg00;ij1JTg00eJj4GTg00?Ej1bTg00f5j7aTg00fYj2`Tg00FXj2_Tg00g;j2^Tg00ggj3]Tg00hFj4\Tg00i8j7[Tg00j0j7ZTg00jTj8YTf0R1g00k8R2'3p=5g00P0R3g00LmR47D1p=<f1R5g00l3R6g00lRR7P7g00m2R8P1g00mRFZp=Ff3R9P6P7P7P8f2R:P5P1GYp=Ig00G2#Hg00H1g00HOg00IOR;P;g00JGR<f6R=f5R>f4R?3A??51g00n2%M5g00ni3DR@f8RAP>P9P:C=#@[[]6P1g00LHRB#9RC#9#9#9RD#9#9#RRE#QRFg00o`f=RGf<RHf;RI3AP?P9P:P5C1;?1f?RJf>RK;AGRLP=P>P?P9C1RM;?:g010`RNp-0ROPLP;POf9RPPAf7RQP=C1%B9RR1:=:RS%65RT%7P%8P549'0'0'0n0110000014010210310<106n0110900013010110:10;RU'Xf@RV?AJKRWPQP=P>P?C1;?9PNPOPWP;POf:ROPPPAPQC1%7OR;%8ORW549,0T,0S,0Rn0110000014010210310<106n0110900013010110:10;;W1WDPLPMP:P1CVP5O2PUP0%BQ1:V=%6>%79%8954Q'0'0fARUPKPAPQP=P>C1P?C=#@P1%BPfCR>/:P%6A%7=%8=54O'0'0P0fDRM/:O%6P%7Q%8Q54I'0fERQfBRLPHPIPOPPC1PAC=#@P1fFRA/:H%6HA4K;W'0P0%6G%7I%8I54JfIRIPAPVPJPKPGC1PHC=#@P1%6J%7K%8K54LfLRK#UP>PLPUPVC1RV#T%SV%>VPIPJP0g011]RJ12E>RV'3%5V%PDRD,;V#<'0PMP>PLPUC1#>,2ERU,3J%5U'0PP12EQ,3J12EARP#51;PD#<'0P0fGR0,2ERP#51;PD#<fHRPP0PAPQC1#>,2ERQ,3J%5Q'0P112EI#5fJRQ,2E/;D#<g012XRD#L%HDP31E3:P51E39CN%K3%O3RDP31C3CRCg013DRA%JB,C3CG,FDR0%b7RUPDP31C3BPAPCCG,FDRCPUPDP6P7P7P8PCP0FaCICI1`D8P1P:g013kRDg014KR8'_1^1:=DD8dA]345C\b>b?b@X33X43X53135:R413:9139?'0\4[^33^43^53P1P212EKPJP:P=O5b=fKPQPIPPC1#>,2ERE,3J%5E'0eW2W0P5P1O2n2001000000121000000W7W9P5P1O2n2001000000121000000F[W<W;P5P1O2n2001000000121000000W0W2P5P1O2n2001000000121000000W0W:P5P1O2n2001000000121000000b1X8@W1X6<WBXFFXAFWJP9P:P5P1O4n01104000141108105107106WCXE3WHWGWIo"). Qed.

(* [comment removed for export] *)
Lemma valid_input_either_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02H0h11Hh22_Hh33_H0h43_H1h53_H2h63_H3h73_H4h83_H5h93_H6h:3_H7h;3inpp;1p;3p;2g014kj1LTg00?gj1ETg015jj1CTg00@]j19Tg016aj1?Tg017Xj16Tg018Lj17Tg019@j15Tg01:8j1<Tg01;2j1;Tg01;lj1KTg01<fj1JTg01=bj1BTg01>Zj1DTg00BHj1=Tg01?Sj1>Tg00TPj1@Tg00UIj3ATg00[2R0j20Tf0R1#K#Jp=4f4R2#B#Df3R3#<f2R4#=#>g00n2R5f1R6#@g00niR73A%;1'0'0'0'0p=21061,04p=3%@1=A57p=1%56/01p=:%B1#Dp=I%@6=A57%;1'0p=8%<4%=6#>/01'0p=H%=6#>/01p=G%=1#>p=Fg00JG%L1P0%E6#C%96#?%66#7%46%56P6P6P6P6P6D23333%14P1%E3#C%92#?%62#7%42%52P2P2P2P2P2D23333P0f5R2#9#?%62#7%42P2P2P2P2P2D2,:233f6#1P1f7#9#?f8R2#6#7%42P2P2P2P2P2D2,:233P0f9R2#6#7%42%52P2P2P2P2P2D233f:#1P1f;#6#7f<R2#4%52P2P2P2P2P2D233P0f=R2#4P2P2P2P2P2D2,:2f>#1P1f?#4f@R2P2P2P2P2P2D2':P0fAR2#5P2P2P2P2P2D2fB#1P1fC#5fDR2P2P2P2P2D2P0fER2#I18229H22fF#1P1fG#IfHR218227H2P0fIR2#<1822,G2fJ#1P1fK#<fLR21822'GP0fMR2#F1822fN#1P1fO#FfPR2/82P0fQR0#1%;0fR#1P1fS#1fT#;P6W:W1P6P1O2n2001000000120000000W0W9P6P1O2n2001000000120000000W0W8P6P1O2n2001000000120000000W0W7P6P1O2n2001000000120000000W0W6P6P1O2n2001000000120000000W0W5P6P1O2n2001000000121000000W0W4P6P1O2n2001000000121000000W0W3P6P1O2n2001000000121000000W0W2P6P1O2n2001000000121000000W0W;o"). Qed.

Lemma valid_entry_either : forall segs pc ph sp brk mb dr inp, valid_input_either inp ->
  valid_entry (mkImage segs pc ph) (mkEntry sp brk mb dr) inp <->
  (valid_sp sp /\ valid_brk segs brk /\ valid_mmap_base mb /\ entry_stack_fits sp (in_argv inp) (in_envp inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h03brkh12drh23inph32mbh42pch52phh64segsh72spp;1p;3p;4p;2g0097j18Tg00;Dj10Tg00<Nj12Tg00<lj11Tg014kj17Tg00R[j36Tg00VVj43Tg01@Kj24Tg00\Wj45Tg00G2#8g00H1g00HOg00LH#0#0#0#0#0#0#2#1R0g00o`g00JGf0R1#7f8f7f636f5f4f3f2C3f1R21421C5UW2W1X30X00W7W5W4W6o"). Qed.

(* [comment removed for export] *)
Lemma mo0_vm_init_sp : forall segs lim en inp, vm_init_sp (m_vmmaps (mo0 segs lim en inp)) = en_sp en.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph23limh34segsp;1p;2g0097j15Tg00;Dj10Tg00<Nj12Tg00<lj11Tg009Wj14Tg00FXj23Tg00G2#5g00P0g00IOg00JGg00LH#0#0#0#0#0#0#2#1f1#4'3W1W0W2W3o"). Qed.
Lemma mo0_alloc_top : forall segs lim en inp, alloc_top (m_vmmaps (mo0 segs lim en inp)) = entry_atop en.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph23limh34segsp;1p;2g0097j12Tg01ASj11Tg00FXj20Tg00G2#2g00P0R0g00IOg00JGf1#1,00W1W0W2W3o"). Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph22pch32phh44segsp;1p;2g0097j16Tg00;Dj10Tg00<Nj12Tg00<lj11Tg00QCj15Tg00?Ej14Tg00FXj23Tg00G2#6g00H1g00HOg00IOg00JGg00LH#0#0#0#0#0#0#2#1R0#5%40'3W1W0W3W2W4o"). Qed.

(* [comment removed for export] *)
Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "p;2g00FXj20Tg00P0g00Lm'0o"). Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02enh13inph22pch32phh44segsp;1g0097j10Tg00G2#0g00H1g00HOg00IOg00JGg01BNW1W0W3W2W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input_either inp ->
    trace_equiv (tree_traces (tS inp enS) (mo0 segsS source_alloc_limit enS inp))
                (tree_traces (tT inp enT) (mo0 segsT target_alloc_limit enT inp)).

(* [comment removed for export] *)
Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
  trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
  intros RS RT tS tT moS moT H tr. unfold tree_traces.
  split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma in_map_WriteEv_no_kill : forall fd l sig fs, ~ In (KillEv sig fs) (map (WriteEv fd) l).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "p'0h01xi001xh11Hh21lh31Ah41Bh53Hinh61fh71yh82Hxh92_Hh:1ei011eh;2fdh<2fsi022fsh=3sigi033sigi041bi052chi064codep;1p;2p;4p;3p;5p;6g00;Dj15Tg00<Nj1;Tg00<lj19Tg0097j18Tg01Oij21Tg01P_j1:j24Tg005Vj47Tg01QUj30Tg00UIj32Tg00[2R0j23Tg01IKR1j26Tg01Qlj5<Tg0062j6?Tg01RKj2>Tg01Rjj1=Tg00LH#5#5#5R2#5#5#5#;#9R3%;2#9R2#8g004Qg01N=R4f1R5f0R6'1P2P4f3R7#:f2R8C730R9g008ZR:p4p710R;P:p4p7210R:P5\5R<%88R=P0f4R>P7P8P5C79076f5R?P>P6O1=2?8f6R@?067'3X0?'6[RAP7P6O1=2>5A0?68'3X0>,6>P?P>P7P8C790>5RB[P?P6O1=2@7f7RC?06>'3X0@,6@\BP>P7P8P5P6D<P5n2001000000120000000X78W2W6W4W3PA^78^2=^6<^4:^3;P6P2P4%:?P>1178P5O614@611>7524A026?'3X02,62P1P214C611?>524A026@'3X02g01SCR1P6f9R8/4611C@524f8R@9026'3P0f:R0/4511@C524A0258P1P6f<R@/471108524A02>@P4f>/4?P4p-0P6P1g01S`P1P1n01101000420105104201051042010610220103102X:4g01T<f;,1@P5E?P11>16b1W9W8P5P6O2n2001000000120000000W1X02P5P6O2n2001000000120100000b5b1W5%=9eW<X=3W2W;o"). Qed.

Lemma nstep_no_kill : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> forall sig fs, ~ In (KillEv sig fs) evs.
Proof.
  intros n mo eff mo' evs Hst sig fs.
  destruct n; cbn [nstep] in Hst.
  - destruct Hst as (k & _ & _ & _ & ->). apply in_map_WriteEv_no_kill.
  - destruct Hst as (_ & Hst).
    destruct (Z.of_nat (length (concat bufs)) =? 0).
    + destruct Hst as (_ & ->). intros [].
    + destruct Hst as (k & _ & _ & ->). apply in_map_WriteEv_no_kill.
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
Qed.

Lemma ttrace_no_kill : forall {R : Type} (t : itree node R) mo tr,
  ttrace nstep nexit t mo tr -> forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo tr Htr sig fs.
  - cbn in Htr. subst tr. intros [].
  - cbn [ttrace] in Htr. destruct Htr as [(code & mo' & _ & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + intros [H | []]. discriminate H.
    + intros Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (nstep_no_kill _ _ _ _ _ Hst sig fs Hin).
      * exact (IH rsp mo' tr' Htr' sig fs Hin).
Qed.

Lemma tree_traces_no_kill : forall {R : Type} (t : itree node R) mo tr,
  tree_traces t mo tr -> forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros R t mo tr (full & Hf & Hp) sig fs Hin.
  exact (ttrace_no_kill t mo full Hf sig fs (in_is_prefix _ _ _ Hp Hin)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run_scfg ACFG (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg segs ACFG c0;
     bh_errors := reaches_error_cfg segs ACFG c0;
     bh_all_errors := all_traces_error_cfg segs ACFG c0;
     bh_unmodeled := reaches_unmodeled_cfg segs ACFG c0 |}.
Proof. intros segs pc ph lim [sp brk mb dr] inp. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ dies_by_signal (run_scfg ACFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Hve Hsv48 Himpl Hleaves Hsafe.
  pose proof (mo0_minv segs pc ph lim en inp Hve Hsv48) as Hminv.
  rewrite run_eq. cbn [bh_traces bh_errors bh_unmodeled].
  destruct (init_behaviour_eqv_scfg ACFG segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (mo0 segs lim en inp))
    as (Htr & Herr & _ & Hunm).
  change (init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) with (ms0 segs pc ph en inp) in Htr, Herr, Hunm.
  pose proof (nodes_sound segs) as NS.
  assert (HTR : trace_equiv (obs_trace_cfg segs ACFG (mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp)))
                            (tree_traces t (mo0 segs lim en inp))).
  { intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_traces2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)). }
  split; [exact HTR| split; [| split]].
  - rewrite Herr.
    apply (impl_run_safe2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Hunm.
    apply (impl_run_modeled2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
  -
    intros (tr & sig & fs & Hb & Hin). cbn [bh_traces] in Hb.
    apply (proj1 (HTR tr)) in Hb. exact (tree_traces_no_kill t _ tr Hb sig fs Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h01Hh12T1h22T2h32trp;1p;2p;6g0097j12Tg01JZj20Tg02mmj61Tg01N=#2R0p-0R1[R2f1R3f0R4'0P1g00[Mg02nXf3P4O1f2R1P4O1P3P4O1E1X301031eW0X22W1o"). Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevel ()) [] "h02H1h12H2h22T1h32T2h42T3h55lemmah62trp;1p;2p;9g0097j14Tg01JZj20Tg00[MR0j22Tg02bDj21Tg02c0l93Tg01N=#4R1p-0R2[R3f2R4f1R5'0R6f5R7f0R8O1f4R9P8O1'2P2P0g02lFf6P5O1P7P5O1P8P9P5O1R7P71127M93W5P4P8O1P5P8O1O2X611094eX16W0X43X33W2o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.zstd.huf_decompress.images Require Import Plain.

Module SrcImg := Plain.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
