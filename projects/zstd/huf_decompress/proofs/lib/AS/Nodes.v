(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim CatSim FileSim ShapeAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Nodes () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesK47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib2AS5Nodes7halt_evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputI47Corelib4Init5Logic3and00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesI47Corelib4Init5Logic2or00C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsEcheck_syscall_err_iffC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00c59OSSVerify5KrLib2AS5NodesBsstep_cfg_of_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5NodesEsstep_cfg_svc_inv_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg<sstep_of_cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes;node_chk_evC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib2AS5NodesDuniform_not_spuriousC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib2AS5Nodes?node_chk_ev_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes8node_chkC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledc59OSSVerify5KrLib2AS5Nodes8node_detC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS6CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeMcheck_ret_only_copyins_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeScheck_ret_only_copyins_no_unmodeledC59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes=node_ret_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg8rz_emit1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5NodesEnode_ret_only_copyinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes6open_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib3Cfg:alloc_no_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7FileSimIcheck_open_result_copyinsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdc59OSSVerify5KrLib2AS5Nodes7open_nxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgGtransparent_nonalloc_noC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00K47Corelib4Init9Datatypes3sum01C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib2AS7FileSimPcheck_open_result_copyins_ok_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Nodes>sstep_of_checkC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif3sig01K47Corelib4Init9Datatypes3sum02C59OSSVerify5KrLib2AS7FileSimYcheck_open_result_copyins_never_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC46Stdlib5Lists4List2InI47Corelib7Numbers7BinNums1Z00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I47Corelib4Init9Datatypes3sum00c59OSSVerify5KrLib2AS5Nodes9node_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC59OSSVerify5KrLib2AS7FileSimGENOMEM_in_openat_errnosC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) ["WithSegs"] "p'0h03effi003effh11Hh23evsi013evsh34codei024codeh47model''i037model''h56model'i046model'h62H1h72H0h82H2h92H3h:2H4h;3Hssh<2H5h=1mh>2H6h?1oi051oh@1ehA4HsvchB1li061lhC1si071shD6model0hE3ms0hF2sthG2x8i082x8hH1bi091bhI2x0hJ3HhchK1ihL2H7hM2e0hN3HeqhO2m'hP1ci0:1chQ5modeli0;5modelhR2msi0<2mshS3ms'i0=3ms'hT3sigi0>3sigi0?9cfg_modeli0@6cfg_msi0A1xp%0p%1p%2p%3p&0p;1p;2p;3p;4p;6p;7p;5p;8p10000p4p70R0g000`R1p4p710R2p8P0g001<R3p4p710R4p8P0P3p4p7210R5p8P0g001YR0p4p710R6p8p10027p4p70R7P2p8P7P4p8P7P5p8P7P6p8P7g002eR7p4p710p8p1003Bp4p7210R8P2p8P8P4p8P8P5p8P8P6p8p1003np4p70R8P2p8P8P4p8P8P5p8P8P6p8g004dk104Tg005Ik10ZTg005gk10VTg006Jk10TTg006jS00k10YTg007Lj1KTg008Rj2:Tg0094S01j30Tg009Nj27Tg00:CR6j4>Tg00;7j2oTg00<Aj1WTg00=8k10WTg00=Zj1iTg00>`k10ATg00?@k20@Tg00@5j21Tg00@Ok20ITg00@ok10\Tg00B7j3cTg00C3k20CTg00D;j38Tg00E1S02j22Tg00ELj1XTg00FBj3HTg00GOk40MTg00Gkj6eTP1j6Ej7[Tg00HIk20PTg00Hhk10aTg00J0k10`Tg00K8j2kTP3j6vTg00L1k203Tg00M:j2=Tg00MTk50]Tg00Nhj2ITg00OBj4pTg00O]k300TP0k809j6`Tg00P7j3~Tg00PQj1^Tg00QHj1ATg00R;j3yTg00S6k20GTg00Slk20FTg00Tbk20hTg00Ujk10gTg00Vbk20fTg00WHk60eTg00XFk30cTg00Y[k10RTg00ZXj3wTP7k306Tg00[8k40bTg00[Xk40XTg00\Pk40QTg00\jS03f1R7f0R030p=Vg00]_R3?070p=Qg00^UR1/:0p=|f3R8f2R50037;00p=g1k70$0Rp=f1770#X9035,28p={f4R4A0857/20'2p=<%W7=050p=JA0485g00_KR29030,27'2p>05g00`AR9Aw9708065p>0>1770#X9035p=r111412851170'='=p>0Kg00a7R:f6R;f5R<;84?H85;07/20p=Y1110p=3A0302p=9A0857/20p=DA8<48?H57g00bAR=50:/20p=Ug00cKR>/1711>0'=p=4g00dIR?P1P7P0H0bp>07%X7=030p=}Q03P1P8P5P7P0Evp>0DA0170p=MQ03P?P8P5P7P0Evp>0:A0?70p=OAH857=0:0p=B1k57$0R/70#Xp=;A0370,25p>0B1770#Xp=5f7R@111;A0485/27,2</=0'='2p=SAH570=0:=p=C1270,25p=6A0<48A0370,25'2,2;p=@A0302,27p=NA0485A0370'2,2<p=?1757#X=030p=nA0370,25,28,24p=ZA0370,25,28p=]111;1285,24,2<1170'='=,2@p=m%K7=050p=T11181170,=5'=,24p=R%X0=032p=uAH@;<=0:411181257/=0'='2p=lA0:7=/20p=zP1P4P8P5P7P0E`p=tP?P4P8P5P7P0E`p=sA0320p=\111<1285,241170'='=,2;p=dA0320,27,25,28p=FA0320,27,25p=GP3P2P4P8P5P7P0F[p>0OP3P2P8P5P7P0EEp>0LP>P5P7P0H0X9y48p=a&0R7/70p=x%i0-037p>02111<1257,28,24/=0'=p>0N11>0p=b1257,28,24/=0p>0UA0:851117/=0'2p>0120@57=w90p>0<B06970p>0_1285,24,2<1170'=p>0;B069709085p=jA0:70p>0^P;P<P4P8P5P7P0CpH0Qp=qP;P<P4P8P5P7P0H0QH0Qp>0JP>P5P7P0H0Xp>08A8485?y70p=h1117/=0p>0=1170,=5p>0H1o7090:5p>0S20G57=w90p>0?B06957=080p=_20G57=w90:0698p=PAw970p>0[20F57=w90p>0E20F57=w90:0698p=L%X09037p>0iA0:0=p>0dg00eP$04$04$04S04$04$04$04$0ZS05$0VR=&0T9R:&0Y=RA%K4S061:=5S0730p,4segsRB17<4S08P5P7C>P6PBf:S09f9R6'7S0:,V8f8RC90:81Q8CPBf@RDf>S0;P5f?S0<1o70RE%W5RF&0W=RG50ARHP:Q0;P7&0Y1RIP5%i8%|0S0=CgRJf=RKfARL/f8P0C{D<X41AJA7GRMP:PK&0A9RNPIP7%i5&0W1S0>CgROf<S0?I05P=1:=0S0@90AFRFP:Q0;20@50>0>7NRPArKL5D<X3=I0KFYX2:,1:X51#3X0>PBQ0;Q0?P0PKP:f;S0APNQ09#9CDEUX0>'4[[[P0Q06=0AGRQ20I?1RR$0\RSAcB<420785-0CR3017;<S0BfDRTfCRU'7S0C'VfBRV90:NQ0B/}V176CS0DfGRWfFRX'7S0E'VQ03Q03P1P0P0n0110:00012010@10?WMS0FQ0:fHRY/7WRZP0H0D1M6WQ03Q03P?P0P7n0110:00012010@10?WMS0GQ0AQ09'7S0HfIR[/7YR\P7H0:Q0A/O[Q0?fJR]'OP0fKR^,OKfLR_Q0;/M_R`A0:N^RaQ0<Q0;'7S0I/}^AJALGAcB<U207VL-0CR50SfVRbfTRc58BRdP5fURePECBS0JPHP:PcP7fSRffWRg?;80S0K60BJS0LD<X41PMP:PfPNfRRh#9Ri,2OS0MPFP:PcPP15g5S0N,QfS0OD<X3=,1=GSX2:,1:X51#3X0>A8BchS0P?C0fS0QfQRj=0:NS0RfPRk#9S0S36X0>'4]6^7Q]1]:]9[X=?1MK^P0P`fMR`A0:N_RlQ0<,7DRm/}_Rn%KhS0T=0AGAcBf4207UV-0CR50SA8BgeRoP5PbPECBS0UPHP:PeP7PJPcfXRp?;80S0VF@X41PMP:PcPN1NOfPFP:PePPPc15p5S0WE?X3=,1=GSX2:,1:X51#3X0>A8BefS0X?C0cS0YA0:hNS0Z%9jS0[36X0>'4]6]7^1H]:]9X=1P0PlP:PNAnLD`RlAJAjGRq%KfRr=0AGRsAcBcf207TU-0CR50SRtA8BpbRuP5PgPECBS0\PHA0:C7S0]PJPefYRv?;80S0^DZX41PMA0:@NS0_PO%9cP=PFA0:CPS0`Pe15v5S0aC]X3=GmX2:,1:X51#3X0>ACd0eS0bA0:<NS0c;6iX0>'4]6]7]1]:XB:P0PlP317VLS0d#X%WhS0e=0AGS0fATAcGAcBecfERl007T-0CR50SA8BvgRiP5PpPECBS0gPHA0:N7RdPJP@fZRw?;80S0hDZX41A0:NNRx%9;S0i,2O56MS0jP=PFA0:NPRyP@15w5S0kC]X3=DRX2:,1:X51#3X0>ACo0bS0l1Nx4S0m'2X0>'4]6]7]1XC3P:PNPB17beRoP0PhC>A8BwpRzP5PvPEPHPdPJ15^]R{f[R|?;80DZX41PM17][#uR}96xOAr{|596FyX3=,1=GlX2:,1:X51#3X0>AHu0g%XZ,Nx'zX0>'4];X@:PB17ecS0nPNPjC>P317XlS0o#XRZPB17gbPNP0C>A8B|vP5PwPECBS0pPHPdPJ17_^S0q#XRuf\R~?;80S0rDZX41PMPxPO%9{P=PFPyPu15~5S0sC]X3=GmX2:,1:X51#3X0>ACi0pS0t%u\76xX0>'4];XF3PBPoPNPZC>PAPG%KgRZ1:=eS0uPAPZPGP8H0MRoPAPZPGQ0uP8PAPG%WbS0vQ0uPAQ0vPGP4H0MPAQ0vPGQ0uP4PAPGPZQ0uPoPhEeEeEeEeEeQ0u90AGPAPGQ00P=p-0P0g00f5S0wg00fRn10110500021000000X@AS0xg00fnS0y1:=bS0zP0EEQ0wA8B~wP5P|PECBS0{PHPdPJ15`_Rof]RZ?;80S0|DZX41PMPxPO%9uP=PFPyPo15Z5S0}C]X3=GmX2:,1:X51#3X0>ACz0vS0~?6x}X0>'400P0b1bNW;PhP<P0F[W;PhP;fOR}F[X<tX8sX6qfNRqP0EEb6X:nP`P0EEb6X9aQ0<P0Dtb6W7Q0;P0Dsb7W1P0O1b1P0O1b1W8P5P7P0P<P4P8O6W:W9W8W6W7X1HX51XS?XD1XE?P;P<P4P8P5P7P0O7AJA0GS10ATA5GS11AcB85S12&0aRRa50S1748/VmS13Q0;90:NS14Q0;#\S1517@;S1617UV'VS17Q0F17C@S18Q0CP0H0DS0C1M@US19Q0GQ0D17lTS1:P7H0:S1;1O6lS1<Q09/OXS1=P0Q0A/OWS1>PYQ0?/MYRnA0:NWRs%\WS1?Q0<=JAGS1@AcB<LS1A=0SaA8BhkRtP5PjPEPHP:PkP7PJP}1ff8P0C{D<X41PMA0:}NS1B%9qS1C76OPFP:PkPPAr}f5D<X3=,1=GlX2:,1:X51#3X0>PBPkPqP0P}P:P`PN%9_CDEUX0>'4S1D]6^7Q]1]:]9[X=?Q0A/MWS1EP0PnP[A0:NYRz%\YRoATAqGS1FAcB}4S1G=0SaA8BfjRuP5PhPEPHP:PjP7PJPk1fc8P0C{D<X41PMA0:kNS1H%9}S1I76OPFP:PjPPArkc5D<X3=,1=GlX2:,1:X51#3X0>PBPjP}P0PkP:PqPN%9`CDEUX0>'4S1J]6]7^1H]:]9X=1P0PzP:PN%\[S1KAJA`GR\ATA}GRiAcBk}S1L=0SaR{Q0PP5PfPECBS0PQ0]PJPj1fe8P0C{S1M56HX41PMQ0_Q0S,2OS1NP=Q0`Arje5S1O56FX3=FdX2:,1:X51#3X0>ACt0jS1PQ0cQ1C36X0>'4S1Q]6]7]1]:XB:P0Q1KAJAqGS1R%KkS1S=0AGS1TAcBjkRt=0SaQ0XP5PcPECBS0XPHPdPJP@A;b80S1UDZX41Q0jP=PFPyP@15b5S1VC]X3=DRX2:,1:X51#3X0>ACu0hS1WQ0m'2X0>'4S1X]6]7]1XC3P:PNPB17hjRuP0PqC>Q0JPHPdPJQ0KCFX41A0322S0K,2O96MxS1YP=Q0N9GFyX3=DRX2:,1:X51#3X0>Q0QQ0K,2xRa'2X0>'4];X@:PB17jkS0NPNP`C>PB17fhS1ZPNP0C>Q0UPHPdPJQ0VCFX41Q1YP=Q0W9GFyX3=DRX2:,1:X51#3X0>Q0Y/2aX0>'4];XF3PBPuPNP2C>PAPGPr1:=jS1[PAPrPGP8H0MS1\PAPrPGQ1[P8PAPGQ0eQ1[PAQ0ePGP4H0MPAQ0ePGQ1[P4PAPGPrQ1[Q1\PqEeEeEeEeEeQ1[90AGPAPGQ0xQ0y1:=hS1\P0EEQ0wQ0\PHPdPJQ0^CFX41Q1YP=Q0a9GFyX3=DRX2:,1:X51#3X0>Q0b/2aX0>'4S0b00P0b1bNW;PqP<P0I0OW;PqP;P^F[RrX<{X8iX6\P]P0H0Lb6X:oP[P0EEb6X9sPKP0Dtb6W7Q0?P0Dsb7W1P0O1b1P0O1b1W8P5P7P0P<P4P8O6W:W9W8W6W7W1XD1XE?P4P8P5P7P0O5Q10Q11Q12&0`RRR50SQ13Q14Q15Q17Q0CQ19Q1;Q1<Q1=P0Q1>PYQ1?Q1@Q1A=0SRQ1D]6^7Q]1]:^9s\nX=?Q1EP0PnP[Q1FQ1G=0SRQ1J]6]7^1H^:o^9zX=1P0PzP:PNQ1KQ1L=0SRRzQ1Q]6^7i^1\]:XB:P0Q1KQ1RQ1TA0StRQ1X]6]7]1XC3PrX<zX8iX6\P]P0H0Lb6X:oP[P0EEb6X9sPKP0Dtb6W7Q0?P0Dsb7W1P0O1b1P0O1b1W8P5P7P0P<P4P8O6W:W9W8W6W7W1XD1XE?P4P8P5P7P0O5%W<S10=0AGS111:=<9TA@S13A8BC;S14P@P<P4P5DaQ11PIP;%i@%|<CgQ0H17q`'VS0HA0:;_Q09,kK/xC/}_Q0;/7KS15Q0N'VS17Q0FQ0IPuP0H0DS1=Q0;/MjS1EQ0GPmQ1ZP7H0:S1R1ODfS1T1OLcS1XP01OVeS1QPb1MUbS1LQ0<=0:eS1F1k5U/xL/}e%WXS1J=0AGS1GQ061:=XS1?50AS1@A8B<WS1DPYPXPlPUDaQ1G202WYS1A%|X50IfbRmf`Ru58BRsP5faRoPECBS1>PHP:PuP7f_R\fcRi?;80S1<60BJS1;D<X41PMA0:\NRzf^Rr#9S19,2OS0CP=PFP:PuPP15i5S12,Q\S0aD<X3=FdX2:,1:X51#3X0>A8BurS0^?C0\S0\A0:ZNS1]%9~S1^36X0>'4S1_]9]8]6]7]1]>]<[X=?1MVeS1`P0Q1LPgA0:DbRR1kwT/xV/}bS1a%K~S1b1:=WS1c50AS1dA8BZYS1eP4PWPXPTDa%WWS1f=0AGS1g202Y[S1h%|W50IA8BioRtP5PmPECBS1iPHP:PoP7PJPufdRS?;80S1jF@X41PMA0:uNRnPO%9\P=PFP:PoPPPu15S5S1kE?X3=GmX2:,1:X51#3X0>A8Bo\S1l?C0uS1mA0:rNS1n%9ZS1o36X0>'4S1p]9]8]6]7^1H]>]<X=1Q1FP0PRP:Pg1k|l/xU/}gRRAJA|GS1q1:=YS1r9TAZS1sA8Br[S1tPZPYPWP8Da%WYS1u=0AGS1v202[]S1w%|Y50IS1xA8BSmRQP5PiPECBS1yPHP:PmP7feS1z?;80S1{:0BJoS1|D<X41PMA0:oNR{1NOuS1}P=PFP:PmPPQ1z/55S1~,QoS20D<X3=FdX2:,1:X51#3X0>ACs0oS21Q1976zX0>'4]9]8]6]7]1]>XB:Q1aP0PRP3A;~XTAJA~GS221:=[S239TArS24A8B\]S25PrP[PYP~Da%W[S26=0AGPIP]%i^%|[CgQ1z=8BiS27P5PSPECBS28PHP:PiP7ffRR?;80S29:0BJ6S2:D<X41PMP:PmPN1NOCS2;PFP:PiPP15R5S2<,Q6S2=D<X3=,1=GSX2:,1:X51#3X0>ACt0mS2>Q0i76nX0>'4]9]8]6]7]1XC3Q1qQ1sQ1tPZPYPWP|DaQ1vQ1xP3A;o^[RnPB17moS2?P\P0C>A8BRSS2@P5Q1zPECBS2APHP:PSP7PJfgRt?;j}RzA;t80S2BF@X41PMA0:iNS2CPO1kRk/xq#uS2DP=PFP:PSPPPz15t5S2EE?X3=GmX2:,1:X51#3X0>ACQ0iS2F1kSq/x_#u76{X0>'4];XF3PB17ouS2GPrPnC>PA%Km1:=qS2H90A0S2IX?AS2JP41:=uS2KPZEEQ2K1:=`S2L50AQ01PA1:=oS2M1:=kS2N90A7S2OfiRn=8BtP5fhR{PECBS2PPHP:PtP7PJfjRQ?;chS2QA;Q80S2RF@X41PMP:PRPNA;nfjS2S,NOPFP:PtPPQ2Q15Q5S2TE?X3=,1=GSX2:,1:X51#3X0>Q1z98BtS2U?C0RS2VP:PSPN%9zD<X0>'4[P0Q2MQ2H50AS2W1:=mS2X1:=}S2Y50AS2ZPAP=Q00P=P=P0P0PSn10110500021010900XMA1:=iS2[Q2NP0EvA0=ikA0=SjS2\P0Q1z=0=hS2]P=PfPBflRzP8P5fkRsPEPHA0:Q7S2^PJfmS2_/fgS2`/5eS2aQ2_?;80S2bDZX41PMA0:nNS2cPO1fzbS2d/5cS2e#9S2fPFP:PQPPQ2aQ2_/55S2gE?X3=,1=S2hJ0NFYX2:,1:X51#3X0>PBPQP7P0PnA0:tNS2iQ2Q#9S2j'2EUX0>'4XH=P=Pf%KnS2kQ0@50A1:=7S2lQ0u50AS2mfnS2n=8BvP5Q2_PECBS2oPHP:PzP7PJfoS2p?;vgS2qQ2p?;80S2rF@X41PMP:PsPNQ2n/fpS2s/5bS2t,NOPFP:PzPPQ2qQ2p/55S2qE?X3=,1=GSX2:,1:X51#3X0>A8BzgS2u?C0sS2vQ2cQ2f36X0>'4]8]AXG=%K{S2w1:=fS2x50A1:=cS2yQ2y50AS2zQ2_=8BpS2{P5PzPEPHP:PsP7PJQ2tQ2n?;80S2|F@X41PMP:PQPNPOQ2aI05PFP:PsPPQ2tQ2n/55S2tE?X3=,1=GlX2:,1:X51#3X0>S2}#bA8BsbS2~?H0QA0:{NS301fseS31/5fS32#9S33'2'zX0>#bP>Q2}PcP1Q2u?HbsS2}PEPHQ2^PIP5%igS2^Q0=CgS34Q2aQ2`/50S2`DZX41PMQ2cPIP7%ibS2cQ0>CgS2aQ2fQ2hI0UH01X2:,1:X51PfP:Q2~?HeQS2h1oc0S2f%WeS35=0AGS36P:PnP7Q2c-03eS37Q0=50IS38Q2eQ2d/50S2dF@X41%WcS39=0AGS3:Q30%ieS30-03cS3;Q0>50IS3<Q33P=Q35Q0@50AS33P:PnB0<e0NS3=-0_7S3>Q2e15zeS2eE?X3=J0;H01X2:PtA8BQePcPn1oftCBQ3:P:P{P{Q3;Q0=50IS3;Q32Q31P0C{D<X41S31#3S3?%WfS3@=0AGS3AQ2i202fcS2iQ0>50IS3BQ2jP=Q39Q0@50AS2jP:P{P{B0<c0NS3CCjQ3215scS32C]X3=J0;S3D'=g00gJS3EQ02AH485S3F00^EP<P8P4P5P7DaS3G[P4P5P8P7P0DaP<P4P81o57CB[S3HQ3GP;P<P41o85CB[P4P8P5P7P0I0]P0n2001000000120000000X2:XO1X=1X0>WKS3GQ3EQ3H^2:^O1^=1^0>]KS3HP0Q2~PePQPcP{Q0?O6b1Q3?Q3DP1Q31PhQ3AA0:ttS31Q2i%|h50IS2~Q2QQ2Q'QS3I'2S3J'2Q09Q31Q3J1I:tQ2~Q3IP6Q2Q,I3CpCpFq400FqK0J400W8WAPRP7PiP<L09PRP0E`b<W7P0O1b7W1P0O1W1n2002105000010101Q2Y90A0S3DA8B{RS3?P5PtPECBS2QPHP:PRP7PJQ2SA;n80S3IF@X41PMP:Q1zPNA;{hk,NOPFP:PRPPQ2S15n5S2SE?X3=,1=GSX2:,1:X51#3X0>Q2@Q1z7C0S2@Q2CQ2D36X0>'4[X?AQ2HO1P0Q2Y,IAO1S2Db1b8W;PZP;P|F[WLW:W9W8W6PpP0EEb6W>PLP0E`b6W<PTP0Dtb6W7PUP0Dsb7W1P0O1b1P0O1b1W:P5P7P0P@P;P<P4P8O8W>W<W:W9W8W6W7W1X2:X41X51X0>XI=XD1XE?Q0AQ09P6PCP@P;P<P4P8P5P7P0O<AJA4GS1F1:=49TA;PBP@P<P;B08485DhQ1FPIP<%i;Q0>CgQ0:Q0q'VS0qA0:N]S1a%\]S1xQ0?,7K17}q'VS2CQ0FQ1517k}P0H0DS151MK}S2~Q0GQ0IQ0NP7H0:S0NQ0</OjS0I1ODhS3JP01OLfS31Pc1MVcS3KA0:NfS3L%\fAJAlGS3MQ061:=lS3N50AS3OPBP<PXPWB08lTUDhS3PQ3MPIPX%iWQ0>CgQ0^P5P\PEPHP:PrP7PJPZA;o80S0^F@X41PMQ1]Q1^76OPFP:PrPPPZ15o5S1]E?X3=,1=GlX2:,1:X51#3X0>PBPrP~P0PZP:P|PN%9wCDEUX0>'4S3Q]9]8]6]7]1]>]<[X=?1MLfS3RP0Q3KPeA0:NcS3S%\cS3TQ1?9TAwS3UPBP|PWP4B08XlTS3VDhS3WQ1GQ1AQ0>50IQ1lP5PuPECBS1lPHP:P\P7A;m80S1A:0BJrS3XD<X41PMQ1nQ1o,2OS1oP=PFP:P\PP15m5S1n,QrS3YD<X3=FdX2:,1:X51#3X0>A8B\ZS3Z?C0rS3[A0:~NS3\%9|S3]36X0>'4]9]8]6]7^1H]>]<X=1Q3LP0Q3SP:PN%\eS3SAJAvGS3^%K|S3_Q1c50AS3`PBP~PYP|B08WXlS3aDhS3bQ1gQ1hQ0>50IS1hQ1>Q09=0:7S3cQ1;56HX41PMA0:6NS1;Q0CP=Q09=0:PS0CQ0a56FX3=FdX2:,1:X51#3X0>Q0\Q0_Q1^36X0>'4]9]8]6]7]1]>XB:Q3TP0Q3SAJAwGS3SQ1bQ1r50AS1^PBPZP[P~B08YWXS0aDhS3dQ1vQ1wQ0>50IQ1iPHPdPJP6Q1jDZX41PMPxQ2;P=PFPyP6Q1kC]X3=FdX2:,1:X51#3X0>Q1mQ0i76xX0>'4]9]8]6]7]1XC3Q3^Q3`Q3bQ1gQ1hP:PNPB17u\S1vP0P~C>Q1yPHPdPJQ1{CFX41Q1YP=Q1~9GFyX3=DRX2:,1:X51#3X0>Q21/2aX0>'4];X@:PB17\rS1wPNP|C>PBQ2GPNP0C>Q28PHPdPJQ29CFX41Q1YP=Q2<9GFyX3=DRX2:,1:X51#3X0>Q2>/2aX0>'4];XF3PBQ1vPNP2C>PA%KoQ2JP<1:=\S2JP~EEQ2JQ2L50AS2<Q01PAQ2KQ2OQ2QPHPdPJQ3ICFX41Q1YP=Q2S9GFyX3=DRX2:,1:X51#3X0>Q2@/2aX0>'4[P0Q2KQ2H50AS2KQ2MQ2Y50APAP=Q00P=P=P0P0Pin10110500021010900X@AQ2XQ2NP0EvA0=mkS2OA0=ijS2@P0A0=ShP=PfPBPsP8P5PQPEPHPdPJA;z80S2SCFX41Q1Y15z5S3I9GFyX3=,1=S2Q'=+0=FYX2:,1:X51#3X0>PBPnP7P0P{PaEUX0>'4XH=P=PfQ2wQ0@50AQ2mPBQ2_PvP5PzPEPHPdPJQ2|CFX41Q1YQ2t9GFyX3=80H=+0=FYX2:,1:X51#3X0>A8BsgS2w?H0Q/zaX0>'4]8]AXG=%KtS2mQ2x50AQ2zA8BzpP5PsPECBS29PHPdPJQ2bCFX41Q1YP=Q2g9GFyX3=DRX2:,1:X51#3X0>S3e#bA8BQbS3f?C0nS3g/2aX0>#bP>Q3ePcP1Q2wPbPQPEPHPdQ34A;zg0CFX41PMQ2aQ0K56xQ2QGlX2:,1:X51PfP:Q3f?HenS2QQ2fQ36PdQ38A;sb0S2fCFX41Q3:PxQ3<Q0KP=Q33P:PNQ3>15seS3>#\D<X3=J0;H01X2:PhA8BneS2a?Hc{S34@0SfhQ3:Q3LQ3;A;Qe0S3eCFX41#3S3hQ3AQ3BQ0K'2S3i,2xS3j'2S3kQ2jP:PNPfQ3CCj15QcS3l3GX3=,1=S3m'=S3n'=Q3GQ3HP0Q3fPePnPcPfPKO6b1Q3hQ3nQ3kQ3mQ3AQ3jQ0APxQ3i1I:NS3iQ3BQ0KQ091I32S3jCpCpCp4003~FqK0J400W8WAQ1zP7PmP<L09Q1zP0E`b<W7P0O1b7W1P0O1W1n2002105000010101Q3DQ2UP5PRPECBS2UPHPdPJA;{80S2zCFX41Q1YP=15{5S3n9GFyX3=DRX2:,1:X51#3X0>Q27?C0SS27/2aX0>'4[X?AQ2HO1Q2Db1b8W;P~P@P0I0OW;P~PCPvF[WLW:W9W8W6PbP0H0Lb6W>PeP0EEb6W<PUP0Dtb6W7PVP0Dsb7W1P0O1b1P0O1b1W:P5P7P0P@P;P<P4P8O8W>W<W:W9W8W6W7W1X2:X51X0>XI=XD1XE?Q09P6PCP@P;P<P4P8P5P7P0O;Q11Q13Q14P@P<P4P8DaS14Q101:=8S1F50A%^;=0AGQ0HP:P@%AC>0?;NP_C_AnK6_Q17Q1=Q1EQ1RQ1TQ1XP0Q1QPbQ1LP:PDQ0<%ALS1Q<0?NPeC_S1TAn5VeQ1GQ1@Q1DQ3V7yYQ1J1:=TS3V50A%^WS1J=0AGQ1_]9]8]6]7]1]>]<[X=?Q1`P0Q1LPgP:PL%AVS1L>0?DNPbC_S1GAnwUbS1@Q1dQ1eQ3a7y4Q1fQ3N50A%^YS1f=0AGQ1p]9]8]6]7^1H]>]<X=1Q1TP0Q1GP:PVPL%AUPNCPAn|TgS1GQ1qQ1sQ1tQ0a7yZS0aQ1uQ1?50AS1u%^[=0AGS1tQ1yQ3cQ1|56HX41PMQ1;Q1}P=Q0CQ2056FX3=FdX2:,1:X51#3X0>Q21Q0_Q1936X0>'4]9]8]6]7]1]>XB:Q1@P0Q1GP315~lQ22Q24Q25PrP[PYPWDaQ26Q1c50A%^]=0AGQ28PHP:PqP`%A}S28PNCPS26P7Q2:D<X41PMP:P`%AqS2:>0?_NPNC_S25Q2;P=PFP:Q26PPQ2=D<X3=FdX2:,1:X51#3X0>Q2>P:P^P]%A_S2>PNCPS2=PNQ0iD<X0>'4]9]8]6]7]1XC3Q1qQ1sQ0aQ1uQ1tP:P[PY%A]S22PNCPS24PBQ2?P0PrC>Q2APHP:P}Pq%AkS0iPNCPS2;P7PJ15tkS1GQ2BF@X41PMP:Q26PN15R},NOPFP:Q2;PPQ1GQ2EE?X3=,1=GSX2:,1:X51#3X0>Q2FP:P_%A`S26>0?^NPNC_17S`#u36X0>'4];X@:PBQ2GQ24PZC>P315m^S24PB17imQ2=P0C>Q2UPHP:PkP}%AjS2=PNCPS2GP7PJ15{jS19Q2zF@X41PMQ2;=0:NS2;POQ1G#9S1GP=PFP:Q2GPPQ19Q3nE?X3=GmX2:,1:X51#3X0>Q27Q25Q1z/7q#u36X0>'4];XF3PBQ2?P]P[%A^S2?PNCPQ24C>PA%KiQ3DX?AP<Q2MPrEEQ2WQ01PAQ2XQ1[90A7PBPQP{P5PnPEPHP:PfPh%AcS2XPNCPS2WP7PJQ32A;s80S3DF@X41PMP:PhPj%AfS24PNCPS25PNPO15QfS0CI05P=PFP:Q2WPPQ3215s5S20E?X3=I0KFYX2:,1:X51#3X0>Q3??H0tP:Q2GPNQ19#9CD'zX0>'4[P0Q2ZQ2[Q2N50APAP=Q00P=P=P0P0Q1zn10110500021010900X@A1:=SQ1[P0EvQ2\Q2]P0A0=RfP=PcPBQ2_P8P5PzPEPHPbPe%AgS2\PNCPS1[=0:7S2[PJQ2n/5gS19Q2|DZX41PMPePc%AbS2|PNCPS2G=0:NS3?POQ2_/5bS1}#9S1;PFP:Q1[PPQ19Q2tE?X3=,1=S2tJ0NFYX2:,1:X51#3X0>PBPsP7P0PQQ2W=0:NS3cQ32#9S1|'2EUX0>'4XH=P=PcQ0@9TAQQ2lQ0z50APBQ2pPwP5Q2nPEPHP:PpPg%AvS1dPNCPS1pP7PJfpS3a/5vS1eQ3a/f8P0C{D<X41PMP:PgPb%ApS1_PNCPS1DPNPOQ2p/5pS2pI05P=PFP:Q1pPPQ1eQ3a;r5D<X3=I0KFYX2:,1:X51#3X0>Q2{?H0zQ3?Q1;'2'zX0>'4]8]AXG=Q2kQ2y50AQ0uQ0u50AQ2oPHP:Q1DP7PJQ2pQ2rF@X41PMP:Q1[PNQ19,NOPFP:Q1DPPQ2pQ2qE?X3=,1=GSX2:,1:X51#3X0>S2q#bQ2v%AeS2p-0GfS1D>0>cNS1[=0:NS2rQ2e#9S2o36X0>#bP>Q2qPeP1Q2{PgPzPEQ2[PI2025pQ0=Q19Q2s;r0CD56HX41PMQ3?PIP7Q2^Q0>CgQ1;36Q2tGlX2:,1:X51PcP:Q2}1oe0PAQ0vPGP:Q2GP7PIQ2^-03bQ0=Q1}Q2`'QCDCDCDX41Q36Q2rQ37Q0>50IQ2oP=Q0vQ0@50AS0vP:Q2GP7B0<b0NCjQ1}Q1}C]X3=J0;H01X2:PfQ2h@0ScfQ36P:Q1[PcQ38Q2eQ2dF@X41#3S2dQ3:Q3cQ3<Q1|'236S3cQ33P:Q1[PcQ3=CjQ2eQ2eC]X3=S2e,1=S3='=S33'=Q3GQ3HP0Q2uPbPsPePcPKO6b1Q2dQ33Q3cQ3=P=Q2ePhQ39Q1\50AP:Q2WPfB0<chNCjRsQ32Q32'QS39'2Q0APsQ39PAPGP:Q1[PcQ00P=P9P0Q2|-0F0Q1Dn10110A00021010>0000[NCjX?AQ2W,I:%^cQ09E`PseQ32,I3CpFq3~3~FqK0J400W8WAPtP7PSP<L09PtP0E`b<W7P0O1b7W1P0O1W1n2002105000010101Q2N90A0Q2PPHP:Q25P7PJQ0CQ2RF@X41PMP:PjPk%AhS2RPNCPPN15nh,NOPFP:Q25PPQ0CQ2TE?X3=,1=GSX2:,1:X51#3X0>Q2VQ2;Q1G36X0>'4[X?AQ2YO1P0Q2N,IAO1b1b8W;PrP@P0F[W;PrPCP|F[WLW:W9W8W6PpP0EEb6W>PgP0EEb6W<PTP0Dtb6W7PUP0Dsb7W1P0O1b1P0O1b1W:P5P7P0P@P;P<P4P8O8W>W<W:W9W8W6W7W1X3=X2:X51X0>XI=XD1XE?Q0AQ09P6PCP@P;P<P4P8P5P7P0O<Q11Q13Q14%^<Q1F50AQ0qP:P;%A@>0E<NP]C_Q0??nC]Q2CQ15Q2~Q0NQ0IQ3JP0Q31PcQ3KP:Q0<Q0;%AD<0ENPfC_S31An5LfQ3MQ3OQ3P%^l1:=US0I50AQ3ZP5PrPEPHP:PZP7PJP~A;u80S3ZF@X41PMQ3\Q3]76OPFP:PZPPP~15u5S3\E?X3=,1=GlX2:,1:X51#3X0>PBPZP|P0P~P:PwPN%9vCDEUX0>'4]8]6]7]1]<]:[X=?Q3RP0Q3KPeP:PDQ0<Q1Q<0ENPcC_RsAnpVcS1QQ3UQ3W%^XQ3V50AQ3Q]8]6]7^1H]<]:X=1Q31P0PsP:PLPDQ1LPNCLAnvUeRsQ3^Q3`Q3bQ1JQ3N50AS1JQ1lPHP:P6P7Q3XD<X41PMP:PCPNQ1oPFP:P6PPQ3YD<X3=,1=GSX2:,1:X51#3X0>Q3[P:P;PNQ3]D<X0>'4]8]6]7]1]<XB:Q1QP0PsP315wTQ3SQ1^Q3dQ1fQ1?50AQ1>PHP:P_P^Q26PNCLS26P7PJPCQ1<F@X41PMP:P^Q2>>0E]NPNC_S2>PO%9@P=PFP:Q26PPPCQ12E?X3=GmX2:,1:X51#3X0>Q0\P:P[PYQ22PNCLS22PN%9<D<X0>'4]8]6]7]1XC3Q3^Q3`Q3bQ1JP:PWPX%AYPNCLS3SPBQ1wP0P|C>Q1iPHP:P`P_Q2:PNCLRXP7PJ15SqRsQ1jF@X41PMP:Q26PN15i`,NOPFP:PXPPPsQ1kE?X3=,1=GSX2:,1:X51#3X0>Q1mP:P]Q2?>0E[NPNC_17o^#u36X0>'4];X@:PB17rZQ3SPwC>P315\[S3SPBQ1vQ22P0C>Q1yPHP:PqP`Q28PNCLRwP7PJQ1z/5}RiQ1{F@X41PMA0:XNS1{PO%9sS1zP=PFP:PwPPPiQ1~E?X3=GmX2:,1:X51#3X0>Q21Q2>17m_#u36X0>'4];XF3PBQ1wPYPW%A[PNCLQ3SC>PA%KuQ2L90A0X?AP41:=rRsP|EE1:=_S3S90AsQ01PAQ2JQ2Y90A7Q2UPHP:PjPkQ2RPNCLRsP7PJ15{hRXQ2zF@X41PMP:PkP}Q2=PNCLS2=PN15tjS2z,NOPFP:PsPPPXQ3nE?X3=,1=GSX2:,1:X51#3X0>Q27P:PwPN%9iD<X0>'4[P0Q2<Q2KPAP=Q00P=P=P0P0Pmn10110500021010900X@AQ2MQ2YP0EvA0=o}Q2OP0Q2@P=PhPBPQP8P5PnPEPHPcPfQ2pPNCLS2p=0:7S2@PJQ3>Q3DDZX41PMPfPhQ2XPNCLS2X=0:NRmPOQ3l#9RiPFP:Q2pPPQ3>Q20E?X3=,1=S20J0NFYX2:,1:X51#3X0>PBP{P7P0PtA0:sNS3D%9XS2Y'2EUX0>'4XH=P=PhQ2mQ0@50AQ2lQ2y50AQ29PHP:PbPeQ2\PNCLRXP7PJQ2_/5gRsQ2bF@X41PMP:PePcQ2|PNCLRwPN15zbRz,NOPFP:PXPPPsQ2gE?X3=,1=GSX2:,1:X51#3X0>Q3g?6miX0>'4]8]AXG=Q1\9TARQ2xQ2x50AQ2wP5PQPEPHP:PwP7PJPzQ2SF@X41PMP:Q2pPNPOQ3>I05PFP:PwPPPzQ3IE?X3=,1=GlX2:,1:X51#3X0>Rz#bQ2a?H0{PhPjQ24PNCLRw=0:NS2415nfRQ#9S3I'2'zX0>#bP>PzPfP1Q2QPEQ2@PIQ2c-035Q0=Q3>Q2f'QCD56HX41PMPmPIP7Q30Q0>CgPiQ20I0UH01X2:,1:X51PhP:Q341of0Q3:P:Q2XP7Q3;Q3lQ3eF@X41Q3AQ24Q3BQ3IP=Q2jP:Q2XP7Q3CCjQ3lQ3lC]X3=J0;H01X2:PjA8B{cPfPt1ohjCBQ3AP:PwPhPIQ2iQ0=1knc/x0-0iQCDD<X41#3RnQ0fQ3DPI202hfQ0>Q2YCD36RIPAQ3@Q0@P:Pw20@f0>0>hN1QQQCDCDX3=,1=RQ'=Rw'=Q3GQ3HP0Q2aPcP{PfPhQ0?O6b1Q0ePA1IA0Q3@=0A0Q00P=Q35=0A0PAP5Q0@P:PX20@g0>0>bN1QssR{CDCDX3=,1=]JP7Q0vP=PAQ07Q0@P:PgPbQ1_PNCLRt20@p0>0>gNQ2n/5pRi/QiCDRiCDX3=P7Q2lQ2l50AP:PXPbB0<g7NCjRm/2{Q2l,IAPmP{PAQ0uP:PtPgQ00P=P9P0Q1d-0F0Q1_-0G5n10110A00021010>0000[NCjX?A1I:X%^gQ0<E`Pme1I3sCpFqWJX3=P0O1Q3:PA%^eQ2y90A0X?APKPG20he0EEQ2x90AGPAPGQ0xQ0yQ2yP0EEQ0wPAPGQ0@PiCDX3=,1=00P0b1b>WJn10110500021110901P0O1bJb?9~IQ9~nwFqK0J400W8WAPSP7PoP<L09PSP0E`b:W7P0O1b7W1P0O1W1n2002105000010101Q2IQ2APHP:Q2=P7PJQ2zQ2BF@X41PMP:P}PqQ0iPNCLPN15Rk,NOPFP:Q2=PPQ2zQ2EE?X3=,1=GSX2:,1:X51#3X0>Q2FQ1{Q1z36X0>'4[X?AQ2LO1P0Q2H,IAO1b1b8W;P|P;P0F[W;P|P@PpF[W>W9W8W6PbP0EEb6W<PeP0EEb6W:PUP0Dtb6W7PVP0Dsb7W1P0O1b1P0O1b1W9P5P7P0P;P<P4P8O7W<W:W9W8W6W7W1XT=X2:X51X0>XI=XD1XE?Q09P6PCP@P;P<P4P8P5P7P0O;Q2l9TA8PBP4P5P8&0g>R|DhQ08Q0d'VA0:ND%\DQ18Q1:'VQ0FQ0DQ0oP0H0D1MClQ0GQ0:Q0EP7H0:Q09/OWQ0A/OYP0Q0?/O[P]1MK]RYA0:N[RWQ1KAJADGQ061:=D50APBP<PLPVP|DhQ0PPHP:PhP7Q1MD<X41PMQ0RQ1NP=PFP:PhPPQ1OD<X3=FdX2:,1:X51#3X0>Q1PQ1BQ1C36X0>'4]6]7]1]:]9[X=?Q0?/M[P0PYP^Q1aQ1xQ1S1:=L50APBPjPVP4P|DhQ0XPHP:PfP7PJPhQ1UF@X41PMQ0ZPOQ0[P=PFP:PfPPPhQ1VE?X3=GmX2:,1:X51#3X0>Q1WQ1HQ1I36X0>'4]6]7^1H]:]9X=1P0Q1aP:PN%\^RLAJA}GRY1:=V9TAjRVPBPhPUPjP|DhRUQ0JQ0]Q0L56HX41PMQ0_Q0MP=Q0`Q0O56FX3=FdX2:,1:X51#3X0>Q0QQ0cQ0S36X0>'4]6]7]1]:XB:Q1xP0PLAJAkGQ0TQ0I50APBPfPTPhP|DhQ0UPHPdPJP@Q0VDZX41Q0jP=PFPyP@Q0WC]X3=DRX2:,1:X51#3X0>Q0YQ0m'2X0>'4]6]7]1XC3P:PNPB17cfRfP0PkC>Q0b];X@:PBQ1ZPNP}C>PBQ0nPNP0C>Q0gPHPdPJQ0hCFX41Q1YP=Q0k9GFyX3=DRX2:,1:X51#3X0>Q0l/2aX0>'4];XF3PBPfPNP2C>PA%KeQ1c90A0X?AP8Q2xPkEEQ2xQ1?50AQ01PAQ2yQ2390A7Q0{PHPdPJQ0|CFX41Q1YP=Q0}9GFyX3=DRX2:,1:X51#3X0>Q0~/2aX0>'4[P0Q2yQ1c50AQ0uQ1r50APAP=Q00P=P=P0P0Pgn10110500021010900X@AQ0zQ23P0EvA0=b[A0=g]P0A0=p^P=P_PBP\P8P5PrPEPHPdPJQ3ZCFX41Q1YQ3\9GFyX3=80H=+0=FYX2:,1:X51#3X0>PBPZP7P0P~PaEUX0>'4XH=P=P_Q1bQ0@50AQ2lQ2H50APBPoPhP5PuPEPHPdPJQ1ACFX41Q1YQ1n9GFyX3=80H=+0=FYX2:,1:X51#3X0>PBP\PkP0PrPaEUX0>'4]8]AXG=Q3_Q3S50AQ2LQ2L50APBPuPjP5P\PEPHPdPJQ0^CFX41Q1YQ1]9GFyX3=80H=+0=FYX2:,1:X51#3X0>#bA8Br}Rr?H0Z/zaX0>R}#bP>P}Q05g00hG+0fQ04$0Z$0V$0T-0I=$0A20I==$0AR}P}g00he$0Ag00i]-0I=$0AJ0eR}A8BZq?C}~PaQ3EQ02AC570Ay87|R~[Ay50|AC857[R|Q3F$0d\~B0c570P0n2001000000120000000X=1X0>WKQ3EP|^=1^0>]KP0PrP}PZQ0AO4b1PxQ0KQ3iQ3jCpFq3~W8WAPvP7PbP<L09PvP0E`b9W7P0O1b7W1P0O1W1n2002105000010101Q1r90A0Q0pPHPdPJQ0rCFX41Q1YP=Q0s9GFyX3=DRX2:,1:X51#3X0>Q0t/2aX0>'4[X?AQ1cO1P0Q1r,IAO1b1b8W;PkP<P0I0OW;PkP;P`F[X<UX8VX6YP_P0H0Lb6W:P^P0EEb6X9WQ0;P0Dtb6W7PKP0Dsb7W1P0O1b1P0O1b1W8P5P7P0P<P4P8O6W:W9W8W6W7X1MXI=XD1XE?P<P4P8P5P7P0O6n10410:10610700001087110<10;10=1040000000005110<10;0000000005110<10;000000000<110<10;108100104103101000000000000000;110<10;108100104101000000000000000<110<10;108100104101102000000000000000;110<10;10810010410110>0000000000006110<10;108000000000Q03Q0D,V5A0:5@1Q5@PBQ0<PKP5Q0;PEPHP:PKP7PJQ0?1fD8P0C{D<X41PMP:Q0?PNPOQ0AI05P=PFP:PKPPQ0??rD5D<X3=I0KFYX2:,1:X51#3X0>PBPKQ0AP0Q0?P:Q09PN%96CDEUX0>'4[[[XC3XB:WPQ0BP8P5O3P0Q03Q16'I1I:41I38O3b1W;WAXF3W@WGXQ1XR?o"). Qed.

(* [comment removed for export] *)
Lemma sstep_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) ["WithSegs"] "h03effh13evsh22m'h31ih41mh51Hh62Hch72Hhh83Hh'h95Hlazyh:4Hsvch;5modelh<2msh=2x8p;1p;3p;2p;4p;5p;=g004dj11Tg005Ij1ETg005gj1:Tg006Jj16Tg006jj1DTg00<Aj1<Tg00=8j1;Tg0094j30Tg007Lj19Tg008Rj28Tg00D;j37Tg00FBj32Tg00;7j24Tg00@Oj2CTg00j<j1BTg00>`j1=Tg00[Xj43Tg00R;j35Tg00MTj5>Tg00=Zj1?Tg00k4j3@Tg00lEl=ATg00dIg00^UR0g00eP#1#1#1#1#1#1#E#:R1g00cKR2g00`A#6R3%D1R4f4R5#<%;130R6f6R7#91815504g00a7R4p,4segsR8f7R9f5R:37?257f3R;f2R<'4301C11R1#6%B:%=130P8f:R1f9R=f8R>P9P7P7P:P5P;g00gJR?g00E1A25;<f1R@f0RA'4504P2P5P<P@C395:;[RBP2P;P@PAC3955<A2:5;14<@504R4[P2P:P;P<C39575\4P5P;P<P@PAD>P@n2001000000120000000X13X20X40X02W3PB^13^20^40^02^3?PAf;=78=P>P1P9P7P;O6b5P@%?9=@7AM=AW9X86W6W:W7W1X20W0W=W;W<o"). Qed.

Lemma sstep_cfg_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep_cfg segs ACFG (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
  apply (sstep_cfg_syscall segs ACFG ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hns.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

Lemma uniform_not_spurious : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (b : bool),
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = b) ->
  forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i).
Proof.
  intros ms model x8 I effs ms' evs b Hinv Hb i (Hoff & Hr & eff' & m' & ev' & Hspec & Hnr).
  apply check_syscall_ok_iff in Hspec.
  destruct (Hinv _ _ _ Hspec) as (j & -> & _ & _).
  rewrite Hb in Hr. rewrite Hb in Hnr. congruence.
Qed.

Lemma sstep_cfg_svc_inv_chk : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs ACFG (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff
           /\ m_halted model' = None
           /\ ((exists model'', e = evs
                   /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
                   /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
               \/ (e = [] /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
                   /\ st = SError)))
          \/ (exists code, m_halted model' = Some code
                 /\ e = evs ++ [halt_ev model' code]
                 /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. split; [assumption|]. split; [assumption|]. left. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. split; [assumption|]. split; [assumption|]. right. repeat split; auto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

Lemma node_chk_ev_gen : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnf Hinv Hnu Hnh Hlazy. split.
  - intros i. apply (sstep_cfg_of_check ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv_chk ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns. split.
  - intros i. apply (sstep_cfg_of_check ms model x8); auto.
  - intros e st Hss. apply sstep_of_cfg in Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
  apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

(* [comment removed for export] *)
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
  - apply (uniform_not_spurious ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma rz_ret_only : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins : forall ms model x8 reads r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, realizes segs (nx i) (T i)) ->
  realizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma rz_exit_chk : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) ["WithSegs"] "h05modelh12msh22x8p;1p;3p;2p;7g004dj10Tg005Ij1:Tg005gj13Tg006jj12Tg00<Aj19Tg00=8j18Tg0094j31Tg007Lj14Tg008Rj25Tg01Xcj16Tg01Y]j77Tg00dIg00^Ug00eP#0#0#0#0#0#0#:#3R0%20R1f1R2#9%8031f3R3#41502511f2R1#6p,4segsf5f4P3P1P2f0F7UUUW2W0W1o"). Qed.

(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

Lemma node_open : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hno Hchk Hmk Hmklazy Hfree.
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 _ Hsvc eq_refl Hno) |]. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hno Hchk Hmk Hmklazy Hfree HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
