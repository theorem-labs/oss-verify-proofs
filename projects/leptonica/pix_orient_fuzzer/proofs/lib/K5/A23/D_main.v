(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import MainSkel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import D_usage D_open D_dir D_file D_trdefs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_main () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib2K54Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A236D_defs5STARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4OPENC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6FAILEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6OPENEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4EXITC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2or00K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K53Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K52AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6NodesA8ast_exitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic3notc69OSSVerify5KrLib2K53A236D_main=length_argv_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53A237D_usage:usage_cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open;to_open_cpsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K54Spec5Canon:open_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open=open_fail_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open9open_cps2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open;failed_cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_dir8dir_cpsEC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec5Canon6oclass03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_file9file_cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8MainSkel=main_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC69OSSVerify5KrLib2K53A236D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs;asegs_belowC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Canon6oclass00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K69OSSVerify5KrLib2K54Spec5Canon6oclass01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec5Canon6oclass02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section MainA.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OPC : open_contract RT.
Hypothesis OPR : open_refused_contract RT.
Hypothesis CLS : close_contract RT.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis FUZZ : fuzz_one_cps RT LIB.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis H_LATCH : tr_latch_hyp XENV XENV_FP.
Hypothesis H_INCB : tr_incb_hyp XENV XENV_FP.

Lemma length_argv_Z : forall (argv : list (list byte)), length (argv_Z argv) = length argv.
Proof.
ltac2:(KReplay.run1 (kr_t_D_main ()) ["MainA"] "h04argvp;1p;3p;4p;2g0000j10Tg000Uj19Tg0013j13Tg001Vj11Tg0026j18Tg002`j37Tg003<j45Tg003[j14Tg004Sj22Tg0053j36Tg005M#0#0#0#9R0#3R1#1R2#1P2g0062R3#1R4%809713f0R3C5g006P%43,24122336eW0o"). Qed.

Theorem main_realizesA : forall c, START RT OUT_rep ERR_rep XENV LIB argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof using All.
ltac2:(KReplay.run1 (kr_t_D_main ()) ["MainA"] "p'0h02HLh12msh22PMh31Hh42moh53HCLh62Pmh71Ah81nh92HAh:3HPMh;3HPmh<2HSh=1ch>2c'h?4codeh@4datai001xp;8p;1p;7p;3p;2p;=p;6p;Ep;Ap;4p;Hp;Rp;Bp;5g006oj8bj7MTg003[j1aTg007gj7GTg008^j7`Tg009Wj7QTg00:Pj1Oj3LTg00;Gj2ITg001Vj1?Tg0000j15Tg000Uj1@Tg0013j1CTg00;gj1UTg00<Ij1TTg00=Oj12Tg00>4j1;Tg00>Rj20Tg00?8j2BTg0053j34Tg00?Zj2NTg00@4j3KTg00@Wj2JTg00AMj1HTg00B@R0j21Tg00B[R1j27Tg00C5j3:Tg00CZj28Tg00DTj39Tg00ERl=FTg004Sj2ATg00FMj1>Tg00Fmj1<Tg00GFj1ETg00HFj6=Tg00HblEDTg00I`lARTg00J^j1STg00K=j1_Tg00K]j4^Tg00L9j2\Tg00M6lEVTg00N6lEWTg00O2lEXTg00P0lHYTg00Pjj1ZTg00QelR[Tg00RalBPTg00Sbj5]Tg00TWR2f3R3f2R4f1R5f0R6D]p=6A4456,13p=3g00UTR7p,2RTR8p,7OUT_repR9p,7ERR_repR:p,4XENVR;p,3LIBR<p,5argvbR=p,2fsR>P6Gbg00VIR?%a=R@P>P8P9P:P;P<P=P>FMP8P9P:P;P<P=P>FGP8P9P:P;P<P=P>F`P8P9P:P;P<P=P>FQ%O>g0062RAAL>56P11IAA#?RBg00WARCp-0RD[REg00XHRFPD[RDP4P5P6f4RGC6P4P6O1RHg005MRI#5RJ#5#5RK#5#5#5#@RL#CRM#URN%T5RO%2JRP#2#2RQ#5#2#;,0L,BM34%2Q#5#;,0L,BM94NO'NROPM%@P%5P#;g00Y>3K,J5RPf7RN,0LRQC3[^1CP5P6O1g00YZ%H5;4>RR[^4FRS'1'1X2D'7X6E'7X7B10L3%2I#2#2#2#2#2#2#;,0LRI5:L/8>99?4P6P4P5P6f6RTC6POPMPPf9RU,0LC3\H^1C/1S'1X2D,7DX6E,7EP1PEP3P5P6PNC6POPMPPf:RV,0LC3\H^1C/1S'1X2D,7DX6EA:LQI/8>99?TP6f5RQP5P6PUC6POPMPPf<RW,0LC3\H^1C/1S'1X2D,7DP1PDPTP4P6PVC6P3P6O1POPMPPf=R1,0LC3[^1C/1S'1X2Df;RX,0L=:LI/8>99?VP6f8PGP6PWC6PQP6O1RGPOPMPPf?RY,0LRZC3[^1C/1S'1P0PUPQP5P1C6PTP6O1RTPOPMPPf@,0LC3[^1CPR\H^4F'1f>A:LZI/8>59?P6PXPNP3PYC6PUP6O1RYPOPMPPfC,0LR3C3[^1CPR\G^4F'1P0PVP6O1POPMPPfD,0LC3[^1CPR\T^4FfBA:L3I/8>59?P6PWP6O1POPMPPfF,0LRLC3[^1CPR\Y^4FP?P2g00ZHg00[CfAP1PUfEPLP>PQP5P6M=FW:W;P5P6O2n2001000000120000000W3W9P5P6O2n2001000000121000000W3X2DP5P6O2n2001000000121100000W3X6EP5P6O2n2001000000121100000W3X7BP5P6O2n2001000000121100000W3X>7W?%?AR7/A@RB#>%;JRJ54ARE#<g006PRDPB%>6=4AJRQ#<X8DP6%@K#C#?RK/A=RL%E=RUE=%>L=4AJRJ#<P8P9P:p,5IO_FPR1P;p,7XENV_FPR2P<P=P>p,2AFR?p,6AF_DRVRFp,3FPRRYp,3EXCRRp,5VARGVRCp,7OUT_locRPp,7ERR_locRMp,8XENV_locROp,7LIB_locRWp,6IO_imgR3p,8XENV_imgRIP6MEDb0W0PDPBPQX8DRQP6PLPUE=RTPJP8P9P:P1P;P2P<P=P>P?PPPMPOPWP3PIP6MARb0X0Eg00\ARVP7g00]<#SP@%_AC^/\>RAg00][34R@PDPBPQP5PLPUE=R7PJP8P9P:P1P;P2P<P=P>P?PFp,3OPRPCPPPMPOPWP3PIP6P5MEVb0W5X0E%<@P7PJP8P9P:P1P;P2P<P=P>P?PFp,3OPCPCPPPMPOPWP3PIP6P5MEWb0W5X0EPTPJP8P9P:P1P;P2P<P=P>P?PFPYPRPCPPPMPOPWP3PIP6MEXb0X0Eg00^V94VAP7PJP8P9P:P1P;P2P<P=P>P?PFp,3MALR7p,4RDIRPYPRPCPPPMPOPWP3PIP6P5MHYb0W5X0E%Z694VAPDPBPQP4PLPUE=PJP8P9P:P1P;P2P<P=P>P?PFp,3CLSP7p,3FREp,3FRNp,3MCPp,5RFILEPYp,3FWRp,4FUZZp,3VPRPRPCPPPMPOPWP3PIp,7H_LATCHp,6H_INCBP6P4P5MR[b0W5X@KX0EP5P6MBPW<W=o"). Qed.

End MainA.

(* [comment removed for export] *)
