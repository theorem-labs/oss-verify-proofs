(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit D_iface D_defs RT_fk RT_fk_iface Bi_fktw Bi_fkkit Bi_fkweak LeptF_iface LeptF_weak LeptF_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.




From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import LeptC_cmapvalid_N0 LeptC_cmapvalid_P0 LeptC_cmapvalid_N16 LeptC_cmapvalid_P16.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptC_cmapvalid () := "C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A028RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface8cmap_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53A02:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A02:Lept_iface5optrFC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface4lenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface4lresC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K53A028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface5lpostC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A02:Lept_iface5keepsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A02BLeptC_cmapvalid_N0DpixcmapIsValid_ok_N0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02BLeptC_cmapvalid_P0DpixcmapIsValid_ok_P0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02CLeptC_cmapvalid_N16EpixcmapIsValid_ok_N16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02CLeptC_cmapvalid_P16EpixcmapIsValid_ok_P16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027Bi_fktwCpixcmapIsValid_cpsFC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53A02:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A02:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53A02:Lept_iface@e_pixcmapIsValidC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A029Bi_fkweakGpixcmapIsValid_cps_of_FC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02?LeptC_cmapvalidBpixcmapIsValid_okFC1?~~~~~~~~~~~~~~~".

Section CV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.   (* [comment removed for export] *)
Hypothesis STDERR : lept_stderr_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorInt.
Hypothesis MAXIDX : pixGetMaxColorIndex_cpsF RT.

Theorem pixcmapIsValid_okF : pixcmapIsValid_cpsF RT.
Proof using AF GP FKC STDERR RERR MAXIDX.
ltac2:(KReplay.run1 (kr_t_LeptC_cmapvalid ()) ["CV"] "p'0h05CASEXh11si001sh25CASEHh31ch42m'h52msh62rvh71yh83Σ'h91Fh:3PMch;2a0h<2a1h=2a2h>2a3h?2a4h@2a5hA2a6hB2a7hC4cmaphD2cvhE2fchF2gphG2lohH1mhI3pixhJ2pvhK2rahL2s0hM2s1hN3s10hO3s11hP2s2hQ2s3hR2s4hS2s5hT2s6hU2s7hV2s8hW2s9hX2sphY2t0hZ2t1h[2t2h\2t3h]2t4h^2t5h_2t6h`2tpha1vhb1xhc2Σi011ei021np%0p;1p;2p;3p;4p;5p;6p;Sp;Dp;7p;og0000j1iTg000hj15Tg001Mj1:Tg001kj1BTg002Nj1hTg0033j2aTg003_j1^Tg004Aj1[Tg005?j1ZTg006;j2GTg006aj30j2DTg007;j26Tg0087j4VTg0096j5gTg00:4j1fTg00;1j12Tg00;Jj1`Tg00<Gj2]Tg00<aj17Tg00=?j5\Tg00>;j1ITg00?3j1HTg00?Sj39Tg00@3j4?Tg00@lj1YTg00Agj6XTg00Bbj5WTg00C]j2;Tg00DGj2=Tg00Dgj2FTg00EGR0j2ETg00EglSNTg00Fdj4Oj5QTg00G]lDPTg00HVj7CTg00IRj2RTg00J2j2MTg00JOj4UTg00Joj7TTg00Kkj28Tg00LFj23Tg00L`j1STg00M@j2ATg00N>j2>Tg00O9j2@Tg00P7j2LTg00PTj2JTg00Q0j3KTg00Qej4<Tg00R@lobTg00SSlocTg00Tflo_Tg00V;lodTg00WPj1eTg00XWR1f0R2g00Y5R330p=1f2R4f1S00/82'8p=4p,2RTR5#iR6g00YSp-0[g00ZI#5R7#5R8#5R9#5#5R:#5#:R;#BR<%h7R=#:/a<%::#B%:9#B#^\<R9g00Zng00[lfYR>#[fZR?#ZfWR@g00\i,G;50<fRRAf8RB,G;50<RCf`RD,65f=REf;RFPBCV%1FfaRG,65f>RHPFPBf9RIDg%fB#1#2%`Bf<RJ50134']P5fbRKf?RLPF%78R8D\g00]`RMf@RNPJg00^XRO%II%HORP39C?P5fdRQfARRPGPN%7=#YEXP5feR=%77P3P8DWfcR7,;;%7:R:'=RS/F3%1SRS%2S'EP01;;Q/=:#1RS%2SP5fhRSfgRTg00_PRUffRVP=PQP7PKPGPDf_RWf^RXf]RYf\RZf[R[P?P>fXR\P@fVR]fUR^fTR_fSR`PAfQRafPRbfORcfNRdfMRefLRffKRgfJRhfIRifHRjfGRkfFRlg00`WS01fERmMSN'DCOg00a^RnP5P4fkRoflRpPofjRqfiRrP=PQP[P?P>P\P@P]P^P_P`PAf3RsPeP2Q00MDPP5fnRtf4RuPgP2PoPhFCP5PtPuPo1R11RvP1P1Pk1Mk8CU%HvRw39PgP2FTPMP2Pk%I4=9OPS02C?'834X49,39X5UPsDQ%SvRP1654RO165p30g00bS,R1#SRx1A54Ry1A5p301>54Rz1>5p5011@5p/L81@54R{'J3434X7<,3<X6<,3<X86,36W35KMP21;;=/=:#1R|fCR}/F3S03%1}R3%23'ES04P0fDR3#1R~%2~S05P5PoPqPrPSPTPVP=PQP7PKPGPDPWPXPYPZP[P?P>P\P@P]P^P_P`PAPaPbPcPdPePfPgPhPiQ01PjMSN,DUCOP5P4PtfoR4PtfmPpPSPTPXPYPZP[P?P>P\P@P]P^PsPbP2Q00MDPP5fqS00PuPdP2PtPeFCP5Q00PuPtP1P1Ph1Mh8CU=9vwPdP2FTPMP2PhQ02C?'834X49,39X5UPsDQ165490PO1A5490xy1>54901z1@54/L8/J{3434X7<,3<X6<,3<X86,36X3n5KMRMP2%1mRnP5p,2AFR6p,2GPR{p,3FKCR8p,6STDERRR4p,4RERRRzp,6MAXIDXRyPpPoPqPrPSPTPVP=PQP7PKPGPDPWPXPYPZP[P?P>P\P@P]P^P_P`PAPaPbPcPdPePfPgPhPiPjPkPlPmP3P}fBRxPRPNPLPHPEPJPFf:ROPIPBf7RPf6RU1;;r/=:#1R:%1lR;PsP2C<MobW0P2O1%2nR9P5P6P{P8P4PzPyPpPoPqPrPSPTPVP=PQP7PKPGPDPWPXPYPZP[P?P>P\P@P]P^P_P`PAPaPbPcPdPePfPgPhPiPjPkPlPmP3P}PxPRPNPLPHPEPJPFPOPIPBPPPUP:%2;RwPsP2C<MocW0P2O1n200110001021010110102b1W2P2O1%2|Q03Q04P0P~Q05PMP2P5P6P{P8P4PzPyPpPoPqPrPSPTPVP=PQP7PKPGPDPWPXPYPZP[P?P>P\P@P]P^P_P`PAPaPbPcPdPePfPgPhPiPjPkPlPmP3P}PxPRPNPLPHPEPJPFPOPIPBPPPU%2:R:P;PsP2C<Mo_X0nP2O1P5P6P{P8P4PzPyPpPoPqPrPSPTPVP=PQP7PKPGPDPWPXPYPZP[P?P>P\P@P]P^P_P`PAPaPbPcPdPePfPgPhPiPjPkPlPmP3P}PxPRPNPLPHPEPJPFPOPIPBPPPUP:PwPsP2C<ModX09P2O1n200110001021010110102b1W2P2O1n200110001021110111102b1UUUUUUVCVCUUUUXb<WaWDXJ1XI1XC1XG1WHWEW9X_<X^<X]<X\<XO<XN<XW<XV<XU<XT<XS<XR<XQ<XP<XB<XA<X@<X?<X><X=<X<<X;<XM<XL<X[<XZ<XY<X`<XF<XX<WKW:Wc%e5eo"). Qed.

(* [comment removed for export] *)
Theorem pixcmapIsValid_ok : pixcmapIsValid_cps RT.
Proof using AF GP FKC STDERR RERR MAXIDX.
ltac2:(KReplay.run1 (kr_t_LeptC_cmapvalid ()) ["CV"] "p;2g00c2j20Tp,2RTg00d?'0o"). Qed.
End CV.
