(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb RunRandom PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymDriveX SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec S1Cells S1Start S1BootDefs S1MainEntry S1MainEntryN S1ReadErr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1DirTail () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Drv;S1MainEntry2p1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedi59OSSVerify5KrLib3Drv9S1DirTail<dir_tail_pre00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib3Drv6S1Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib3Drv6S1Spec5t_dieC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Drv7S1Cells>stack_writableC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Drv6S1Exit9img_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Drv7S1Cells4cellC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C49OSSVerify5KrLib9RunRandom9rr_canaryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Drv7S1Cells<drv_cells_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C47Corelib4Init5Peano2ltK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Drv<S1MainEntryN9main_strNC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Drv9S1ReadErrBref_read_error_dotC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib3Drv6S1Spec8dot_pathC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Drv9S1ReadErr6re_ivsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op203".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL1.
Context {fx : FPState}.

Record dir_tail_pre {AMB : Amb} {RRND : RunRandom} (sp0 p1 : word) (tid : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x1006b8;
  dt_s2 : getr R 18 = p1;
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x100610 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x1005f0 8 0x1005f0;
  dt_canary : cell M 0x120928 8 rr_canary;
  dt_pagesz : cell M 0x120978 8 4096;
  dt_nlocks : cell M 0x12094b 1 0;
  dt_path : rdn RSEGS M p1 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0];
  dt_t8 : exists t8, rdn RSEGS M (Z_to_bv 64 (bv_unsigned p1 + 1)) 8 = Some t8;
  dt_cells : drv_cells_ok M
}.

Section DirTail.
  Context {AMB : Amb} {RRND : RunRandom}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw [a0s; dot_path] envv a_uid a_hwcap tid regs0 mem0.

  Theorem dir_tail : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) mem0 R M ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65814) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_S1DirTail ()) ["FXALL1"; "DirTail"] "p'0h02Hah12t8h21Hh37__arithh44__ffh58__varmaph65__with74__x1h84__x2h94Hfd2h:2Hhh;5Hlazyh<4Hpprh=4Hstrh>3Ht8h?5Htidrh@1MhA7McanaryhB6McellshC4MimghD7MnlockshE7MpageszhF5MselfhG6MstackhH4MtidhI1PhJ1RhK3RgphL3Rs2hM3RsphN3RtphO4SPhihP4SPlohQ3ShihR4SlenhS3SlohT2SrhU2_HhV7__sat10hW7__sat11hX7__sat12hY6__sat9hZ1ah[4cstrh\8dt_cellsi008dt_cellsh]5dt_t9h^2ivh_5modelh`2ppi019dt_canaryi025dt_gpi036dt_imgi049dt_nlocksi059dt_pageszi067dt_pathi075dt_s2i087dt_selfi095dt_spi0:8dt_stacki0;5dt_t8i0<6dt_tidi0=7dt_tidri0>5dt_tpi0?1xp&0p;1p;2p;3p;4p;8p;5p;>p;Op;<p;7p-1R0g0000R1p4p710p8P0g000QR2p4p710p8P0P2p4p7210p8g000nj10Tg001Sj11Tg0028j1VTg002Vj1dTg0039k208Tg003ej1OTg004Gj1wTg005>j1ZTg005`j32Tg006:j2cTg006Zj1RTg007:j1fTg0082j1QTg008Rk10>Tg009Fj13Tg009dj26Tg00:Jk206Tg00;Bk105Tg00<:j2LTg00<\k402Tg00=Sj2ATg00>=R0j8vTg00?>j1mTg00@3j5BTg00@ej2DTg00AZj1iTg00BXj1@Tg00CKj2FTg00D@j3KTg00Dcj2MTg00EUj2eTg00F2k20ATP2k30@Tg00G1k30?Tg00GNk30=TP1k30;Tg00HGj1:Tg00Hfj4JTg00I[R1j2=Tg00J7j2bTg00JTR2j2>Tg00Jok107Tg00Kgj3PTg00LGj2?Tg00LdR3j2_Tg00M>j1XTg00N;j28Tg00NWk204Tg00O7j3^Tg00ORk303Tg00OmR4j2\Tg00PEj2STg00P_j1~Tg00Q=j1}Tg00Q[j1zTg00RFj2HTg00Rij4UTg00STj2uTg00T6j2tTg00Tbj3sTg00UAj4rTg00V3j4xTg00V^j2YTg00W>l>qTg00X=j4pTg00Y6j4yTg00YRj2oTg00Yij3{Tg00ZFR5j1|Tg00Zfj1nTg00[]k100Tg00\Bj2]Tg00\jj3`Tg00]Nj2lTg00]lj4kTg00^Jj2aTg00^mj3WTg00_Pj8jTg00`4mO09Tg00a9k30:Tg00b3j4hTg00bdl<gTg00cIk70<Tf0R6#0#0p=E%06#0#1#0p=7%16#1p=<%06#0#0#0p=5%16#0p=[%06#3p=Ng00cmR7f1R8<0:6p=C%06#0#0#3p=9%06#1p=4%16#1#1#1p=IP7f2R9P8P6Chp=Gg00ebg00fAR:P4P5P1g00f_f5R1f4R5f3R4P9P8P6M<gp>01P8g00gAR;g00g`R<P<g00h@R=P6g00h`K0<p=Tg00i@R>/86p=;g00i^R?#0R@#1RA#VRB%0@RC#0RD#0RE#ERF#VRG#dRH+08%VDRD#dRI#O\Hg00jC%OH%w6%ZH321cHHRJ#R%f8%QJ32g00k9RJ#O&0>9%3@RK,6GRL+06&05L,LJ32p,3AMBRJp,4RRNDRLp,3sp0RMPMp,3a0sRNg00l1ROp,4envvRPH02RQp,3tidRR,AGRSp,4mem0RTP1P5GvP0PJPLPMPQPSPTf6R0P1p,2fxRUf7RV%1?#7#<#5#7#[#N,6GRWP0%m7R7DB/D1%iORX%@1'F'CP6fERYg00liRZ9KBK'M1AGMR[%0FR\#3'e,6G52HfFR]%1?R^#3=KBZ'M%1E#5#5#9,6G52HfGR_%3C=KBZ'M%0?#5#5#<#4#4#<#9,6G52HfHR`%1CRC#N=KBZ'M=2HQ20A`M1c::R`fJRZB0@::6B0?::640=X^`g00mE40;PZ%0?#5#5#<#E#7#9g00n>#:RZ#:R`#:#:RBPSCJ1=>S%1ARA#NRa,bKRb,=S'>fLRc%0?#E#5#7#I#[#9Rd%:B#:#:#:RBPdCJfMRd%0?#4#5#4#7#4#4#9PB&07LRLCJfNRe%0?#4#5#4#7#I#9PB%0\#5Rf#3CJfORg%7?#E#7#4#4#7#<#3PZP>CJ%RIRh#ORifPRj?GQ`%1A#N,6D16D>%QIRD5PIRA5PI,Lh32fRRk1AGQ%3?Rl'?,6GRm;GB1Lh6Rn52iX1h,_hP3PhfSR3?GmB=2inX1h%X3PUfURoPWfTRpP7DB/D3%@3,FX'C]\P6AGomB=2infVRm#Xg00n]/8[Rqg00oX,8[Rr%3E-04[=2:>RE'>Rsp,4HvspRt3^PqB03qst9^rEPrPJPM%QhRJ9PhO9PhNRNPPPRp,5rdrawp,5regs0PTp,3Hvap,3HvePtp,2MEPZ1\Z`1=lKRRPZPl1S:lP`PK1S:KJ01g010SR`#QRO%R`R`%~:Rr%}:RE%z:RsP:1H:lg011?1H:KCU'T1us=RlP6P9g011fRqg012FRu'S1t69=2qudAs:>8CrRub4b5b6PRP6b3Cx1YhN,\ZeM>qPMPNPPPZCpRPPhPZPNPDCyRD,YIRN/oZ5GTA{IDA,Lh52iRD1AGPRP,8[RA%1\#4#E#4#4#<#9R\,?[,8PRI%|NRZ%1^#<#I#I#I#3'8R^1?PZ,6G=GTB=2inX1h,_hRn'>Ri'>RB'>RT'>P2PDPTPUf\PWf[P7DBfZRP'D%@P,FX'CP6P2PAPBPUf`PWf_P7DBf^RP'D%@P,FX'CP6P2PIPiPUfdPWfcP7DBfbRP'D%@P,FX'CP6P2P^PnPUfhR2PWfgP7DBffR7'D%@7,FX'CP6PQPH%n61AG6RH#;%3FRF,bKRQ,=H'>PUPMPJfkPtfjfiP2P8PSPLfmflfWPmPoPpP3PkfQPjPgPePdPcPYf;RYP_&00N%;Z1]KF1=>KRZ%;F1=>Q[[%;KRNg012fR_A`KF8UW0%;Q\_^0N1]Ka%;a1=>b[\ZA`Ka8V_X0N%;b\_^0NPOP`P:1l:9P8PrCkPEPsP;P<P<P=P:1a:?R?g013BR=1a:@R@1H:\5W:CU,Ts%Z<P:%3CRC,H:9W:?P=%0f#E#5#9Rf,H:9W:@CU,TsGjPlPub4b5b6X7:X8:1?8\,861?8C1?9f'8[^7:^8:P6P[1AGVf=RGO3b3bYbVbWbXb[fKP]NO09b<b`XUnXR^P8P6O2n2001000000121000000X2iXQIP8P6O2n2011000000121000000X2BXSAP8P6O2n2011000000121000000X2TXTDP8P6O2n2111000000121000000bZbObPWBW>X1hP8P6O2n200100000012110?000W]W=WDWEWAWFW?WHWCWGWLWNWKWMf>PGf<PYf:f9f8PVP0P1P5P4P9P8P6O?n80000000010000001?110910210>10710:10310<10=10810110510410610;100WIW9W;W:W_W@WJo"). Qed.
End DirTail.

End FXALL1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
