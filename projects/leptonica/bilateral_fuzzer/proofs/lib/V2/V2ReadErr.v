(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev's channel-reader flag; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare SymExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2ExitBase V2MainEntry V2MemPreds.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2ReadErr_defs V2ReadErr_tail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2ReadErr () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2V2>V2ReadErr_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common9CliDriver4Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec9exit_codeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00C59OSSVerify5KrLib2V2>V2ReadErr_tail7re_segFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_tail4reF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_tail8re_segBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2V2>V2ReadErr_defs5srRE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_defs5knRE0C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2V2>V2ReadErr_defs4srF0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_defs3knEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib2V29V2ReadErr6valsREC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver8SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List=app_nth2_plusC69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2ReadErr_defs3spxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K45stdpp9bitvector;definitions2bv01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib2V2;V2MainEntry@regs_ok_by_indexC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2V2;V2MainEntry8all_regsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib2V2:V2MemPreds9img_clearC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib2V29V2ReadErr6re_ivsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic6eq_indC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Peano2le00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib6Common9CliDriver9SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z7add_0_lC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib2V29V2ReadErr<img_clear_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib5Lists7ListDef6Forall02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib2V29V2ReadErr9know_okREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V29V2ReadErr7re_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V29V2ReadErr:valsRE_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V29V2ReadErr9regs_okREC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib2V29V2ReadErr>ref_read_errorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0x46120); (0x46121,0x46169); (0x56169,0x561a0); (0x56288,0x76298); (0x561d4,0x56220); (0x56228,0x56240);
   (0x56248,0x56260); (0x56270,0x56280); (0x762b0,0x764d8); (0x764e0,0x764e8); (0x764f9,0x76500);
   (0x76508,0x76510); (0x76520,0x76528); (0x76530,0x76560); (0x76918,0x77000); (0, 0x1000)]%Z.

Section ReadErr.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Hypothesis Hrd2 : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17a94) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h04__x1h13HL0h27__arithh34cstrh45cstr0h54__ffh68__varmaph75__with84HL'0h98__sat114h:6__sat9h;5cstr1h<2HKh=3HK'h>2HLh?3HL'h@3HPlhA2HRhB3HR'hC6HnonulhD4Hpp1hE4Hpp2hF4HstrhG5Hstr'hH3Ht8hI1MhJ2M'hK2P0hL2P2hM2Q0hN4Q113hO2Q2hP1RhQ2R'hR4pathhS2pphT2t8hU4valshV5vals'hW1xhX1yp&0p;1p;2p;3p;4p;Hp;7p;Kp;5p;<p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000np4p710p1001Ip4p710p8g001gj16Tg002Lj1PTg002jj1WTg003Mj1JTg003mj14Tg004Rj2qTg005>j1ZTg005`j2FTg006Fj3dTg006]j1cTg0076j19Tg007Tj2<Tg0080j23Tg008Pj10Tg008oj2?Tg00:3j31j1\Tg00:Mj2ATg00;7j2CTg00;Tj2GTg00<Nj3UTg00=^j4TTg00>nj2STg00?Ej4KTg00@=j1RTg00@]j3bTg00A=j3QTg00AZj2ITg00B<j1aTg00CEj2`Tg00DAj1_Tg00EEj1^Tg00F8j2]Tg00G3k200Tg00GnR1j18Tg00HNj2~Tg00I1j3}Tg00INj2>Tg00Ihj4HTg00JOj1@Tg00K4j2|Tg00Kej2{Tg00LEj2yTg00Lcj1xTg00MAj1wTg00Mlj2rTg00NOj4[Tg00O:j2pTg00O\j2oTg00PHj3nTg00Pgj4mTg00QYj2NTg00R<j1lTg00R^j2VTg00S9p;IlIkTg00T7j7jTg00U2lKiTg00V1j1sTg00Vmj5tTg00Wfj2hTg00X[j2uTg00Y[j3vTg00ZZl<gTg00[?j7fTg00[cj7zTg00\Gj8eTf0R0#6#6p=2f1R2/30#8p=:%40#4p=5%00#0p=E%00#0#0#0p=L%00#0#0#0#0#0#0#0p=Y%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=;g00\kR3?120p==P3g00]JR4P0P1P2f2R1f3R5f4R6f5R7f6R8f7R9f8R:M<gp=Og00]hR;/<0p=7P2g00^FR<g00^eR=P=g00_ER>P0g00_eFfp=BP4P2g00`EP0C[p=MP1P<P=P=P>P2P0Fzp=XP5P<P=P=P>P1P2P0Gep=Dg00`lR<#6R?#6R@#6RA#PRB#WRC#JRD%6ARE#2RF#PRG#WRH%JHRI%4?RJ#P/qHRK%ZC\HRL1FB;RB=dC7#c1:C8%4<#5RM#2#9RN'<13H6g00aQRO#0RP#0RQ#E#LRR#0#E#L#Y#;RS'=1?7Op,3sp0RT51H1?8Q=1H:1AGTRUf9RV,AG'<f:RW,AGf;RX,:C'C%9A'C%2F#2#2#2#2#2#2#2#9,CU'<p,2BLRF/GVg00b0;U:g00blRA1GFWP:g00d>CT%ZDRYPAPVf=RZf>R[,3C/SPCK%RC9bCBRB9QC[,ID31PAPW1AG[f?R\,:C'C,FGPRCK1IDZ51YPTPFp,5modelRRp,4HvspR]p,2HhR^p,5HlazyR_f@R`P\1:C`Ra%9?R?%a`Rb'`%_?%^RR?']+00RcP[PZf<RdPX13HZRZ/=S%8ZRe%4@#5#9R@514Rf%\3Rg%\4Rh%82%805141=201~203}XX3XW3R3PZPe1>4ePSP@1>4@RiM9OP:CHRjPffA,3CRk#@Rl%8k#7Rk13H\Rm#@Rn%8m#7Rm%9ERE,|URo%7U%7E1{UE#7[[REg00e:RU#RRp%JURU1y42Rq%x4Rr%w4RsP41r4<Rtg00efPtC['B1ps>R>P0P1g00fMRug00fmRv'>1o01=1uvdAn4;2CmRvb5b6b7X04RuA1400^04RwP0fE,:CRxO1b2b:b4b3b1PjPfPlPkPnPmPoPEPpPUPqPrPs1N4;/Mt,BsR;%l=R=Ps1N4N,Mt,BsRmP=%4M#5#5#5#5#5#5#9RM,N4,Mt,Bs9Xs;CDCDP>Pvb5b6b7X04%70Rt1<2NRn%71Rk1<1M'V[[^04P0PxP5P[O3b2b:b4b3b1PWP:P9P8P7P6P5P1P2P013H1%ES#Y#;#;#;#;RW#E#L#;#;#;Rx'=1?5O=1HT1?6QfD51H1?7WfF,:C,FG51H1GF8g00gM;U7PA1GF9P7g00hHCTPAP8fHRWfIRQ,3C/SPCKAQCQB,ID51YPTPFPRP]P^P_p,4Hfd2p,4Hrd2fJR_PQ1:C_PVP:P913HVRV/=x%8VR9%2J#4#5#9RJ514R:PgPhP3PVP91>49PxPJ1>4JM9OP8CHRJP:13HWRW/=S%8WRx=14@R9PgPhP3PWPx1>4xPSP@PiM9OfCCHRiP9fL,3CR@#@RS%8@#7R@13H_RH#@Rx%8H#7RH%@ZRZ%7eRePoPEPuPwP0fQ,:CRCO1b2b9b;b4b3b1b8PJP:PiP9PSP@PxPHPZPePoPEPpPUPqPrPsP;P=PsPmP=AXs;mCDCDP>Pvb5b6b7X041<1N,Vk\n\t^04P0PCP6P_O3b2b9b;b4b3b1b8P8P7P6P5P\P[P1P2P0MIkWGW=WBWNWOWMW?XJLXQKXVIPTPFPRP`P\PaPcFjeMKig00iBPd%6<#5#5#6#4#6#4#2#4#6#4#2#9,FGPX%sADt/hR1ub?5vAeWHWFW<WAWEWDWLWKW>W@WCWIWPWUXTDWSWRo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x56270.
  Hypothesis Rs2 : getr R 18 = pp.
  (* [comment removed for export] *)
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x561c8 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x561a8 8 0x561a8.
  Hypothesis Mpagesz : cell M 0x76528 8 4096.
  (* [comment removed for export] *)
  Hypothesis HBL2 : length (nth 2 BL []) = 8%nat.
  Hypothesis Mguard : bytes_at M 0x764d8 (nth 2 BL []).
  (* [comment removed for export] *)
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : length valsRE = 39%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h01np;1p;2p;3p;6g001gj13Tg002Lj1ATg002jj1=Tg005`j28Tg00@=j1@Tg00@]j31Tg0080j24Tg00j:j1<Tg00A=j39Tg00>nj25Tg008Pj12Tg00:3j36Tg00INj2?Tg00kBj1>Tg001Ij67Tg00lRj3:Tf0R0#2#2#2#2p=0%20#2p=;g00\kR1g00`l#3#3#3#3#3#3#AR2#=R3p,3sp0p,2ppR4p,3tid,82%@3R5513913491349134513513R4'4R6p,1RR7#<R8g00]h,82=135R5593R2,43R9'5g00aQ#0#0#0#0#0#0#0#0R:#2#;#0R;9610X01P11438R<1435R='51560=61;X01P1P:150=,56=61;X011?1;P<%>7E7P9A:385E7A9342,43A:342E7g00m1,43=61;eo"). Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h01ih12Hih21bh31np;2p;1p;3p;4p;6p;5g00mij2<Tg001gj12Tg002Lj1ATg002jj1OTg00j:j1KTg005`j25Tg00@=j1DTg00@]j31Tg00A=j3:Tg00nAj46Tg003mj1BTg00Gnj19Tg00n]j28Tg00:3j34Tg00INj2NTg00oVj2MTg0102j4LTg010Nj6JTg001Ij67Tg0080j2=Tg00kBj1FTg011Xj6ETg00>nj2@Tg0125j5GTg008oj2;j1HTg012Wj1CTg013^j2ITg014fj2>Tg008Pj13Tf0R0#3#3p=?%30#3#3#3p=0g00\kR1g00aQR2#?#0R3#?#0#0#0#0#0#0R4,<0g00`l#2R5#2#2#2#2#2#AR6#OR7P7f1R8p,1RR9#KR:g00]h,56R;%D7R<517R=5:7R>P;C6R?%B5#AR5f2R@#9'5,899470X27RAP7P7P8P:P;C6RBPAP7%98,55,89RCPA1N7CP7P8P1P7%90,55,89X01R51M24CLP;C6P7P5P8P4P;P0EJE7A47BCeP?P7P:P=P;P8P1P41<@0X31P01=7:%F9E7EEE7P7p,3sp0p,2ppR9p,3tid,56=17<917991799179517517R9,=7/@8R<A:79>R6P;C6P7P9P>P;P8DGE71;6<=47Ceg00m1R61@38R8';=47Ce%H6p,2BL#C'I/>8=47Cep,1E/>8=47CeW1W0o"). Qed.

  Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h01zh12b1h22b2h31nh41Hh51bh61kp;1p;2p;3p;6g001gj17Tg002Lj1HTg002jj18Tg014fj2?Tg005`j29Tg015kj2ETg00:Mj20Tg00;7j22Tg00:3j36Tg016ej3>Tg017Ij24Tg0076j1<Tg017oj2GTg00Kej23Tg00INj2FTg018Lj3DTg0193j1;Tg01:5j2:Tg01:dj3CTg01;Lj2BTg001Ij6=Tg01<Hj1ATg01=Bj2@Tg00]JR0f1R1f0R236p=1P0f4R3f3R4f2R5P1P2E=p=5g00`l#7R6#7#7#7#7#7R7#HR8#8R9p,1ER:g00aQ'?R;1982R<'ER=p,3sp0,08R>/21R?,98R@9692X59g01>KRA%82RB%81RCg00R^%85?61210451041'1RD[10511052'1%84?651[RE%83?645\DA>512P2n2001000000120000000W2W1W3PE^2C^1B^3AP2P81981,08RA,2>RB,98RCP@148B12>5RE,98,08RD,12X001481R412>2R3,48/1DX00148?RD1485,2>,48/12X0012>4RF%<6%<7'GR7'3148ER6,12X001317RG1337/16X0013?7R61357,2>/37/12X00P613E7,12X001F0612>G/37AD1>7D5PD%;?D5P4%;1D5148F%;FD5108@1:8?D5PA1:81D5108C1:8BD5O4b41983R3969=eg01>i?C;<1B;<E=%A2,@:=693eX60o"). Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 all_regs];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRE : regs_ok E srRE0 R.
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "p'0h02Hih11ni001nh21zh32Hah44__p1h54__x1h61bh72b1h82b2h91ih:1xh;1Hh<2H0h=2H1h>4HBL0h?3Hi0h@7__arithhA4__ffhB6__sat3hC6__sat4hD6__sat5hE8__varmaphF5__withG4cstrhH5cstr0hI1yp%0p&0p;1p;2p;3p;4p;6p;<p;7p;8g003mj1<Tg001gj14Tg0076j17Tg002Lj1TTg00:Mj2@Tg007Tj2QTg008PR0j10Tg00miR1j21Tg002jj1ATg01?Uj3NTg01@8j1MTg00nAj4HTg01=Bj2ITg01AAj2yTg005`j2RTg014fj2]Tg01A^j1pTg01:dj3nTg00:3j38j1bTg015kj2YTg016ej3iTg00;7j29Tg017Ij2FTg017oj2ZTg00Kej2DTg00INj2CTg018Lj3hTg0193j1PTg01:5j2OTg01;Lj2gTg001Ij6STg00n]j2WTg01B<k105Tg01CEk304Tg00GnR2j1GTg01DNR3j2LTg00Ihj4eTg003Mj1dTg00@=j1cTg0080k200Tg00HNj2~Tg00I1j3}Tg00ZZl<`Tg00JOj1XTg01Djj2|Tg01ERj3{Tg00K4j2xTg01F6j1wTg00LEj2uTg01FTj4^Tg00Lcj1sTg00MAj1rTg00QYj2VTg00Mlj2qTg00NOj4\Tg00R<j1oTg01G2j6tTg00O:j2vTg00O\j2mTg00PHj3lTg00Pgj4zTg01GVj4kTg01HZl<aTg00[?j7jTg01I?j3KTg00\Gk801Tf0R4#<#<p=;%44#4p=J%44#4#4#4p=f%44#4#4#4#4#4#4#4p=>f7S00f6R5f5R6f4R7g01IbR8f3R9CH'Wf2R:g01J^R;f1R<g00b0R=P4CH'I38p=21]<4,C:p=31W:<=894p=Ug00]JR>?8<4p=:P>P7P9P:P<P4ESp=E1I<4989:p>031979/9:/9</94p=6g00\kR?P?P>P>P0P2P2P5g01KgR5P6P7P?P?P>P>P0P2P2P9P5P:P<P4M<aM<ap=5P?P>P1P2P3g01LKP6P7P9P:P<P4M<`p>02g00]hR3/Q4p==P<g00^FS01g00^eR1P1g00_ER5P4g00_eFjp=[AK>79=K>:=K><=K>4p=?P9Q01P1P1P5P:P<P4L01p=_%04#0#0#0p=Bp,4SPlog00`lR0#<R@#;#;#;#;#;#;#;#4#J#f#>#>#>#7%40RA#4RB#4RC#4RD#4RE#4RF#TRGp,3sp0RH'@RI'Qp,4SPhi%4FRJ#>#>#>#>#>#7,QIp,1ERKP=p,1RRLg00aQRM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm,14RnP?%AGRoPL%<ARp#TRq#ARrP<g01LmRs9Nq3RtPKP<%M3RuG2^0nP<11MmA3oKSPoPLPrPMP8PtCHP;PMP=PuCH,IKCUeW0P?%04R=/1mPoPLPr%0<R;PtPKP;PuG2]0P411NmA3oKTPoPLPrPNPtPKPNPuG2eW0P?%0=R=/1mPoPLPr%0;RNPtPKPNPuG2]0P411OmPo%7J,yIR8,RGRng01>iRv1]KMRw%pJRJ,RGRx3nS0298o4X6oPo1YwxA8on4X6og01>KRy%A4Rz%A<R{g00R^%A:?8<41@9:1@9<':R|[1@:<1@:4':%A9?8:<[R}%A7?89:\|Ai:<4P4n2001000000120000000W8W7W1P}^8{^7z^1yP4PGPn1@GxS03,9IRy,RGRz1FG8R{1@GzS04,:4X2>1FGy1:{4X2>1FGJRz19I4R},FG,:{X2>%7ARA%7F'ZRF,D8R|19IzR7,FGS05,:4X2>1D7F1:|4X2>S061DJFR~1D}F,:|X2>19IJ/DFR|Q061C>|19I~/DFAhJIFDEPz%PJDEQ05%P7DEP{%P8DEQ031OGJDEQ041OGyDE1@Gn1OG8DEO4b=1YHx98oneQ021gwxESANqAs,WLRxp,3RspESPoPxPK&05M%MJ604vH03ePoPLPrPOPtPKPOPuG2eW0P?%0=R=/1mPoPLPr%0NRvPtPKPvPuG2]0P411Pmp,3RgpPoPL%7@=Nqs%<D#4#J#>#7#M,IKCUePoPLPrPPPtPKPPPuG2eW0P?%0=R=/1mPoPLPr%0vRPPtPKPPPuG2]0P411Qmp,3RtpPoPL%7B=Nqs%40#<#4#;#4#J#<#J#<#;#f#7#M,IKCUePoPLPrPQPtPKPQPuG2eW0P?%0=R=/1mPoPLPr%0PRQPtPKPQPuG2]0P411RmA3oKXPoPLPrPRPtPKPRPuG2eW0P?%0=R=/1mPoPLPr%0QRRPtPKPRPuG2]0P411SmA3oKYPoPLPrPSPtPKPSPuG2eW0P?%0=R=/1mPoPLPr%0RRSPtPKPSPuG2]0P411TmA3oKZPoPLPrPTPtPKPTPuG2eW0P?%0=R=/1mPoPLPr%0SRTPtPKPTPuG2]0P411UmA3oK[PoPLPrPUPtPKPUPuG2eW0P?%0=R=/1mPoPLPr%0TRsPtPKPsPuG2]0P411VmA3oK\PoPLPrPVPtPKPVPuG2eW0P?%0=R=/1mPoPLPr%0sRVPtPKPVPuG2]0P411WmA3oK]PoPLPrPWPtPKPWPuG2eW0P?%0=R=/1mPoPLPr%0VRWPtPKPWPuG2]0P411XmA3oK^PoPLPrPXPtPKPXPuG2eW0P?%0=R=/1mPoPLPr%0WRXPtPKPXPuG2]0P411YmA3oK_PoPLPrPYPtPKPYPuG2eW0P?%0=R=/1mPoPLPr%0XRYPtPKPYPuG2]0P411ZmA3oK`PoPLPrPZPtPKPZPuG2eW0P?%0=R=/1mPoPLPr%0YRZPtPKPZPuG2]0P411[mA3oKaPoPLPrP[PtPKP[PuG2eW0P?%0=R=/1mPoPLPr%0ZR[PtPKP[PuG2]0P411\mA3oKbPoPLPrP\PtPKP\PuG2eW0P?%0=R=/1mPoPLPr%0[R\PtPKP\PuG2]0P411]mA3oKcPoPLPrP]PtPKP]PuG2eW0P?%0=R=/1mPoPLPr%0\R]PtPKP]PuG2]0P411^mA3oKdPoPLPrP^PtPKP^PuG2eW0P?%0=R=/1mPoPLPr%0]R^PtPKP^PuG2]0P411_mp,3Rs2PoPLPrP_PtPKP_PuG2eW0P?%0=R=/1mPoPLPr%0^R_PtPKP_PuG2]0P411`mA3oKfPoPLPrP`PtPKP`PuG2eW0P?%0=R=/1mPoPLPr%0_R`PtPKP`PuG2]0P411amA3oKgPoPLPrPaPtPKPaPuG2eW0P?%0=R=/1mPoPLPr%0`RaPtPKPaPuG2]0P411bmA3oKhPoPLPrPbPtPKPbPuG2eW0P?%0=R=/1mPoPLPr%0aRbPtPKPbPuG2]0P411cmA3oKiPoPLPrPcPtPKPcPuG2eW0P?%0=R=/1mPoPLPr%0bRcPtPKPcPuG2]0P411dmA3oKjPoPLPrPdPtPKPdPuG2eW0P?%0=R=/1mPoPLPr%0cRdPtPKPdPuG2]0P411emA3oKkPoPLPrPePtPKPePuG2eW0P?%0=R=/1mPoPLPr%0dRePtPKPePuG2]0P411fmA3oKlPoPLPrPfPtPKPfPuG2eW0P?%0=R=/1mPoPLPr%0eRfPtPKPfPuG2]0P411gmA3oKmPoPLPrPgPtPKPgPuG2eW0P?%0=R=/1mPoPLPr%0fRgPtPKPgPuG2]0P411hm%0mRq93oKPoPLPrPhPtPKPhPuG2eW0P?%0=R=/1mPoPLPr%0gRhPtPKPhPuG2]0P411im%0qRq93oKPoPLPrPiPtPKPiPuG2eW0P?%0=R=/1mPoPLPr%0hRiPtPKPiPuG2]0P411jm%0qRq93oKPoPLPrPjPtPKPjPuG2eW0P?%0=R=/1mPoPLPr%0iRjPtPKPjPuG2]0P411km%0qRq93oKPoPLPrPkPtPKPkPuG2eW0P?%0=R=/1mPoPLPr%0jRkPtPKPkPuG2]0P411lm%0q93oKPoPLPrPlPtPKPlPuG2eW0%0=/1m%0kR=/1m%G<Rl%70R0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6%7ERE'LS02P=1940X:>R=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=P=PlO1S04O1S03O1S05O1S06O1S07O1S08O1S09O1S0:O1S0;O1S0<O1S0=O1S0>O1RqO1RBO1R@O1RJO1RMO1RxO1RwO1RnO1RHO1R8O1RGO1RyO1R{O1R7O1RzO1RFO1R~O1R|O1R}O1P=PkP}P=PjP|P=PiP~P=PhPFP=PgPzP=PfP7P=PeP{P=PdPyP=PcPGP=PbP8P=PaPHP=P`PnP=P_PwP=P^PxP=P]PMP=P\PJP=P[P@P=PZPBP=PYPqP=PXQ0>P=PWQ0=P=PVQ0<P=PsQ0;P=PTQ0:P=PSQ09P=PRQ08P=PQQ07P=PPQ06P=PvQ05P=PNQ03P=P;Q04P=P<Pl1C>lF5F5F5F5F5F5F5F5F5F5F5F5F5F5F5F5PmPE1C>EJ02P4CeQ02%TC#ARm%dmPOp,2BL%cmCH+00Rm=8?U%GmRO%7CRC':R=P?P>%b?P2%b>%G4,:lA8?<41~<43}XI?X:?PmPO1C>OPUPC1C>CM<`p,4HBL2CeP=%X9%G9#=%Xm%=O%<p#4#7RO,|A1L3A%=O1ZAORm,L3[[%=AR=g01MIRCA{AO<UW3%=m\C^3=%7DRD,xI%=I%=D1DID#=[[p-0RDg00e:RI#c%dIP>%w>RIP<P>1u><P<PIC^C^%s>%r>RIP>1V>3g00`E1q>pRpC\,[I%o1R=PIP>Pp1V>0RpPpPpPpD?PpPpPpPpD?PpPpPpPpD?PpPpPpPpD?PpPpPpPpD?PpPpPpPpD?PpPpPpPpD?PpPpPpPpD?g01Me1V>EC\,[IP=PIQ01P1P1P5P9EtC_C_1vI5P4P:g00fMRIg00fmR5'C1m4:=8I5dAl>3<CzbAbEbFX5>W4%=4P<P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6P0P0P0P0D6/LEP9[[^5>^4DP4PoPLPrf9Rr#B#B#B#B#B#B#B#BRLPtPKPLPuG2%GrP6Q00O4b@bBbCbDbHbGb>b?W0X9?P4O1n0110001020111100X1?P4O1n0110001020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020111100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020011100X1?P4O1n0110000020111100X1?P4O1n0110000020011100X1?P4O1n0110000020011100P4O1W0X9?Ckb<b;o"). Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h03Hinh12hih22ivh32loh41xp;2p;4p;3p;6g01NLj28Tg01Nlj41Tg006Fj30Tg000Qj32Tg01OLj37Tg01Oij36Tg0000j34Tg01Pej33Tg01QGj65Tg00]JR01800R1P0P0f1R2f0R3C1g01QbR430p,1MA2003A700336X21R5=414R6A0134P5P2O1[^41R7[P6\7A3154p,4MimgP0P0f2P2C1P3E5W0X10W3o"). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRE0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -6144513 + d)%Z with (bv_unsigned sp0 - 6144513 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mself.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg.
    - (* [comment removed for export] *)
      unfold elenZ, estart. cbn [a_base a_off edenot]. rewrite (u_small 8), (u_small 0) by lia.
      split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
      change (eb E 2) with (nth 2 BL []). split; [rewrite HBL2; reflexivity|].
      intros i Hi. rewrite Z.add_0_l. apply Mguard. rewrite HBL2. exact Hi.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mpagesz.
    - kimg. - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
    - kimg.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17a94) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h02Hah14__x1h24__x2h34__x3h44HBL0h53HPlh66Hnonulh74Hpp2h84Hstrh93Ht8h:7__arithh;4__ffh<7__sat10h=7__sat11h>6__sat9h?8__varmaph@5__withA4cstrhB5cstr0hC4pathhD2t8hE1xhF1yp;1p;2p;3p;4p;<p;Ap;7p;8g001gj10Tg002Lj1LTg002jj1GTg003Mj1STg005`j2NTg006Fj3bTg006]j1^Tg0080j27Tg00GnR0j13Tg003mj1<Tg0076j18Tg007Tj29Tg00:Mj2PTg00;7j22Tg005>j1eTg008Pj14Tg00>nj2aTg00?Ej4JTg00@=j1QTg00@]j3MTg00A=j3]Tg00AZj2KTg00:3j35j1HTg00INj2:Tg00nAj4\Tg00HNj2[Tg00I1j3ZTg00ZZl<YTg00Ihj4XTg00JOj1FTg01Djj2WTg01DNj2ETg017oj2VTg01ERj3UTg00K4j2TTg00Kej2qTg01clj2DTg01dUj3RTg01e>j2pTg00LEj2ITg01F6j1oTg01FTj4OTg00Lcj1nTg00MAj1mTg00QYj2@Tg00Mlj2CTg00R<j1dTg01I?j3?Tg00O:j2fTg00O\j2gTg00PHj3hTg00Pgj4iTg029[j1`Tg02:VlAjTg00NOj4kTg00[?j7_Tg00\Gj8lTf0R1#0#0p==%<1#<p=6%01#0#0#0#0#0#0#0p=;g00]hR2/91p=1g00]JR3f1R4g00`EP1Ckp=>P4g00^FR5g00^eR6P6g00_ER7P1g00_eF_p=A%01#0#0#0p=cf3R8P5P6P6P7f2R5P4P1Glp=Bg00`lR9#0R:#=R;#LR<#GR=#SR>1N<2R<=b=4#^17=5#3%<9#6R?#=#8'9%0;R@#=RA#LRBp,2ppRC'PRD17=8#3'2%8;R;'2p,3sp0RE,PBRF%;A#;#8RA'2'9%e>RGg00blRHp,1MRIPCf4RJ,7=g00aQRK#4RL'aCJ%Q=RM9M=<9]=J,K>35PHPIf5RH,7=#3,2D,NB%4LRL#4R<#4#4#4#4#4RNCJ1K>J55Gf6PCPHg00m1p,1RPIPJP8g02;O%GBRB/:E1:BCp,4Hpp1P5g02<Kg00\kRBP>PLp,2BLPMC\,7=RM;5N%3MRC=53;REPBP3%HBP0%H3%34%31553A5B411[413ZXFBXEBPMPC1:3CPNP;1:3;M<Yp,4HBL2CXPEf7,7=RE#F%3E#1%FM%1C%8:RC%<:RM#<#0#8RE'W1E2C%1E1VCERN,E2[[%1CRBg01MIR0AUCE4UW0%1N\0^0B%8@R@,TF%1F%1@1qF@#1[[g00e:R@1D3<1D3L1D3K5R35R3g028K'p%Q@3M%S@P31I35P4P31I38P8%o3COCO%n3%m3R@1@321C3MRM'>,A@%d6R6P@1C39R9=?3M1@3;RM5?31C3:R:1@3A5?3RK'>,A@P6P@%6?#6#6#6#6#6#0#=#c#;#;#;#8R?,@3/>:,A@P6A?39M/>K,A@CBCBCB1f@7P1P5g00fMR@g00fmR7':1g15=5@7dAh324Cib;b?b@X13X23X33%151248/2;125A'919?8128;12JA'9[[[^13^23^33P1f=,7=#3PFPDPHf9p,4SPloO6b:b>b<b=bBbAb4#`P4P1MAjW9W8W7W5W6XD>WCo"). Qed.

  Corollary ref_read_error_dot : forall (t8 : list byte),
    (bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0] ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17a94) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2ReadErr ()) ["ReadErr"] "h01xh14HBL0h27__arithh34__ffh47__sat10h57__sat11h66__sat9h78__varmaph85__with94cstrh:2E0h;1Hh<2Hah=4__p1h>4__x1h?4__x2h@1yhA4Hpp2hB4HstrhC3Ht8hD1mhE1nhF2t8p;1p;2p;4p;3p;6p;<p;7p;8p;Bg001gj15Tg002Lj1RTg002jj1cTg003Mj1DTg00:Mj2<j1gTg003mj19Tg0076j14Tg00;7R0j20Tg007TR1j21Tg005>j1[Tg008Pj17Tg00?Ej4ATg005`j2@Tg00@=j1FTg00@]j3PTg00AZj2GTg00:3j32j1HTg01h:R2j2lTg02=Fj6eTg00nAj4dTg0080j2NTg00GnR3j1;Tg00HNj2_Tg00I1j3^Tg00ZZl<ETg00Ihj4]Tg00JOj1\Tg01Djj2ZTg01DNj2CTg017oj2YTg01ERj3XTg00K4j2WTg00Kej2VTg01F6j1UTg00Lcj1TTg00MAj1vTg00QYj2STg00NOj4QTg00R<j1uTg01G2j6tTg00O:j2sTg00INj2OTg00O\j2qTg00PHj3pTg00Pgj4oTg006]j1MTg006Fj3nTg01kjj1kTg01k?j4ITg01lHj4fTg00LEj2iTg01FTj4jTg00Mlj2BTg01I?j3=Tg02=cj7mTg00[?j7bTg00\Gj8aTg01HZl<rTg025:lB`Tf0R4#5#5p=3g00]JR5/O4p=6g00]hR6/14p=81S54p=:f1R7g00^FR8g00^eR9P9g00_ER:P4g00_eFbp=>f3R;P8P9P9P:f2R<P7P4Gap=Kg00\kR=P5P5P5P3P3f5R>f4R?P;P<P7P4M<rp=hP5P5P1f7R@P1f6R1P>P?P;P<P7P4M<Ep=JP5P7g00`EP4CQp=?P5P5P5P5P5P5P0P4P7P<P0P;P?P>P1P@f8R@f9MB`p=Lg00`lR>#5R?#5R0#5RA#RRB#cRC#DRD%5ARE#3RF#RRGp,2ppRH'<RI%90#4R0'0p,3sp0,<GRJ%3F#3#3#3#3#3#3#3#4RF'0RK'1%[DRLg00blRMp,1MRNPHg00aQ#7RH#7ROCA%9?#9RP#9#5#4RQ,@BRR1@B6RS%FCRT5PC5PC,GD32PMPN%4>RN,0IRM,@G%7O#7#7#7#7#7RGCA1GD<52Lg02>cRLP;A2CRSR;g027LRU'lRVP2P;PUPUP4PCP5%gBPRPSP4Ee1<BR1<BS525PDPOp,2BLPTCd,NCRT=2=G%;TRO%4ARA525RDP=P5%H=P3%H5%;7%;4R3525A2=741_743^X@=X0=PTPO%6OPGPA%6ARGM<Ep,4HBL2C]RBPD%\TRT%8ORO%4?RR%5P#4RP'ZR21C6R%8P1YRPRW,C6[[RX%8RRYg01MIRZAXRP7UW<RP%8W\Z^<YRY%4ERE,WJRZ%8J%8E1VJE#8[[REp-0RWg00e:RR#FR[%DRRR%U5R\%T5R]%v5R^P5%:Qg00ef1S56CQ,>^%u9R_P^P8P9P9P:P<EtCK1s^:R:P4P<g00fMR9g00fmR8'O1q4<=298dAp567CoR8b3b7b8W=A25Q6P7[^=WP4PUP1O2b2b6b4b5b9b1b:X:;P4O1PUPUP4n010000000X;UP4O1n200100000021100010000W;%MVeAnCSL#Me%;HRS%9>#9#9#3#4RV'111NVRUP4X05R;1174#kX@5X05R1PSPNP;P;%63X0=PHPN%6NEhRHPVPV%6VGJPBPDPTPOP2PXPPPYPZPEP[PRP\P]%:NR=%:V'?,>^P:P8b3b7b8PUP4b2b6b4b5b9b1CI1NCL#;RL/1Ve10ISRV/0ARC/1K10MARU/1KP;P1PCPUP;P;P;P5P5g02971074Cf#6XD5XE5RUPVPMP;P;P;PUPIPI%6IPSPNPHM:LPAPAPGM:LPKPK%6KGJPBPDPTPOP2PXPPPYPZPEP[PRP51i5<P7P\CjP]P^1B5>R>%:05=51B5?%:F5=5R?'?,>^P_A=5>=%:A5=5/??,>^CKP:P8b3b7b8X>5X?51040107F'1107N/0A10<F'1[^>5^?5P4PJPIP@O3b2b6b4b5b9b1CI10IL/0A/1KeP7P4FmWCWBWAWFo"). Qed.
End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
