(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive RefMemcpyLib AgentLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SymAux RefPrintfLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1PrintfBufBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1PrintfBuf () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC49OSSVerify5KrLib8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C49OSSVerify5KrLib6SymAux7sregionC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indI59OSSVerify5KrLib3Drv?U1PrintfBufBase3pfH00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C49OSSVerify5KrLib6SymRun6stk_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Drv?U1PrintfBufBase5PF_FRC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K59OSSVerify5KrLib8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux;log_coveredC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux9same_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8SymDrive5kreadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?U1PrintfBufBase:pf_regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?U1PrintfBufBase3pfEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?U1PrintfBufBase:pf_know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymRun9run_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib3Drv;U1PrintfBuf7pf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C49OSSVerify5KrLib6SymRun;carry_afterC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX22evC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C49OSSVerify5KrLib5Frame9frame_modC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux@keeps_cs_of_sameC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib6SymAux6rdenotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux<regions_flatC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAuxAlog_covered_frameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib3Drv;U1PrintfBuf;adenot_var1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib<RefPrintfLib5rdn_2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf;adenot_lit0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses6eq_iffI59OSSVerify5KrLib8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf7pf_fuelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf8pf_stopsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?U1PrintfBufBase5pf_srC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?U1PrintfBufBase5pf_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf:pf_regionsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC49OSSVerify5KrLib<RefPrintfLib:mod4_shiftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefPrintfLib7bt_and3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib<RefPrintfLib9bt_and3_0C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib3Drv;U1PrintfBuf7pf_caseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3Drv;U1PrintfBuf5dirsAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4resAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4carAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib3Drv;U1PrintfBuf5dirsBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4resBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4carBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf5dirsCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4resCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4carCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf5dirsDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4resDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf4carDC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefPrintfLib:mod4_casesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf8pf_caseAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf8pf_caseCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf8pf_caseBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;U1PrintfBuf8pf_caseDC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL1.
Context {fx : FPState}.

Definition pf_stops : list Z := [0x65be8].
Definition pf_fuel : nat := 3000.

Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0xf00e8, 4); (SA (ELit 0) 0xf0110, 8); (SA (EVar 1) 0, 2)].

Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x65c94) mem rom) (mkst regs' (Z_to_bv 64 0x65be8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xf00e8, 4);
                          (Z_to_bv 64 0xf0110, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xf0110) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xf00e8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x65be8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_U1PrintfBuf ()) ["FXALL1"; "Package"] "h02Hah12Hkh27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81kh91zp;2p;1p;3p;4p;7p;6g0000j21Tg000Lj10Tg0011j18Tg001Oj2?Tg001lj24Tg002Hj29Tg002cj1ITg003Aj1CTg003dj2ATg004Aj23Tg004gj32Tg005Aj2;Tg005[j2<Tg006Ej2VTg006mj3UTg007Qj1TTg0081j1OTg008Qj1NTg008oj1LTg009Mj1HTg00:8j25Tg00:[j4:Tg00;Fj3BTg00;ij7DTg00<Mj2ETg00<oj2FTg00=[j3GTg00>:j4@Tg00>lj2JTg00?aj6KTg00@?j27Tg00A3j1>Tg00Akj2MTg00Bdj1=Tg00C\j2PTg00DTj1QTg00EKj2RTg00FCj7STf1R0g00FgR1g00GFR2P2g00GfR3f0R4g00HFFSp=6g00HfR5g00IDR6/14g00Ib#0R7#8R8%07#0#0#0#0R7#8R9'?R:,44'9P5P6%I7R7#CR;f2R<,A4,37137<32X951370R=,;;1376R>,<71V8914681169146:R?[[1168R@g00JGRAAU890UW0116:\A^0@g00JcR@#T%O@%N5%L5%H5R@P1P2P2P3P51556R2g00KOP2C:,6@P5P2g00L61558=B57C:,6@FD1E@3P4P<g00L]R@g00M=R3';1F4<=2@3dAG560C@b3b6b71166/9?P4b2b4b5,J6EK17>0=2;=ep,1ER>%>6/M0R0#='P%Q0'7=2;=e1R>0=2;=eW1W8o"). Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
Proof.
ltac2:(KReplay.run1 (kr_t_U1PrintfBuf ()) ["FXALL1"; "Package"] "p'0h02Hah14__x1h24Pbszi004Pbszh34Pcani014Pcanh46Pcan64i026Pcan64h56Pflagsi036Pflagsh64Pimgi044Pimgh74Plbfi054Plbfh85Plocki065Plockh95Psp16i075Psp16h:5PspHii085PspHih;5PspLoi095PspLoh<4Pstki0:4Pstkh=2Pwi0;2Pwh>5Pwendi0<5Pwendh?5Pwposi0=5Pwposh@7__arithhA4__ffhB7__sat65hC7__sat66hD7__sat67hE8__varmaphF5__withG1ihH1khI1phJ1zp;4p;1p;2p;3p;8p;6p;7p100M]p4p70R0p100NPp4p710p8P0p100Nlp4p710p8g00OHR0j4vTg000Lj10Tg002cj1RTg003Aj1[Tg00PFj19Tg00Pej1dTg00Akj2XTg00EKj2TTg003dj2GTg004Aj25Tg004gj32Tg005[j2OTg0011j1>Tg00Q]j2tTg0000j2:Tg00R=j11Tg00Rbj4\Tg001lj2CTg002Hj2DTg00STj1STg00T6j1QTg0081j1PTg00TXj2?Tg00U`j2BTg001Oj2uTg005Aj2ZTg00VBj2sTg006Ej2rTg006mj3qTg007Qj1pTg00W3j2oTg008oj1nTg009Mj1jTg00:8j2LTg00WQj2iTg00;Fj3fTg00:[j4UTg00X4j8eTg00<Mj2cTg00<oj2gTg00=[j3hTg00>:j4bTg00>lj2kTg00?aj6lTg00@?j2WTg00Bdj1aTg00C\j2mTg00DTj1`Tg00XXj4_Tg00FCj7^Tg00;ij7]Tf0R1#0#0p=E%01#1p=4%01#0#1#0p=7%01#0#0#1p=A%01#0#0#0p=3%01#>p=F%11#1p==%11#1#1#1p=Y%11#1#1#1#1#1#1#1p=I%11#1#1p=<%11#0#0#0p=H%11#0p=@f1R2%01#0#>'5p=6g00YIR3f2R4P2P1C_p=;%>1,52p=M%01#1#0#0p=Kg00IDR5/:1p=8g00HfR6P2g00KOP1CUp=NP2g00FgR7g00GFR8P8g00GfR9P1g00HFF^p=JP4P7P8P8P9P2P1F]p=Vp,2PHp,3memR:p,2spR;p,1wR<p,3canR=CvP0P:P;P<P=g00IbR0#0R>#ER?#0R@#ERA#RRB#[RCp,1ERDg00Zh#9RE#dRF/X4'T1G<4,5B32P11OB;RG%>@R@'tRH=265%00#4#7#7#A#3#F/:G%=0RI#1#Y#I#I#IRJ#<#Y#I#>,:GP3P:P;g00[GC\%3AR;#0#3#F/:1%4I#=#H#3#3#F,C1'D%R?#[R?#SP:15B2O1%Q?32[^G6%P?R?#SRI%<0#3#3#=#@#@,6B%9E#9#9RE5;:%1>,MB,?E,B?32%<0#E#3#K#7,6B%9E#9#9#9R35;:%E0#H#=#4#3#7,6B,?3,B?52I%<0#E#3#K#K,6B=;:315B<RK,?3,B?52I%00#4#A#H#3#K#FRL/:<%00#4#A#@#H#3#=#FRM,:<'D%<0#3#A#4#7,6B=;:31MB;,?3,B?52I%<0#3#A#4#=#4,6B=;:E1MBJ,?E,B?RJ52I%<0#3#A#4#=#@,6B=;:E=2IJ%70#7#4#@#@#7,6B=;:315B=,?3,B?52I%8=%>>R>%>ARA'uRI,C='DP6P<fNR=,G1,5B1G<=,5B52CXJ6fMR=,G<,5BR?,ZC1OBK1sG@%8G%8@%8H[[1r>A1C5>%8A1C5I[[%8>RHg00JGR@Aq>A2UW0%8I\@^0Hg00JcRH#p%PH1o62%n6%j6RHP7P8P8P91L6L1i60R0'N,JH1L6M,N0,JH5VH%Q81L65/N0,JHP6P0g00L61L6>=f6BCU,JH5VHGe1cH9P1P4g00L]RHg00M=R9'Z1g14=2H9dAh652CbbAbEbFX161:L11:1M'D%821C2I'D[^16P1P<f9RIO2b@bBbCbD,k<El1WK==2C?e1XF=R=#a,mD%`='W=2C?e1TD==2C?eW4W3W7W8W2W=W?W>W5W6W<W:W;W9f=f<f;f:PIf8f7f6f5f4f3P4P2P1O>n4000010000001>110710910810:10410310<10=10;100106105101102bIXH6o"). Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x65c94 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x65be8 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0xf0110 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0xf00e8 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
Proof.
ltac2:(KReplay.run1 (kr_t_U1PrintfBuf ()) ["FXALL1"; "Package"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Hh77__sat65h87__sat66h97__sat67h:1bh;1Bh<6__sat0h=6__sat1h>2B0h?1rh@1xi001xhA2B1hB2HahC3HmshD1RhE4__p1hF4mem'hG2HKhH3HK'hI2HRhJ3HR'hK6HcarryhL4HcovhM3HlfhN3HpchO2HrhP4HrunhQ5HsamehR3HschS3HsphT3Hw1hU2K1hV2K2hW2K3hX2K4hY4Pbszi014PbszhZ4Pcani024Pcanh[6Pcan64i036Pcan64h\6Pflagsi046Pflagsh]4Pimgi054Pimgh^4Plbfi064Plbfh_5Plocki075Plockh`5Psp16i085Psp16ha5PspHii095PspHihb5PspLoi0:5PspLohc4Pstki0;4Pstkhd2Pwi0<2Pwhe5Pwendi0=5Pwendhf5Pwposi0>5Pwposhg2R'hh2Z0hi4dirshj1ehk3hs'hl1ihm3kn'hn1lho1mhp1nhq1phr5regs'hs4scr'ht3scshu3ss'hv1yp%0p&0p&1p;1p;2p;3p;5p;7p;4p;6p;Dp;=p;8p;<p;Bg0081j1qTg00\Ej2mTg007Qj1XTg00\ek30MTg00R=j14Tg00PFj1WTg00]`k51QTg00^]k71NTg00_Wj4`k30Lk20rTg004gj3:Tg00`7j1RTg00`mj1ETg00adk210Tg00b[j1cTg00cSk30|Tg00dHk30zTg00STk10CTg00A3j1vTg00e?k507Tg00Pek10NTg000Lj11Tg0011j1BTg00f2k30nTg00fjk40fTg00gkk70bTg00hnk40`Tg00ijj3lTg00jik61PTg00klk40^Tg00lkmD1OTg002ck10?Tg003Ak10\Tg00m`k21FTg00nLj2gTg00oLj3PTg010MR0k20WTg010gk51<Tg002HR1j20Tg00Nlj6@Tg004Aj29k10qTg011ck317Tg012ck215Tg013Dm=14Tg00OHR2k412Tg005[j2|Tg00Q]k20~Tg0000R3j22Tg00Rbk40}Tg001lj28Tg00T6k10OTg001Ok20yTg014;k10xTg005Aj2FTg0152k20wTg015fk20BTg016`k20vTg017=j3Hj2^k10sTg017]k30ATg00U`k203Tg003dR4j23Tg018Qk80uTg019Mk10tTg00VBk20pTg006Ek20oTg006mk30mTg00W3k20lTg008ok10kTg009Mk10iTg00WQk20hTg00:8k20KTg00:[j4hTg00<Mk20eTg00<ok20dTg00=[k30cTg00>:k40aTg019kj8ZTg00;Fk30_Tg00>lk20>Tg00?aj6oTg00Akj2rTg00NPk40]Tg01:Hk11MTg01;:k31LTg01;QS00j2dTg008Qk11ETg01;kj3{Tg01<gk21CTg01=_k71BTg01>\R5j2tTg01?6j4STg01?am<0<Tg01@XR6k108Tg00EKk202Tg00C\j2zTg01A8k10YTg01B8k61@Tg01B\k11>Tg01C=k11=Tg01C[k41;Tg01D>j6yTg01Dgk81:Tg01E^k20RTg01F^k30VTg00TXk20UTg01GFk218Tg01HAj4wTg01H\k40QTg01I6k50JTg01Ihk30PTg00XXk40ZTg01J\k316Tg00FCj7jTg00;ij7pTg00X4k81DTg01K?k313Tg00Bdk11GTg00DTk11HTg01K\k31ITg01L9m<0ITg01L^m<1JTg01MCmB11Tg01Mik31KTf0R7#1#1#4#1p=a%47#4p=<%47#1p=Q%17#4p=M%17#Bp>0@%W7#Wp>0j%W7#W#W#Wp=T%47#4#4#4p>0F%17#1#1#Bp=\g00L]R8g00M=R97:7p>0D%17#1#1#1p=>f3R:f2R;f1R<00373:p=s%17#1#1#4p=]%17#1p>0Hf5R=f4R>19:;P<P7I0Jp>1Ag00YIR?f6R@P=P>19:;P<P7I0J40Pp=U10<7,0;p=k%E79P;<p=[P>P:P;P<P7I0J:0P?=p>0;%17#4#1#1p=x%47#1#1#1p=N%47#4#4#4#4#4#4#4p>0620U<7-03;p=?P?P:P;P<H0Z=:>7p=5%B7,9<p=V12<7,0;p>0{g00IDRA/2</07p>0512A7p=6P:g00HfRB19;<P7C`p=AP;PBP<P7C`p>04AH;<79H>:p=_B16B<7p=GP<g00FgRCg00GFRDPDg00GfREP7g00HFRFFjp>0g1FB7p=J20KB7p=CP;PCPDPDPEPBP<g00KORGP7ChPFFjp=;P>PCPDPDPEP:PCPDPDPEPBP;PGP<ChPFFjP7Fpp=DP;PCPDPDPEPBP<g00L6RHP7ChPFFjp=~P:PCPDPDPEP;P<P7L1Dp=fPBP>P:P;P<P7Eop=nPBPAP:P;P<P7Eop=}g01NORI@13B7p=K&1G<,z;,|:&1H7'3p==B1IIB7p=IPIPBP<P7C`p>0=g00M]RJ?:<7p=7g01OHS01,d7p=i12A@18=>12A:13;</27'0'0'0p=LPBP<PHP7Chp>00P:PCPDPDPEP;PCPDPDPEP<PFFjP7Fpp>0113;</27,0:,0>,0=p=OP>PCPDPDPEP:P;PCPDPDPEP<P7FpFpp>0[g01OeS02PBP5P6P3g01PDP=P>P:P;P<P7N<0Ip=u13;</27p>0XP;PCPDPDPEP<P7Fpp>1?Q02PBPBPBP6P6P=P>P:P;P<P7N<1Jp>0GPBPBP3P=P3P>PAPAP:P;P<P7N<0Ip>0EPBPBPBPBPBPBP4P7P<P;P4P:P>P=P@f7R4f8R6f9S03NB11p>09PBPBP3P4P3P@P=P>P:P;P<P7N<0Ip>0:P4P@P=P>p-0S04/F<:1K:;P7Eyp=YPBP<PGP7Chp>0TP:PCPDPDPEP;P<PCPDPDPEP7PFFjFpp>0S13;</27,0:p=e12A:18;</07'0p=bP?P;P<P7H0Zp>19%q8S05g01PfRFg01QcRG#qR3g01R_R5g01SZ#qRHQ051mF3RK/m5P?g01TTRLP9g01UPRMg01VMRN#XRO%X8RP60M=g00IbRQ#4#a#<#Q#M#a#Q$0@RRg01WERSg01XC#Xg01Y=RTg00ZhRU#WRV#WRW$0jRX#TRY#T#T#T#T#T#T#T#TRZI1Q%XGR[K1NPKP5PFP3P>P:C`P;C`3:%R=%4Q#a#<#M$0F#M#\RF5:Bg01Z;S06%E@+10$0D%c4g01[:60|S$0D1mH3R5Q05'm%E6@0zTPP5Q05PHP3P=P[C`P>C`3:&0CNR3P?P@%vARH%<Q#Q#>#a#a#\R5PYI07PNg01\8S07&0NVRK%1QR\#BR]#v40nS08CsP3P?P4PH%<Q#Q#>#]#<#M#\R^PXI07PN%4\R_#BR`#vS09CsP3P?P6PKPAPVI07PN%4QRa#1#\Rb#vS0:CsP3P?Q03PK%BQR3PVI07PN&0@_RN#vS0;CsP?p,3memRcp,1ERdf<S0<H0fp,4regsRep,2spRfp,1wRgp,3canRhp,2R1p,2R2p,3R11K0bPePfPgPhH0`Ri?lSePePcPfPgPhp,2PHRjJ1PP?PiPcPTH0^p,2fxRiP?PLPMfARM@0MOPPRPSPTPZf@S0=f?f>RZPdPcp,3romROPef;S0>P<P7P;ND1O&0?_%1\R\#1R_#1RL$0HRk$0?Rl$0\Rm+1FRn%cM=ld7%EMRo,gdPiPePlPRPcPOJ1ARRPiP7Pl%RMAPdcoPOFU3kXDn+0WP0PnfBR0#c=ld7%E0Ro,gdPRPiP7Pl%R0APdcoPOFU3kXDnPePcPOPfPgI1<RoP7fDR0#c=ld7%E0Rp,gdPRPiP7Pl%R0APdcpPOFU3kP1fERp#c=ld<%EpR0,gdPRPiP<Pl%RpAPdc0POFU'0PoP7fGS0?#c=ld:fHS0@#ER0,gdPRPiP>PlQ0@#RAPdc0POFU'0P1fIR1#ER0,gdPRPiP=Pl%R1APdc0POFUPoP7fKR0#E,gdPRPiP6PlfLR1#RA[dc1POFUPBfMR1#RPRPif:S0APlP7fN#ERq9PdcRrPOFUX5BP7PFQ0?E@PRPiQ0319lFRFA[dc1POJ0;P?PdPcPqPTPPP0P[fJPpP;PZB17?cd-15GN=14P?PdPrP0H0^PjPcPfPgPhH12P2PcPfPgPhPoP71|lfRo%BLR2+0~Rj=:BA%1Q#x#N#N#x#\S0B/2o%4aRa#4$0F$06$06$06R0#4#<$0F$06#BS0C,2oP?PcPfg00[GH0}%>kRr#1$0H#\/27%Ma#<#Q#>#>#\,87'0&0?_Ra$0\RG$0CRZPc19l<S0DO1&0OG3:[^lB%qGRp$0CR[Pc19l^S0EPX19l`9?pXR`D5P[Pc%4Q#<#>#]#>#N,VlPY&0HQ#N#<#x#>#N,Vl9?pYD5P[Pc19l5RPPY19lgRT9?pYD5%1Q#M#]#Q#>#]#\Rq/2gS0F%1Q#M#]#Q#N#>#<$0@R180{gP[Pc%4Q#<#>#]#x#N,VlPY1Vlr9?pYD5P[Pc%4Q#<#>#]#M#<#x,VlPX1Vl09?pXR0D5P[Pc%4Q#<#>#]#M#<#N,VlPXP0D5P[Pc%aQ#a#M#Q#N#N,VlPY19lh9?pYD5%BkRk-0y]R0,8h-05h&0xf%6oRf18o0'01FBAS0G19lA,|lRh=:BA1FmT20wdVS0H=:mTPnPZ\mRZPRPiP<PFP7POJ0;20Be<1mmBRrPmPl%QL#>RL#BRs-0voPsCARtQ0E%B\R\604mRu%B_R_:04mPRvB04mT]Rw%XrRx5HrRy5HrRz5HrR{3HR|:0Ac7P[P7PTPW19abS0I19aNS0J%XG5HGS0K5HG-03pRGD5P[P7PPPY13g],9lS0L9?pYS0MD5P[P7Q0EPXP`D5'03kRa3kXFZ+0WXrnf[RNPZPRPif\RbPFP7POJ0;20Beb;kaXFZfoRZ9[dcRaPRPiPNPFPaPOJ0;20BeNROB0Aca|RFP[PaPTPWPGD5S0NP[PaPPPYQ0MD5S0OP[PaQ0EPXP`D5S0P'0S0Q'0R`'0RG'0fQS0RPOPGPdPS%cZPePNfgf`fWL0uPFP`PmPT%qrR`PrPmPl&0tLRL,3oPsCARFPrPmPl13h^P\CAPrPmPl13h5P_CAPrPmPl1|l7S0S/3ARNP]CAPxD_D_;:|X:mPrPFPrPmPl137^S0TP\CAPrPmPl1375S0UP_CAPrPmPl1|lTRe/3AP]CAPxD_D_=:`|X5BPgPrPFPrPmPl13A^RZP\CARSPrPmPl13A5RGP_CAROPrPmPl137ARWP]CAPxD_D_=:`|X5BP`P`1^rF1^rtRt13gARF,9lS0V>04m]Ri=HrxRR9HrORb9HrSP{P`\`R{/FtP`P`1^rS1^ruRuPbPz1F{uP`P`1^rO1^rvRvPRPy1F{vP`P`1^ri1^rwPxPxPrP{&0srRvPvPiPwP{\r/FvPBPrQ0V:0LmBB0LmBTP]P]PmPr\BRv20rmBR{P{Q0VPTPv\m/F{PBPm&0qlR{P{PFPgPm\B/F{20po2R{%62%6j[\fRf20o]kRj18A]%6k18A0[[R2%6]S0Wg00JGRvB0m]k<UWBRkQ0W%60\v]BRvg00JcRw#XRi%qwRw20lB<Ry&0kBRR&0iBROPB20hBQRQ20KBARu'GRzg01\dPQCh+0g20eOERbP7P;1F8920d7;$0DdB0cBA<H0aR9b1b2b3X4BA:BW7^4BP7PgO1b0b7b8b9GZGZ%J]GZGZ1F`xGZGZGZGZPeP{PfPjP2PkPvPiPwPyPRPOPOPO%CqPQ%C19;OQS0XDDS0Y&0ODRxPOPOPuPQ%C]S0Z>0_BlR89~OQDDCfPbP9b1b2b3X4BS0[12q71271S0\'0R118<0-05<[^4BS0]P7PgQ0<O2b0b7b8b9-0>gDnPhP<C}Q0HP7EoPJPrPmPlPlPd%K7RqPqC=S0^%I7S0_CAX?J1mIBS0`&0NU/rL00=sRUQ0`1rH^RI00=\RqQ0`1rH5RS00=_RtQ0`1rKAR}00=]R~Q0`#XD_D_H0]=:`|ePJPr&1MdQ06H0]S0`=:`|RrePrP`Q0`fq9[dcS0`>0Ac7Xn`PdPcQ06fp#ES0afiQ06:1LJ7Q0017U<17q<17t<17~<#i'd'dPlPd%K;R`P`C=R`P`P0%I;RrP`PrP0FLP717U;PJPUQ0^Q0^P0Q0_Q0^Q0_P0FLX?JS0_P{PfPjP2PkPvPiPwPyPRPOQ0C#C9;OQPxPOQ0B#C=;OQPxPOPOPu%CL,GQRrPOPO200r8POPOPu%CsR`1Gr`=;O8DDH01DDCfCfPbP9b1b2b3X4BQ0C,27Q0B/2<13;LRLPLP0PsPLPsP0FL[[^4BP7PoQ0?Q0@O3b0b7b8b9PlPd%KURoPoC=RoPoP0%IURUPoPUP0FLeP:P7E@W6P7O117q;17t;17~;#i'd'dQ0017q:17t:17~:#i'dPlPd%K>RUPUC=RUPUP0%I>RoPUPoP0FLP717q>PJPqQ0_Q0T#6S0@Q0T/80S0B%6\S0CQ0TP\P0EOX5BPjP2PkPvPiPw&1EBRoPRPOPOPu%C^S0^,GuRUPOPO200U8POPOPu%C\Rs1GUs=;O8DDH01DDPbP9b1b2b3%6ZRU18Z0RLQ0C13Z\S0b/20S0c'0S0d'0S0e'0S0fP7b0b<b=S0gPhP6C}PlPd%KqR`P`C=R`P`P0%IqRqP`PqP0FLeP=P7E@W6P7O117t>17~>#i'dQ0017t=17~=#iPlPd%K@RqPqC=RqPqP0%I@R`PqP`P0FLP717t@PJPtQ0_Q0U#6S0hQ0U/80S0i%6_S0jQ0UP_P0EOX5BPjP2PkPvPiPwPoPRPOPOPu%C5S0k,GuR`POPO200`8POPOPu%C_Rq1G`q=;O8DDH01DDPbP9b1b2b3%6GR`18G0RrQ0j13G_S0l/20S0m'0S0n'0S0o'0S0pP7b0b<b=S0qPhQ0AC}PlPd%KtS0rQ0rC=S0rQ0rP0%ItRtQ0rPtP0FLeP4P7E@W6P7O117~@#iQ0017~4Q01PlPd%K6RtPtC=RtPtP0%I6S00PtQ00P0FLP717~6PJP~Q0_PmPT%6NS0_18N0S00Q0WPNP]P0EOX:mPg%6WS0r18W0S0sQ0WPWP]P0EOX5BP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOA;OuzS0tPOA~Oz8S0uPOPOPuQ0ZQ0Z,Gz=;O8DDI0[CfPbP9b1b2b3X4B13<AS0v#6S0wQ0v/80S0xQ0WQ0vP]P0EO\1^4BP7PgQ0?O2Rtb0b7b8b9PeP{PfPjP2PkPvQ0[Q0]Ptb0b7b8b9-0>gDnQ0HQ0>EoPlPd%K~RtPtC=RtPtP0%I~R~PtP~P0FLeQ03P7E@W6P7O1Q01Q01PlPdQ0A#KR~P~C=R~P~P0Q0A#IRtP~PtP0FLP7n010000000W6P7O1n200100000021100010000W6P7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000%K<%I<5{deWOX?JQ06-1CdefTK1BP|P7E@b6Q0NQ0QP?PdPaflS0QPKPAPVQ0:fPS0NfcS061tVV1233R|PVP3%J3S01PVP3Q01EuPiPwPoPR%C3RJ=;OJPbP9b1b2b3P|P7b0CSS0?1tVY123_R|PVP3Q01PYP_%J_S0WEuPiPwPoPRA;OJqPbP9b1b2b3P|P7b0CSS0yN<0<&08VR|9{d}RtP[Q0a9PdcS0a202d}S0zPVQ0:,zd9?pVR~D5[P?PdQ0afmPKP3PVQ0;Q0RQ06Q0?Q0yN<0<1rK3S0?={d|RKP[Q0`Q0?-02dS06PVQ0;,zd9?pVS0;D5[PmQ0zP[fs9[dcS0zP<PVP~D5\tX:mP<Q0V&0YAE@P[fr9[dcS0RQ0VPVP~D5\tPmQ06P[ft9[dcS06P<PVQ0;D5\KX:mP<13g3RA,9lS0V&0Y3E@P[Q0zQ0VPVQ0;D5\KP?Q0zPTQ0IQ0JPgB0X7]0X5BP{PfPjP2PkPvQ04PiPwPyPRPOPOPCPDPDPEP:J1@Q0X61?OPxQ0Z,GQ=;O8CfPbP9b1b2b3X4BWEQ04Q0\,0<B0X<]0[^4B]EP7Q0FPgQ0=O3b0b7b8b9PeP{PfPjP2PkPvQ0[Q0]P7PgQ0=O2S0=b0b7b8b9-0>gREDnPBPFP[fu9[dcQ0DPVP~D5\tX5BP<Pg&1>gE@P[Q06PTPVP~D5\tP7PmPTQ0_Q00%6|R~PNP|P0EOX:mPgQ0rQ0sP~PWP|P0EOX5B%6FRW18F0RN13F|S0s/20S0r,0~S00'0S0_'0%63Rc13F3S0D/20S0F'0RD,0NRC,0WPWQ0_PWPCPWPWPWPNQ00PNPDPNPNPNP~Q0rPcQ0FP7X@BRN12<7$1=XvBX@BRDQ0GP|P3PNPNQ02&087#JW@S02PVP3Q01J0GRWJ0ES0FPNPDQ0sQ0DPNPNPNPBPBg01]K13<7H1;#JXoBXpBRCPFPF%JFP|P3PWN:09P0P0%J0RFL0:EyGYGYP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOQ0tPOQ0uPOA;OuJS0uPO1GzJ00T8H0SI0[CfPbP9b1b2b3X4BQ0wQ0xPcQ0vP3P0EO\1^4BP7PgPMO2RMb0b7b8b9CSPeP{PfPjP2PkPvQ0[Q0]PMb0b7b8b9-0>gDnQ0HP=EoPlPdP}P}C=R}P}P0P~P}P|P0CeCbePteO1b>PgP[Q061373Rt,9lPVQ0K-03pD5X5BP7PmPTQ0S/33R}P}P0P~P}P|P0CeCbX:mPgPtPtP0P~PtP|P0CeCbX5B%6ARt18A0R}13A|S0S/20S0K,0~S0]'0S0['013A3S0v/20S0x,0cRM,0}Rz,0tPtQ0[PtPzPtPtPtP}Q0]P}PMP}P}P}P~Q0KPcQ0xQ0FPNPDQ0SQ0vPNPNPNPCPAPA%JAP|P3PWN:09P0P0PFL0:EyGYGYP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOPOPu1GQJRQPOPO200Q8POQ0uPO1GQJ00T8H0SH01DDCfPbP9b1b2b3X4B13<3RQPQP0PcPQP3P0CeCb\1^4BQ0=b0b7b8b9CSPePEDnQ0HP>EoPlPdQ0?Q0?C=R1P1P0P~P1P|P0CeCbePKeO1PePEDnL1:bAb>bAb>Q0OQ0PP?PdPaQ0QPHP5PYQ08Q0NfeQ0y1tYY12__REPYP_Q0WPYP_Q0WEuPiPwPoPRA;OqqPbP9b1b2b3PEP7b0CSN<0<&08YRE9{dSReP[Q0a202dSRKPYQ08,zd9?pYR|D5[PmPKP[Q0RP<PYP|D5\eX:mP7PPPjP2PkPvPiPwPoPRPOPOPuQ0kQ0k=~O8DDPbP9b1b2b31850-055P7b0b<b=-0R5E@P[Q0`PPPYP|D5\ePmQ0HP[Q0z@19PYR|PpQ0719l]R580V<-0UYCs\eX:mP7PTP;E@P[Q0RPPPYQ07@0VT5R59?pYD5\ePmP5P[Q06PPPYA?pY<D5\eX:mP7Q0L218g]E@Q0M9:[|\eP7Q0hQ0i%6ER|Q0UPEP0EOX5B13GERg/20R],0|RP,0rR5,0`Q0pP`P5P`Q0oP`P`P`PrPPPrQ0nPrPrPrP|P]Q0jQ0mPNPDQ0GPEP_PNPNQ02PYP_Q0WJ0GR]J0EPNPDPgQ0lPNPNPNPCPGPG%JGPEP_P]N:09P0P0PFL0:EyGYGYQ0qCSPhP=C}PlPdPSPSC=RSPSP0P|PSPEP0CeCbePeeO1b;b;b;b;P?PdPaQ0QPHP^PXQ09Q0Nfd1tVX123\RHPVP3Q01PXP\%J\R3EuPiPwPoPRA;OJsPbP9b1b2b3PHP7b0CS1tXY12\_RHPXP\P3PYP_Q0WEuPiPwPoPRA;OsqPbP9b1b2b3PHP7b0CSN<0<&08XRH9{dIRqP[Q0a202dIRsPXQ09,zd9?pXRpD5[PmPsP[Q0RP<PXPpD5\qX:mP7Q0EPjP2PkPvPiPwPoPRPOPOPuQ0^Q0^=~O8DDPbP9b1b2b318^0-05^P7b0b<b=-0R^E@P[Q0`Q0EPXPpD5\qP7Q0@Q0B%6HRpQ0TPHP0EOX5B13ZHRB/20R[,0pR^,0LR9,0UQ0fPUP9PUQ0ePUPUPUPLP^PLQ0dPLPLPLPpP[Q0CQ0cPNPDQ0GPHP\PNPNQ02PXP\P3J0GR3J0EPNPDPBQ0bPNPNPNPCPZPZ%JZPHP\P3N:09P0P0PFL0:EyGYGYQ0gCSPhP:C}PlPdPIPIC=RIPIP0PpPIPHP0CeCbePqeO1b;b;CwCwCwCwCwH0QH0QbTbhbSW[WZW^W_WYWdWfWeW\W]WcWaWbW`f=Q0<Q0>Q0AQ03P6P4P@P=P>P:P;P<P7O>n4000010000001>110810:10910;10510410=10>10<101107106102103bqbHbCWCWMP<P7O2n2001000000121000000W6WJP<P7O2n2001000000121000000W6XgnP<P7O2n2001000000121100000bjbGbIWRWXWWWVWUWKWQWLWNWPWkWmWsWtWuWio"). Qed.
End Package.

End FXALL1.
Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].
Section FXALL2.
Context {fx : FPState}.

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x65c94 pf_sr [] pf_kn 40) [].

Definition dirsA : list bool := [true; false; false; true; false].
Definition dirsB : list bool := [false; true; true; true; true].

Definition dirsC : list bool := [false; true; true; true; false].
Definition dirsD : list bool := [false; true; true; false; false].

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

End FXALL2.
Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.
Section FXALL3.
Context {fx : FPState}.

Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x65be8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA.
Qed.

Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x65be8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB.
Qed.

Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x65be8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC.
Qed.

Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x65be8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD.
Qed.

Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x65be8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x65c94) mem rom) (mkst regs' (Z_to_bv 64 0x65be8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xf00e8, 4);
                          (Z_to_bv 64 0xf0110, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xf0110) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xf00e8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
ltac2:(KReplay.run1 (kr_t_U1PrintfBuf ()) ["FXALL3"] "h04mem'h15regs'h21Hh32H0h42H1h52H2h62H3h72PHh82R1h93R11h:2R2h;3canh<3memh=1oh>4regsh?3romh@2sphA1wp;1p;2p;4p;3p;5p;;g000Lj12Tg00R=j16Tg002cj1OTg003Aj1UTg00m`j2ZTg00STj1STg00OHj4XTg0011j11Tg01]oj3KTg01^Rj2HTg004Aj20Tg004gj33Tg028`j1YTg00Q]j2=Tg01;QR0j2RTg01I6j5@Tg01Ihj3NTg015fj2MTg00\Ej2WTg005[j2LTg016`j2JTg007Qj1QTg017]j3ITg0081j1VTg00PFj1:Tg00XXj4CTg00U`j2DTg003dj2GTg00TXj2FTg002Hj2ETg010Mj2>Tg029\l;_Tg02:Yl;^Tg02;Vl;]Tg02<Sl;\Tg00_Wj4[Tg017=j3TTf0R1#2#2p=;%61#2p=5%21#6p=9%61#6p=Ag00HfR2g00IDR3731p=Pf1R4=321p=4f2R5=324/R1p=8%21#2#2#2p=?P5P2P4P1C[p=7f4R6f3R7AT5413Tp=<1E41,E5p=Bg00IbR8#2R9#6R:#OR;%29R<#2R=#2R>#;#OR?#UR@'ZRA%O=RB#URC#S\@RDP6P5P4P1CXf6R5%18REg01kDRF5K;'H%58#9#9#5#A#A#5#5#;#1,0?RG53@f7RH%19R9=K;F'H=3@6f8RI%6:#1=K;F'H10?353@f5R3#Y%1<R<,=3RF#P%68R;#1RJ,4F98F998FE'RP01=5<RF#P14FJ98F998FEg00YIRFp,2fxRKf=RL%58#9#9#A#;#5#9#9#;#1,0?RMf<RNf;ROD@PKP4PGP1POD@3N1ML41W@2RPf:RQ,L?%5>#?#1R>'J,0?=7@>PP%68#A#?#?#A#5#5#;#1,0?RR=7@<RSPP%68#A#;#?#9#;#9#?#1,0?R8%1=57@R=PPf9RT,0?RU=7@9%QPRVD<D<9IN1%VCRW#SRXPFP1PUg00Zh#:#:RUCCPC%?;#1,0BPC%2:#1,0B%QCD<,DWRC33PFP1P8%:U#:R8#:#:#:#:RBCCR;1GT9,0?,FB,DW53XPFP1PRP8CC%1:,0?,F8,DW53XR8'E3B3BX0D,>DX1A,>AP11=H<R:#PPNPOPQPTPIPHP5P1P3P6P7M;_W3P1O114:J98:998:EP01=I<R:/4E14:J98:9PKf?R:PMf>R7PLD@PKP4PGP1PLD@5NF1M:4PP1L?N/J>,0?=7@>PPPSPPP=PP10?OR6=7@9PVD<D<9I71PFP1P6PUCC=3XC1GO9,0?,FB,DW93X;/E83B3BX0D,>DX1A,>AP11=T<R6/4EP7PLPNPOPQPTPIP1PHP5P3M;^W4P1O1146J9869P01=Q<R0/49140JPKfAR0PMf@RMP:D@PKP4PGP1P:D@5NF1M04PP1L?7/J>,0?=7@>PPPSPPP=PP10?LRP=7@9PVD<D<9IM1PFP1PPPUCC=3XC1GL9,0?,FB,DW93X;/E83B3BX0D,>DX1A,>AP11=O<R</49PMP:P7PLPNPOPQP1PTPIPHM;]W5P1O114<JPMP:P7PLPNPOPQP1PTPIPHM;\W6P1O1n200100001021000010000W2P1O1n200100001021000011000W2P1O1n200100001021000011000b=W9W:W8W7X;2XA2X@@X?DW<W>o"). Qed.

End FXALL3.

