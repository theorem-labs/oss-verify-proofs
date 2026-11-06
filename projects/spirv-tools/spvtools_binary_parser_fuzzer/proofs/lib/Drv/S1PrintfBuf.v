(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive RefMemcpyLib AgentLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SymAux RefPrintfLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1PrintfBufBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1PrintfBuf () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC49OSSVerify5KrLib8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C49OSSVerify5KrLib6SymAux7sregionC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indI59OSSVerify5KrLib3Drv?S1PrintfBufBase3pfH00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C49OSSVerify5KrLib6SymRun6stk_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Drv?S1PrintfBufBase5PF_FRC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K59OSSVerify5KrLib8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux;log_coveredC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux9same_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8SymDrive5kreadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PrintfBufBase:pf_regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PrintfBufBase3pfEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PrintfBufBase:pf_know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymRun9run_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib3Drv;S1PrintfBuf7pf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C49OSSVerify5KrLib6SymRun;carry_afterC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX22evC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C49OSSVerify5KrLib5Frame9frame_modC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux@keeps_cs_of_sameC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib6SymAux6rdenotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAux<regions_flatC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymAuxAlog_covered_frameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib3Drv;S1PrintfBuf;adenot_var1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib<RefPrintfLib5rdn_2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf;adenot_lit0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses6eq_iffI59OSSVerify5KrLib8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf7pf_fuelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf8pf_stopsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PrintfBufBase5pf_srC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PrintfBufBase5pf_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf:pf_regionsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC49OSSVerify5KrLib<RefPrintfLib:mod4_shiftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefPrintfLib7bt_and3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib<RefPrintfLib9bt_and3_0C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib3Drv;S1PrintfBuf7pf_caseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3Drv;S1PrintfBuf5dirsAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4resAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4carAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib3Drv;S1PrintfBuf5dirsBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4resBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4carBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf5dirsCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4resCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4carCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf5dirsDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4resDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf4carDC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefPrintfLib:mod4_casesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf8pf_caseAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf8pf_caseCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf8pf_caseBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1PrintfBuf8pf_caseDC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL1.
Context {fx : FPState}.

Definition pf_stops : list Z := [0x65994].
Definition pf_fuel : nat := 3000.

Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0xee390, 4); (SA (ELit 0) 0xee3b8, 8); (SA (EVar 1) 0, 2)].

Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x65a40) mem rom) (mkst regs' (Z_to_bv 64 0x65994) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xee390, 4);
                          (Z_to_bv 64 0xee3b8, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xee3b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xee390) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x65994.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_S1PrintfBuf ()) ["FXALL1"; "Package"] "h02Hah12Hkh27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81kh91zp;2p;1p;3p;4p;7p;6g0000j21Tg000Lj10Tg0011j18Tg001Oj2?Tg001lj24Tg002Hj29Tg002cj1ITg003Aj1CTg003dj2ATg004Aj23Tg004gj32Tg005Aj2;Tg005[j2<Tg006Ej2VTg006mj3UTg007Qj1TTg0081j1OTg008Qj1NTg008oj1LTg009Mj1HTg00:8j25Tg00:[j4:Tg00;Fj3BTg00;ij7DTg00<Mj2ETg00<oj2FTg00=[j3GTg00>:j4@Tg00>lj2JTg00?aj6KTg00@?j27Tg00A3j1>Tg00Akj2MTg00Bdj1=Tg00C\j2PTg00DTj1QTg00EKj2RTg00FCj7STf1R0g00FgR1g00GFR2P2g00GfR3f0R4g00HFFSp=6g00HfR5g00IDR6/14g00Ib#0R7#8R8%07#0#0#0#0R7#8R9'?R:,44'9P5P6%I7R7#CR;f2R<,A4,37137<32X951370R=,;;1376R>,<71V8914681169146:R?[[1168R@g00JGRAAU890UW0116:\A^0@g00JcR@#T%O@%N5%L5%H5R@P1P2P2P3P51556R2g00KOP2C:,6@P5P2g00L61558=B57C:,6@FD1E@3P4P<g00L]R@g00M=R3';1F4<=2@3dAG560C@b3b6b71166/9?P4b2b4b5,J6EK17>0=2;=ep,1ER>%>6/M0R0#='P%Q0'7=2;=e1R>0=2;=eW1W8o"). Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
Proof.
ltac2:(KReplay.run1 (kr_t_S1PrintfBuf ()) ["FXALL1"; "Package"] "p'0h02Hah14__x1h24Pbszi004Pbszh34Pcani014Pcanh46Pcan64i026Pcan64h56Pflagsi036Pflagsh64Pimgi044Pimgh74Plbfi054Plbfh85Plocki065Plockh95Psp16i075Psp16h:5PspHii085PspHih;5PspLoi095PspLoh<4Pstki0:4Pstkh=2Pwi0;2Pwh>5Pwendi0<5Pwendh?5Pwposi0=5Pwposh@7__arithhA4__ffhB7__sat65hC7__sat66hD7__sat67hE8__varmaphF5__withG1ihH1khI1phJ1zp;4p;1p;2p;3p;8p;6p;7p100M]p4p70R0p100NPp4p710p8P0p100Nlp4p710p8g00OHR0j4vTg000Lj11Tg002cj1QTg003Aj1[Tg00PFj17Tg00Pej1dTg00Akj2YTg00EKj2UTg003dj2HTg004Aj25Tg004gj32Tg005[j2PTg0011j1>Tg00Q]j2tTg0000j2:Tg00R=j10Tg00Rbj4\Tg001lj2ETg002Hj2FTg00STj1TTg00T6j1STg0081j1RTg00TXj2ATg00U`j2BTg001Oj2uTg005Aj2ZTg00VBj2sTg006Ej2rTg006mj3qTg007Qj1pTg00W3j2oTg008oj1nTg009Mj1jTg00:8j2KTg00WQj2iTg00;Fj3fTg00:[j4VTg00X4j8eTg00<Mj2cTg00<oj2gTg00=[j3hTg00>:j4bTg00>lj2kTg00?aj6lTg00@?j2XTg00Bdj1aTg00C\j2mTg00DTj1`Tg00XXj4_Tg00FCj7^Tg00;ij7]Tf0R1#1#1p=?%11#0#1#1p=@%01#1#1#1p=8%11#0p=3%11#1#1#1p=4%11#>p=G%01#0p==%01#0#0#0p=O%01#0#0#0#0#0#0#0p=I%01#1#0#0p=C%01#0#0#1p=Df1R2%11#1#>'5p=6g00YIR3f2R4P2P1C_p=;%>1,52p=L%01#1p=<%11#1#0#1p=Ng00IDR5/:1p=9g00HfR6P2g00KOP1CVp=MP2g00FgR7g00GFR8P8g00GfR9P1g00HFF^p=JP4P7P8P8P9P2P1F]p=Wp,2PHp,3memR:p,2spR;p,1wR<p,3canR=CvP0P:P;P<P=g00IbR0#1R>#?R?#1R@#?RA#QRB#[RCp,1ERDg00[>#7RE#dRF/Y4'U1H<4,5B32P11PB;RG%>@R@'tRH=265%10#@#@#8#3#4#G/:G%=0RI#0#O#I#I#IRJ#0#=#O#I#>,:GP3P:P;g00[]C\%4AR;#1#4#G/:1%3I#=#4#4#4#G,E1'F%Q?#[R?#TP:15B2O1%S?32[^G6%R?R?#TRI%00#C#8#D#@,6B%7E#7#7RE5;:%0>,LB,AE,B?32%00#C#8#=#C#?,6B%7E#7#7#7R35;:%?0#8#3#3#<#<#<#<,6B,A3,B?52I%00#C#8#D#D,6B=;:315B<RK,A3,B?52I%10#@#N#3#3#3#@#GRL/:<%10#3#4#C#3#@#=#GRM,:<'F%00#C#8#=#O#?,6B=;:31LB;,A3,B?52I%00#<#D#3#4#3#=,6B=;:E1LBJ,AE,B?RJ52I%00#<#D#3#4#8,6B=;:E=2IJ%?0#8#N#3#N#<,6B=;:315B=,A3,B?52I%9=%>>R>%>ARA'uRI,E='FP6P<fNR=,H1,5B1H<=,5B52CXJ6fMR=,H<,5BR?,ZC1PBK1sG@%9G%9@%9H[[1r>A1E5>%9A1E5I[[%9>RHg00JGR@Aq>A2UW0%9I\@^0Hg00JcRH#p%RH1o62%n6%j6RHP7P8P8P91K6L1i60R0'M,JH1K6M,M0,JH5WH%S81K65/M0,JHP6P0g00L61K6>=f6BCV,JH5WHGe1cH9P1P4g00L]RHg00M=R9'Z1g14=2H9dAh652CbbAbEbFX161:L11:1M'F%921E2I'F[^16P1P<f9RIO2b@bBbCbD,k<El1XK==2C?e1YF=R=#a,mD%`='X=2C?e1UD==2C?eW4W3W7W8W2W=W?W>W5W6W<W:W;W9f=f<f;f:PIf8f7f6f5f4f3P4P2P1O>n4000010000001>110710910810:10410310<10=10;100106105101102bIXH6o"). Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x65a40 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x65994 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0xee3b8 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0xee390 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
Proof.
ltac2:(KReplay.run1 (kr_t_S1PrintfBuf ()) ["FXALL1"; "Package"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Hh77__sat65h87__sat66h97__sat67h:1bh;1Bh<6__sat0h=6__sat1h>2B0h?1rh@1xi001xhA2B1hB2HahC3HmshD1RhE4__p1hF4mem'hG2HKhH3HK'hI2HRhJ3HR'hK6HcarryhL4HcovhM3HlfhN3HpchO2HrhP4HrunhQ5HsamehR3HschS3HsphT3Hw1hU2K1hV2K2hW2K3hX2K4hY4Pbszi014PbszhZ4Pcani024Pcanh[6Pcan64i036Pcan64h\6Pflagsi046Pflagsh]4Pimgi054Pimgh^4Plbfi064Plbfh_5Plocki075Plockh`5Psp16i085Psp16ha5PspHii095PspHihb5PspLoi0:5PspLohc4Pstki0;4Pstkhd2Pwi0<2Pwhe5Pwendi0=5Pwendhf5Pwposi0>5Pwposhg2R'hh2Z0hi4dirshj1ehk3hs'hl1ihm3kn'hn1lho1mhp1nhq1phr5regs'hs4scr'ht3scshu3ss'hv1yp%0p&0p&1p;1p;2p;3p;5p;7p;4p;6p;Dp;=p;8p;<p;Bg0081j1rTg00\[j2mTg007Qj1VTg00];k30NTg00R=j11Tg00PFj1[Tg00^6k51RTg00_3k71OTg00_mj4dk30Pk20rTg004gj3:Tg00`Mj1PTg00aCj1BTg00b:k20}Tg00c1j1`Tg00cik30yTg00d^k30vTg00STk10BTg00A3j1{Tg00eUk504Tg00Pek10MTg000Lj12Tg0011j1FTg00fHk30hTg00g@k40bTg00hAk70aTg00iDk41QTg00j@j3oTg00k?k61PTg00lBk40^Tg00mAmD1JTg002ck10JTg003Ak10]Tg00n6k21CTg00nbj2^Tg00obj3OTg010cR0k20XTg011=k51:Tg002HR1j20Tg00Nlj6>Tg004Aj29k10qTg0129k316Tg0139k214Tg013Zm=12Tg00OHR2k411Tg005[j2zTg00Q]k210Tg0000R3j24Tg00Rbk40~Tg001lj28Tg00T6k10QTg001Ok20{Tg014Qk10zTg005Aj2@Tg015Hk20xTg016<k20CTg0176k20wTg017Sj3Jj2Tk10sTg0183k30ATg00U`k206Tg003dR4j23Tg018gk80uTg019ck10tTg00VBk20pTg006Ek20oTg006mk30nTg00W3k20mTg008ok10kTg009Mk10jTg00WQk20iTg00:8k20LTg00:[j4jTg00<Mk20fTg00<ok20eTg00=[k30dTg00>:k40cTg01:Aj8]Tg00;Fk30`Tg00>lk20@Tg00?aj6pTg00Akj2~Tg00NPk40_Tg01:^k11NTg01;Pk31ITg01;gS00j2fTg008Qk11DTg01<Aj3uTg01==k21BTg01>5k71ATg01?2R5j2wTg01?Lj4QTg01@7m<0=Tg01@nR6k105Tg00EKk20<Tg00C\j2yTg01ANk10[Tg01BNk61?Tg01C2k11=Tg01CSk11<Tg01D1k41;Tg01DTj6|Tg01E=k819Tg01F4k20UTg01G4k30RTg00TXk20YTg01G\k217Tg01HWj4}Tg01I2k40TTg01ILk50ITg01J>k30STg00XXk40OTg01K2k315Tg00FCj7iTg00;ij7kTg00X4k813Tg01KUk31ETg00Bdk11FTg00DTk11GTg01L2k31HTg01LOm<0KTg01M4m<1KTg01MYmB1LTg01N?k31MTf0R7#2#2p=x%17#2#1#1p=a%27#1#2#2p=b%17#2#2#2p=Y%27#2#2#Fp=U%[7#[p>0l%[7#[#[#[p=N%27#2#1#2p=g%17#1#2#2p=s%17#1p=M%17#2p=c%27#Fp>0Eg00L]R8g00M=R97:7p>0D%27#1p=;f3R:f2R;f1R<00673:p=tf5R=f4R>19:;P<P7I0Ip>1@g00YIR?f6R@P=P>19:;P<P7I0I40Sp=S10<7,0;p=l%B79O;<p=XP>P:P;P<P7I0I:0S?=p>0>%17#1#1#1p>0F%17#1#1#1#1#1#1#1p>09%27#2#2#2p=R20Y<7-06;p=?P?P:P;P<H0O=:>7p=5%F7,9<p=\14<7,0;p>0|g00IDRA/4</07p>0814A7p=6P:g00HfRB19;<P7Cdp=AP;PBP<P7Cdp>07AJ;<79J>:p=ZB15B<7p=CP<g00FgRCg00GFRDPDg00GfREP7g00HFRFFip>0g1@B7p=I20LB7p=EP;PCPDPDPEPBP<g00KORGP7CjPFFip=<P>PCPDPDPEP:PCPDPDPEPBP;PGP<CjPFFiP7Fkp=DP;PCPDPDPEPBP<g00L6RHP7CjPFFip>01P:PCPDPDPEP;P<P7L13p=hPBP>P:P;P<P7Epp=nPBPAP:P;P<P7Epp>00g01NeRI@1EB7p=K&1F<,y;,z:&1G7'3p==B1HIB7p=HPIPBP<P7Cdp>0?g00M]RJ?:<7p=7g01O^S01,f7p=q14A@18=>14A:13;</47'0'0'0p=GPBP<PHP7Cjp>02P:PCPDPDPEP;PCPDPDPEP<PFFiP7Fkp>0313;</47,0:,0>,0=p=LP>PCPDPDPEP:P;PCPDPDPEP<P7FkFkp>0\g01P;S02PBP5P6P3g01PZP=P>P:P;P<P7N<0Kp=v13;</47p>0ZP;PCPDPDPEP<P7Fkp>1>Q02PBPBPBP6P6P=P>P:P;P<P7N<1Kp>0HPBPBP3P=P3P>PAPAP:P;P<P7N<0Kp>0GPBPBPBPBPBPBP4P7P<P;P4P:P>P=P@f7R4f8R6f9S03NB1Lp>0:PBPBP3P4P3P@P=P>P:P;P<P7N<0Kp>0;P4P@P=P>p-0S04/@<:1M:;P7E|p=WPBP<PGP7Cjp>0WP:PCPDPDPEP;P<PCPDPDPEP7PFFiFkp>0V13;</47,0:p=_14A:18;</07'0p=eP?P;P<P7H0Op>18%r8S05g01Q<RFg01R9RG#rR3g01S5R5g01T0#rRHQ051mF3RK/m5P?g01TjRLP9g01UfRMg01VcRN#VRO%V8RP60N=g00IbRQ#1#x#a#b#Y#URRg01W[RSg01XY#Vg01YSRTg00[>RU#[RV#[RW$0lRX#NRY#N#N#N#N#N#N#N#NRZI1R%VGR[K1OPKP5PFP3P>P:CdP;Cd3:%P=%1Q#g#s#M#g#c$0ERF5:Bg01ZQS06%B@+0}$0D%`4g01[P60yS$0D1mH3R5Q05'm%B6@0vTPP5Q05PHP3P=P[CdP>Cd3:&0BNR3P?P@%{ARH%MQ#;#s#;#M#;#M#UR5PYI04PNg01\NS07&0MVRK%2QR\#FR]#{40hS08CtP3P?P4PH%MQ#;#s#;#M#g#UR^PXI04PN%1\R_#FR`#{S09CtP3P?P6PKPAPVI04PN%1QRa#2#URb#{S0:CtP3P?Q03PK%FQR3PVI04PN&0E_RN#{S0;CtP?p,3memRcp,1ERdf<S0<H0bp,4regsRep,2spRfp,1wRgp,3canRhp,2R1p,2R2p,3R11K0aPePfPgPhH1QRi?oSePePcPfPgPhp,2PHRjJ1PP?PiPcPTH0^p,2fxRiP?PLPMfARM@0NOPPRPSPTPZf@S0=f?f>RZPdPcp,3romROPef;S0>P<P7P;ND1J&0J_%2\R\#2R_#2RL#xRk$0JRl$0]Rm+1CRn%`M=od7%BMRo,^dPiPePlPRPcPOJ1@RRPiP7Pl%PMAOdcoPOFS3lXDn+0XP0PnfBR0#`=od7%B0Ro,^dPRPiP7Pl%P0AOdcoPOFS3lXDnPePcPOPfPgI1:RoP7fDR0#`=od7%B0Rp,^dPRPiP7Pl%P0AOdcpPOFS3lP1fERp#`=od<%BpR0,^dPRPiP<Pl%PpAOdc0POFS'0PoP7fGS0?#`=od:fHS0@#BR0,^dPRPiP>PlQ0@#PAOdc0POFS'0P1fIR1#BR0,^dPRPiP=Pl%P1AOdc0POFSPoP7fKR0#B,^dPRPiP6PlfLR1#PAXdc1POFSPBfMR1#PPRPif:S0APlP7fN#BRq9OdcRrPOFSX5BP7PFQ0?E>PRPiQ0319lFRFAXdc1POJ0>P?PdPcPqPTPPP0P[fJPpP;PZB16?cd-14GN=12P?PdPrP0H0^PjPcPfPgPhH11P2PcPfPgPhPoP71zlfRo%FLR2+10Rj=:BA%2Q#b#b#Y#b#US0B/4o%1aRa#1$0F$09$09$09R0#1#M$0F$09#FS0C,4oP?PcPfg00[]H0~%RkRr#2#x#U/47%;a#s#R#R#U,87'0&0J_Ra$0]RG$0BRZPc19l<S0DO1&0QG3:[^lB%rGRp$0BR[Pc19l^S0EPX19l`9?pXR`D5P[Pc%1Q#a#Y#M#a#R,\lPY%xQ#Y#;#;#c#c#c#Y,\l9?pYD5P[Pc19l5RPPY19lgRT9?pYD5%2Q#b#g#;#;#;#;#URq/4gS0F%2Q#;#R#a#;#b#M$0ER180|gP[Pc%1Q#a#Y#M$0F#R,\lPY1\lr9?pYD5P[Pc%1Q#a#c#;#R#;#s,\lPX1\l09?pXR0D5P[Pc%1Q#a#c#b#g#R,\lPXP0D5P[Pc%xQ#Y#g#;#g#Y,\lPY19lh9?pYD5%FkRk-0{]R0,8h-08h&0zf%6oRf18o0'01@BAS0G19lA,zlRh=:BA1@mT20xdVS0H=:mTPnPZ\mRZPRPiP<PFP7POJ0>20Ce<1mmBRrPmPl%cL#RRL#FRs-0woPsCARtQ0E%F\R\607mRu%F_R_:07mPRvB07mT]Rw%VrRx5JrRy5JrRz5JrR{3JR|:0Ac7P[P7PTPW19abS0I19aNS0J%VG5JGS0K5JG-06pRGD5P[P7PPPY13g],9lS0L9?pYS0MD5P[P7Q0EPXP`D5'03lRa3lXFZ+0XXrnf[RNPZPRPif\RbPFP7POJ0>20Ceb;laXFZfoRZ9XdcRaPRPiPNPFPaPOJ0>20CeNROB0Aca|RFP[PaPTPWPGD5S0NP[PaPPPYQ0MD5S0OP[PaQ0EPXP`D5S0P'0S0Q'0R`'0RG'0fQS0RPOPGPdPS%`ZPePNfgf`fWL0uPFP`PmPT%rrR`PrPmPl&0tLRL,3oPsCARFPrPmPl13h^P\CAPrPmPl13h5P_CAPrPmPl1zl7S0S/3ARNP]CAPxDZDZ;:|X:mPrPFPrPmPl137^S0TP\CAPrPmPl1375S0UP_CAPrPmPl1zlTRe/3AP]CAPxDZDZ=:`|X5BPgPrPFPrPmPl13A^RZP\CARSPrPmPl13A5RGP_CAROPrPmPl137ARWP]CAPxDZDZ=:`|X5BP`P`1TrF1TrtRt13gARF,9lS0V>07m]Ri=JrxRR9JrORb9JrSP{P`\`R{/@tP`P`1TrS1TruRuPbPz1@{uP`P`1TrO1TrvRvPRPy1@{vP`P`1Tri1TrwPxPxPrP{&0srRvPvPiPwP{\r/@vPBPrQ0V:0PmBB0PmBTP]P]PmPr\BRv20rmBR{P{Q0VPTPv\m/@{PBPm&0qlR{P{PFPgPm\B/@{20po2R{%62%6j[\fRf20o]kRj18A]%6k18A0[[R2%6]S0Wg00JGRvB0n]k<UWBRkQ0W%60\v]BRvg00JcRw#VRi%rwRw20mB<Ry&0kBRR&0jBROPB20iBQRQ20LBARu'CRzg01]:PQCj+0g20fOERbP7P;1@8920e7;$0DdB0dBA<H0cR9b1b2b3X4BA:BW7^4BP7PgO1b0b7b8b9G]G]%I]G]G]1@`xG]G]G]G]PeP{PfPjP2PkPvPiPwPyPRPOPOPO%EqPQ%E19<OQS0XDDS0Y&0QDRxPOPOPuPQ%E]S0Z>0`BlR8:01OQDDChPbP9b1b2b3X4BS0[14q71471S0\'0R118<0-08<[^4BS0]P7PgQ0<O2b0b7b8b9-0@gDnPhP<H00Q0HP7EpPJPrPmPlPlPd%K7RqPqC=S0^%H7S0_CAX?J1mIBS0`&0MU/~L00?sRUQ0`1~H^RI00?\RqQ0`1~H5RS00?_RtQ0`1~KAR}00?]R~Q0`#VDZDZH0_=:`|ePJPr&1NdQ06H0_S0`=:`|RrePrP`Q0`fq9XdcS0`>0Ac7Xn`PdPcQ06fp#BS0afiQ06:1IJ7Q0017U<17q<17t<17~<#q'f'fPlPd%K;R`P`C=R`P`P0%H;RrP`PrP0FGP717U;PJPUQ0^Q0^P0Q0_Q0^Q0_P0FGX?JS0_P{PfPjP2PkPvPiPwPyPRPOQ0C#E9<OQPxPOQ0B#E=<OQPxPOPOPu%EL,CQRrPOPO202r8POPOPu%EsR`1Cr`=<O8DDH03DDChChPbP9b1b2b3X4BQ0C,47Q0B/4<13;LRLPLP0PsPLPsP0FG[[^4BP7PoQ0?Q0@O3b0b7b8b9PlPd%KURoPoC=RoPoP0%HURUPoPUP0FGeP:P7E>W6P7O117q;17t;17~;#q'f'fQ0017q:17t:17~:#q'fPlPd%K>RUPUC=RUPUP0%H>RoPUPoP0FGP717q>PJPqQ0_Q0T#6S0@Q0T/80S0B%6\S0CQ0TP\P0ELX5BPjP2PkPvPiPw&1DBRoPRPOPOPu%E^S0^,CuRUPOPO202U8POPOPu%E\Rs1CUs=<O8DDH03DDPbP9b1b2b3%6ZRU18Z0RLQ0C13Z\S0b/40S0c'0S0d'0S0e'0S0fP7b0b<b=S0gPhP6H00PlPd%KqR`P`C=R`P`P0%HqRqP`PqP0FGeP=P7E>W6P7O117t>17~>#q'fQ0017t=17~=#qPlPd%K@RqPqC=RqPqP0%H@R`PqP`P0FGP717t@PJPtQ0_Q0U#6S0hQ0U/80S0i%6_S0jQ0UP_P0ELX5BPjP2PkPvPiPwPoPRPOPOPu%E5S0k,CuR`POPO202`8POPOPu%E_Rq1C`q=<O8DDH03DDPbP9b1b2b3%6GR`18G0RrQ0j13G_S0l/40S0m'0S0n'0S0o'0S0pP7b0b<b=S0qPhQ0AH00PlPd%KtS0rQ0rC=S0rQ0rP0%HtRtQ0rPtP0FGeP4P7E>W6P7O117~@#qQ0017~4Q01PlPd%K6RtPtC=RtPtP0%H6S00PtQ00P0FGP717~6PJP~Q0_PmPT%6NS0_18N0S00Q0WPNP]P0ELX:mPg%6WS0r18W0S0sQ0WPWP]P0ELX5BP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOA<OuzS0tPOB01Oz8S0uPOPOPuQ0ZQ0Z,Cz=<O8DDI0\ChPbP9b1b2b3X4B13<AS0v#6S0wQ0v/80S0xQ0WQ0vP]P0EL\1^4BP7PgQ0?O2Rtb0b7b8b9PeP{PfPjP2PkPvQ0[Q0]Ptb0b7b8b9-0@gDnQ0HQ0>EpPlPd%K~RtPtC=RtPtP0%H~R~PtP~P0FGeQ03P7E>W6P7O1Q01Q01PlPdQ0A#KR~P~C=R~P~P0Q0A#HRtP~PtP0FGP7n010000000W6P7O1n200100000021100010000W6P7O1n200100000021100011000W6P7O1n200100000021100011000W6P7O1n200100000021100011000%K<%H<5udeWOX?JQ06-1BdefTK1AP|P7E>b6Q0NQ0QP?PdPaflS0QPKPAPVQ0:fPS0NfcS061wVV1433R|PVP3%I3S01PVP3Q01EvPiPwPoPR%E3RJ=<OJPbP9b1b2b3P|P7b0CQS0?1wVY143_R|PVP3Q01PYP_%I_S0WEvPiPwPoPRA<OJqPbP9b1b2b3P|P7b0CQS0yN<0=&05VR|9ud}RtP[Q0a9OdcS0a20<d}S0zPVQ0:,yd9?pVR~D5[P?PdQ0afmPKP3PVQ0;Q0RQ06Q0?Q0yN<0=1~K3S0?=ud|RKP[Q0`Q0?-0<dS06PVQ0;,yd9?pVS0;D5[PmQ0zP[fs9XdcS0zP<PVP~D5\tX:mP<Q0V&0[AE>P[fr9XdcS0RQ0VPVP~D5\tPmQ06P[ft9XdcS06P<PVQ0;D5\KX:mP<13g3RA,9lS0V&0[3E>P[Q0zQ0VPVQ0;D5\KP?Q0zPTQ0IQ0JPgB0Z7]0X5BP{PfPjP2PkPvQ04PiPwPyPRPOPOPCPDPDPEP:J1?Q0X61>OPxQ0Z,CQ=<O8ChPbP9b1b2b3X4BWEQ04Q0\,0<B0Z<]0[^4B]EP7Q0FPgQ0=O3b0b7b8b9PeP{PfPjP2PkPvQ0[Q0]P7PgQ0=O2S0=b0b7b8b9-0@gREDnPBPFP[fu9XdcQ0DPVP~D5\tX5BP<Pg&1=gE>P[Q06PTPVP~D5\tP7PmPTQ0_Q00%6|R~PNP|P0ELX:mPgQ0rQ0sP~PWP|P0ELX5B%6FRW18F0RN13F|S0s/40S0r,0~S00'0S0_'0%63Rc13F3S0D/40S0F'0RD,0NRC,0WPWQ0_PWPCPWPWPWPNQ00PNPDPNPNPNP~Q0rPcQ0FP7X@BRN14<7$1<XvBX@BRDQ0GP|P3PNPNQ02&057#IW@S02PVP3Q01J0HRWJ0GS0FPNPDQ0sQ0DPNPNPNPBPBg01]a13<7H1;#IXoBXpBRCPFPF%IFP|P3PWN:0:P0P0%I0RFL0;E|GWGWP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOQ0tPOQ0uPOA<OuJS0uPO1CzJ00W8H0VI0\ChPbP9b1b2b3X4BQ0wQ0xPcQ0vP3P0EL\1^4BP7PgPMO2RMb0b7b8b9CQPeP{PfPjP2PkPvQ0[Q0]PMb0b7b8b9-0@gDnQ0HP=EpPlPdP}P}C=R}P}P0P~P}P|P0C_CeePteO1b>PgP[Q061373Rt,9lPVQ0K-06pD5X5BP7PmPTQ0S/33R}P}P0P~P}P|P0C_CeX:mPgPtPtP0P~PtP|P0C_CeX5B%6ARt18A0R}13A|S0S/40S0K,0~S0]'0S0['013A3S0v/40S0x,0cRM,0}Rz,0tPtQ0[PtPzPtPtPtP}Q0]P}PMP}P}P}P~Q0KPcQ0xQ0FPNPDQ0SQ0vPNPNPNPCPAPA%IAP|P3PWN:0:P0P0PFL0;E|GWGWP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOPOPu1CQJRQPOPO202Q8POQ0uPO1CQJ00W8H0VH03DDChPbP9b1b2b3X4B13<3RQPQP0PcPQP3P0C_Ce\1^4BQ0=b0b7b8b9CQPePEDnQ0HP>EpPlPdQ0?Q0?C=R1P1P0P~P1P|P0C_CeePKeO1PePEDnL19bAb>bAb>Q0OQ0PP?PdPaQ0QPHP5PYQ08Q0NfeQ0y1wYY14__REPYP_Q0WPYP_Q0WEvPiPwPoPRA<OqqPbP9b1b2b3PEP7b0CQN<0=&05YRE9udSReP[Q0a20<dSRKPYQ08,yd9?pYR|D5[PmPKP[Q0RP<PYP|D5\eX:mP7PPPjP2PkPvPiPwPoPRPOPOPuQ0kQ0k>01O8DDPbP9b1b2b31850-085P7b0b<b=-0U5E>P[Q0`PPPYP|D5\ePmQ0HP[Q0z@18PYR|PpQ0719l]R580R<-0YYCt\eX:mP7PTP;E>P[Q0RPPPYQ07@0RT5R59?pYD5\ePmP5P[Q06PPPYA?pY<D5\eX:mP7Q0L217g]E>Q0M9:[|\eP7Q0hQ0i%6ER|Q0UPEP0ELX5B13GERg/40R],0|RP,0rR5,0`Q0pP`P5P`Q0oP`P`P`PrPPPrQ0nPrPrPrP|P]Q0jQ0mPNPDQ0GPEP_PNPNQ02PYP_Q0WJ0HR]J0GPNPDPgQ0lPNPNPNPCPGPG%IGPEP_P]N:0:P0P0PFL0;E|GWGWQ0qCQPhP=H00PlPdPSPSC=RSPSP0P|PSPEP0C_CeePeeO1b;b;b;b;P?PdPaQ0QPHP^PXQ09Q0Nfd1wVX143\RHPVP3Q01PXP\%I\R3EvPiPwPoPRA<OJsPbP9b1b2b3PHP7b0CQ1wXY14\_RHPXP\P3PYP_Q0WEvPiPwPoPRA<OsqPbP9b1b2b3PHP7b0CQN<0=&05XRH9udIRqP[Q0a20<dIRsPXQ09,yd9?pXRpD5[PmPsP[Q0RP<PXPpD5\qX:mP7Q0EPjP2PkPvPiPwPoPRPOPOPuQ0^Q0^>01O8DDPbP9b1b2b318^0-08^P7b0b<b=-0U^E>P[Q0`Q0EPXPpD5\qP7Q0@Q0B%6HRpQ0TPHP0ELX5B13ZHRB/40R[,0pR^,0LR9,0UQ0fPUP9PUQ0ePUPUPUPLP^PLQ0dPLPLPLPpP[Q0CQ0cPNPDQ0GPHP\PNPNQ02PXP\P3J0HR3J0GPNPDPBQ0bPNPNPNPCPZPZ%IZPHP\P3N:0:P0P0PFL0;E|GWGWQ0gCQPhP:H00PlPdPIPIC=RIPIP0PpPIPHP0C_CeePqeO1b;b;C}C}C}C}C}H0TH0TbTbhbSW[WZW^W_WYWdWfWeW\W]WcWaWbW`f=Q0<Q0>Q0AQ03P6P4P@P=P>P:P;P<P7O>n4000010000001>110810:10910;10510410=10>10<101107106102103bqbHbCWCWMP<P7O2n2001000000121000000W6WJP<P7O2n2001000000121000000W6XgnP<P7O2n2001000000121100000bjbGbIWRWXWWWVWUWKWQWLWNWPWkWmWsWtWuWio"). Qed.
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
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x65a40 pf_sr [] pf_kn 40) [].

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
  getr regs 1 = Z_to_bv 64 0x65994 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA.
Qed.

Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x65994 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB.
Qed.

Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x65994 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC.
Qed.

Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x65994 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
  intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD.
Qed.

Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x65994 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x65a40) mem rom) (mkst regs' (Z_to_bv 64 0x65994) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xee390, 4);
                          (Z_to_bv 64 0xee3b8, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xee3b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xee390) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
ltac2:(KReplay.run1 (kr_t_S1PrintfBuf ()) ["FXALL3"] "h04mem'h15regs'h21Hh32H0h42H1h52H2h62H3h72PHh82R1h93R11h:2R2h;3canh<3memh=1oh>4regsh?3romh@2sphA1wp;1p;2p;4p;3p;5p;;g000Lj16Tg00R=j17Tg002cj1LTg003Aj1TTg00n6j2XTg00STj1RTg00OHj4WTg0011j11Tg01^Ej3ITg01^hj2GTg004Aj20Tg004gj34Tg0296j1YTg00Q]j2=Tg01;gR0j2QTg01ILj5?Tg01J>j3NTg016<j2MTg00\[j2VTg005[j2KTg0176j2JTg007Qj1PTg0183j3HTg0081j1UTg00PFj19Tg00XXj4DTg00U`j2BTg003dj2FTg00TXj2ETg002Hj2CTg010cj2@Tg02:2l;^Tg02:ol;]Tg02;ll;\Tg02<il;[Tg00_mj4ZTg017Sj3STf0R1#6#6p=2%71#6p=3%61#7p=8g00HfR2g00IDR3741p=Of1R4=421p=5f2R5=424/Q1p=;P5P2P4P1CZp=:%71#7p=Af4R6f3R7AS5413Sp=<1C41,C5p=>g00IbR8#6R9#7R:#LR;%69R<#6R=#6R>#2#LR?#TR@'XRA%L=RB#TRC#R\@RDP6P5P4P1CWf6R5%18REg01kZRF5I;'G%38#8#8#3#8#3#8#8#2#1,0?RG54@f7RH%19R9=I;F'G=4@6f8RI%7:#1=I;F'G10?354@f5R3#Y%1<R<,=3RF#O%78R;#1RJ,5F9;F99;FE'QP01=5<RF#O15FJ9;F99;FEg00YIRFp,2fxRKf=RL%38#8#8#3#3#8#2#2#2#1,0?RMf<RNf;ROD?PKP4PGP1POD?3N1ML41V@2RPf:RQ,K?%3>#2#2#1R>'J,0?=:@>PP%78#3#A#3#2#A#3#8#2#2#1,0?RR=:@<RSPP%78#3#A#3#2#A#3#A#3#2#1,0?R8%1=5:@R=PPf9RT,0?RU=:@9%PPRVD<D<9HN1%UCRW#RRXPFP1PUg00[>#9#9RUCDPC%2;#2#1,0BPC%6:#1,0B%PCD<,BWRC34PFP1P8%9U#9R8#9#9#9#9RBCDR;1FT9,0?,EB,BW54XPFP1PRP8CD%1:,0?,E8,BW54XR8'C3>3>X0D,@DX1A,@AP11=H<R:#OPNPOPQPTPIPHP5P1P3P6P7M;^W3P1O115:J9;:99;:EP01=I<R:/5E15:J9;:9PKf?R:PMf>R7PLD?PKP4PGP1PLD?5NF1M:4PP1K?N/J>,0?=:@>PPPSPPP=PP10?OR6=:@9PVD<D<9H71PFP1P6PUCD=4XC1FO9,0?,EB,BW94X;/C83>3>X0D,@DX1A,@AP11=T<R6/5EP7PLPNPOPQPTPIP1PHP5P3M;]W4P1O1156J9;69P01=Q<R0/59150JPKfAR0PMf@RMP:D?PKP4PGP1P:D?5NF1M04PP1K?7/J>,0?=:@>PPPSPPP=PP10?LRP=:@9PVD<D<9HM1PFP1PPPUCD=4XC1FL9,0?,EB,BW94X;/C83>3>X0D,@DX1A,@AP11=O<R</59PMP:P7PLPNPOPQP1PTPIPHM;\W5P1O115<JPMP:P7PLPNPOPQP1PTPIPHM;[W6P1O1n200100001021000010000W2P1O1n200100001021000011000W2P1O1n200100001021000011000b=W9W:W8W7X;2XA2X@@X?DW<W>o"). Qed.

End FXALL3.

