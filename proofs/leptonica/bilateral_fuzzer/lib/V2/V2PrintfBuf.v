(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim SymExec RefMemcpyLib AgentLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymAux RefPrintfLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2PrintfBufBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2PrintfBuf () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8AgentLib7u64_litC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common8PropExec6v_addiK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26a_baseC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26edenotC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25a_offC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26adenotK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux7sregionC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indI5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase3pfH00K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun6stk_okI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase5PF_FRI47Corelib4Init9Datatypes4prod00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sym_execK47Corelib4Init9Datatypes4prod01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux;log_coveredC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux9same_regsC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25carryC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive5kreadK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S9scs_denotC5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase:pf_regs_okC5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase3pfEC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase:pf_know_okC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7know_okC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun9run_soundC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S8log_flatC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S9mem_denotI47Corelib4Init5Logic2ex00c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf7pf_postC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S8sc_denotK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun;carry_afterC5ARocqVerifyHarness?AgentSubmission6Common8PropExec9u64_rangeC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX22evC5ARocqVerifyHarness?AgentSubmission6Common<RefMemcpyLib8keeps_csC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5Frame9frame_modC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux@keeps_cs_of_sameK47Corelib7Numbers7BinNums1Z03C35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux6rdenotC46Stdlib5Lists4List2InI47Corelib4Init5Logic2or00C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S4flatC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAux<regions_flatC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymAuxAlog_covered_frameI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive9kread_rdnC56Stdlib6ZArith6BinInt1Z6of_natc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf;adenot_var1K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib5rdn_2c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf;adenot_lit0C4ELinuxProcessSemantics5Riscv3Sem5alu64C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib9alu_add_ZK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses6eq_iffI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr00I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf7pf_fuelc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf8pf_stopsI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00C5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase5pf_srI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00C5ARocqVerifyHarness?AgentSubmission2V2?V2PrintfBufBase5pf_knc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf:pf_regionsC5ARocqVerifyHarness?AgentSubmission6Common<RefMemcpyLib<callee_savedK4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01C56Stdlib6ZArith6BinInt1Z3eqbC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib:mod4_shiftC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib7bt_and3C47Corelib4Init9Datatypes4negbC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib9bt_and3_0K47Corelib5Lists7ListDef6Forall02c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf7pf_caseK47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf5dirsAc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4resAc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4carAK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf5dirsBc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4resBc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4carBc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf5dirsCc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4resCc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4carCc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf5dirsDc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4resDc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf4carDC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<RefPrintfLib:mod4_casesc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf8pf_caseAc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf8pf_caseCc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf8pf_caseBc5ARocqVerifyHarness?AgentSubmission2V2;V2PrintfBuf8pf_caseD".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition pf_stops : list Z := [0x17c14].
Definition pf_fuel : nat := 3000.

(* [comment removed for export] *)
Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0x46020, 4); (SA (ELit 0) 0x46048, 8); (SA (EVar 1) 0, 2)].

(* [comment removed for export] *)
Section VP0.
  Context {fx : FPState}.   (* [comment removed for export] *)
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x17cc0) mem rom) (mkst regs' (Z_to_bv 64 0x17c14) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x46020, 4);
                          (Z_to_bv 64 0x46048, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x46048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x46020) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
End VP0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  Context {fx : FPState}.   (* [comment removed for export] *)
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x17c14.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_V2PrintfBuf ()) ["Package"] "h02Hah12Hkh27__arithh34__ffh47__sat12h57__sat13h68__varmaph75__with81kh91zp;2p;1p;3p;4p;7p;6g0000j21Tg000Lj10Tg0011j18Tg001Oj2?Tg001lj24Tg002Hj29Tg002cj1ITg003Aj1CTg003dj2ATg004Aj23Tg004gj32Tg005Aj2;Tg005[j2<Tg006Ej2VTg006mj3UTg007Qj1TTg0081j1OTg008Qj1NTg008oj1LTg009Mj1HTg00:8j25Tg00:[j4:Tg00;Fj3BTg00;ij7DTg00<Mj2ETg00<oj2FTg00=[j3GTg00>:j4@Tg00>lj2JTg00?hj6KTg00@Fj27Tg00AAj1>Tg00BJj2MTg00CTj1=Tg00D]j2PTg00Efj1QTg00Fnj2RTg00H7j7STf1R0g00H[R1g00I:R2P2g00IZR3f0R4g00J:FSp=6g00JZR5g00K8R6/14g00KV#0R7#8R8%07#0#0#0#0R7#8R9'?R:,44'9P5P6%I7R7#CR;f2R<,A4,37137<32X951370R=,;;1376R>,<71V8914681169146:R?[[1168R@g00L;RAAU890UW0116:\A^0@g00LWR@#T%O@%N5%L5%H5R@P1P2P2P3P51556R2g00MCP2C:,6@P5P2g00Mj1558=B57C:,6@FD1E@3P4P<g00NQR@g00O1R3';1F4<=2@3dAG560C@b3b6b71166/9?P4b2b4b5,J6EK17>0=2;=ep,1ER>%>6/M0R0#='P%Q0'7=2;=e1R>0=2;=eW1W8o"). Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
Proof.
ltac2:(KReplay.run1 (kr_t_V2PrintfBuf ()) ["Package"] "p'0h02Hah14__x1h24Pbszi004Pbszh34Pcani014Pcanh46Pcan64i026Pcan64h56Pflagsi036Pflagsh64Pimgi044Pimgh74Plbfi054Plbfh85Plocki065Plockh95Psp16i075Psp16h:5PspHii085PspHih;5PspLoi095PspLoh<4Pstki0:4Pstkh=2Pwi0;2Pwh>5Pwendi0<5Pwendh?5Pwposi0=5Pwposh@7__arithhA4__ffhB7__sat65hC7__sat66hD7__sat67hE8__varmaphF5__withG1ihH1khI1phJ1zp;4p;1p;2p;3p;8p;6p;7p100OQp4p70R0p100PUp4p710p8P0p100Q1p4p710p8g00QMR0j4tTg000Lj11Tg002cj1OTg003Aj1XTg00RJj1:Tg00Rij1aTg00BJj2TTg00Fnj2STg003dj2GTg004Aj27Tg004gj32Tg005[j2NTg0011j1>Tg00T2j2qTg00TRj10Tg0000j29Tg00U7j4[Tg001lj2ETg002Hj2DTg00V:j1RTg00V\j1QTg0081j1PTg00W>j2?Tg00XFj2ATg001Oj2ZTg005Aj2YTg00Xhj2sTg006Ej2rTg006mj3pTg007Qj1oTg00YYj2nTg008oj1jTg009Mj1iTg00:8j2JTg00Z7j2dTg00;Fj3cTg00:[j4UTg00ZZj8bTg00<Mj2eTg00<oj2fTg00=[j3`Tg00>:j4gTg00>lj2hTg00?hj6_Tg00@Fj2WTg00CTj1kTg00D]j2^Tg00Efj1lTg00[>j4mTg00H7j7]Tg00;ij7\Tf0R1#1#1p=6%01#1p=3%01#0p=5%11#1#1#0p=@%11#1#1#1p=4%11#>p=F%01#0#0#0p=L%01#0#0#0#0#0#0#0p=H%01#1#1#1p=Cf1R2%11#1#>'7p=8g00\6R3f2R4P2P1Cmp=<%>1,72p=K%11#0#0#1p==%11#0p=Bg00K8R5/91p=;g00JZR6P2g00MCP1CUp=MP2g00H[R7g00I:R8P8g00IZR9P1g00J:F]p=IP4P7P8P8P9P2P1F\p=Vp,2PHp,3memR:p,2spR;p,1wR<p,3canR=CtP0P:P;P<P=g00KVR0#1R>#6R?#1R@#6RA#ORB#XRCp,1ERDg00]H#:RE#aRF/T4'S1G<4,7B32P11NB;RG%>@R@'qRH=265%00#3#5#3#3#@#4#F/9G%00#5#L#H#H#HRI#0#5#L#H#>,9GP3P:P;g00]gC[%4AR;#1#4#F/91%10#6#3#C#4#4#F,E1'D%O?#XR?#RP:17B2O1%Q?32[^G6%P?R?#RR3%@0#C#4#C,8B%:E#:#:RE5<:%0>,KB,?E,A?32%@0#C#@#4,8B%:E#:#:#:RJ5<:%50#=#5#B#B#4,8B,?J,A?523%@0#C#@#6#3,8B=<:J17B<RK,?J,A?523%00#3#5#B#6#3#3#4#FRL/9<%00#3#5#=#3#B#L#FRM,9<'D%60#=#4#3#4,8B=<:J1KB;,?J,A?523%60#=#4#3#3#5,8B=<:E1KBI,?E,A?RI523%60#=#4#3#5#6,8B=<:E=23I%50#=#B#6#5#=,8B=<:J17B=,?J,A?523%;=%>>R>%>ARA'ZR3,E='DP6P<fNR=,G1,7B1G<=,7B52CXJ6fMR=,G<,7BR?,YC1NBK1sG@%;G%;@%;H[[1r>A1E5>%;A1E53[[%;>RHg00L;R@Ap>A2UW0%;3\@^0Hg00LWRH#o%PH1n62%j6%i6RHP7P8P8P91J6L1d60R0'M,IH1J6M,M0,IH5VH%Q81J65/M0,IHP6P0g00Mj1J6>=c6BCU,IH5VHGb1eH9P1P4g00NQRHg00O1R9'Y1f14=2H9dA`652CgbAbEbFX1619L1191M'D%;21E23'D[^16P1P<f9R3O2b@bBbCbD,h<E_1WK==2C?e1TF=R=#k,^D%l='W=2C?e1SD==2C?eW4W3W7W8W2W=W?W>W5W6W<W:W;W9f=f<f;f:P3f8f7f6f5f4f3P4P2P1O>n4000010000001>110710910810:10410310<10=10;100106105101102bIXH6o"). Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x17cc0 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x17c14 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0x46048 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0x46020 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
Proof.
ltac2:(KReplay.run1 (kr_t_V2PrintfBuf ()) ["Package"] "p'0h07__arithh17__sat65h27__sat66h37__sat67h44__ffh58__varmaph65__with74__x1h81zh91Hh:1bh;1Bh<2B0h=1rh>1xi001xh?2B1h@2HahA3HmshB1RhC4__p1hD4mem'hE2HKhF3HK'hG2HRhH3HR'hI6HcarryhJ4HcovhK3HlfhL3HpchM2HrhN4HrunhO5HsamehP3HschQ3HsphR3Hw1hS2K1hT2K2hU2K3hV2K4hW4Pbszi014PbszhX4Pcani024PcanhY6Pcan64i036Pcan64hZ6Pflagsi046Pflagsh[4Pimgi054Pimgh\4Plbfi064Plbfh]5Plocki075Plockh^5Psp16i085Psp16h_5PspHii095PspHih`5PspLoi0:5PspLoha4Pstki0;4Pstkhb2Pwi0<2Pwhc5Pwendi0=5Pwendhd5Pwposi0>5Pwposhe2R'hf2Z0hg4dirshh1ehi3hs'hj1ihk3kn'hl1lhm1mhn1nho1php5regs'hq4scr'hr3scshs3ss'ht1yp%0p&0p&1p;1p;2p;3p;5p;7p;4p;6p;Dp;=p;8p;<p;Bg0081j1lTg00^dj2hTg007Qj1^Tg00_Dk30JTg000Lj14Tg00RJj1UTg00`Pk51OTg00a^k71ITg00bij4ck30Lk20pTg004gj3:Tg00cIj1RTg00dPj1GTg00eXk20|Tg00f`j1bTg00gik30zTg00hok30wTg00V:k10BTg00AAj1uTg00j7k502Tg00Rik10KTg0011j1HTg00k;k30jTg00TRj15Tg00lDk40bTg00mVk70_Tg00nXk40^Tg00oSj3mTg010ck61NTg011ek40\Tg0135mD1MTg002ck10GTg003Ak10YTg014;k21GTg014gj2_Tg0168j3TTg017JR0k20TTg017dk61:Tg002HR1j20Tg00Q1j6BTg004Aj29k10oTg018_k315Tg01:0k214Tg01:Qm=12Tg00QMR2k411Tg005[j2zTg00T2k20}Tg0000R3j21Tg00U7k40{Tg001lj28Tg00V\k10MTg001Ok20xTg01;Yk10vTg005Aj2ITg01<Wk20uTg01=\k20ATg01>]k20tTg01?:j3Kj2\k10qTg01?Zk30@Tg00XFk204Tg003dR4j22Tg01@_k80sTg01Alk10rTg00Xhk20nTg006Ek20mTg006mk30lTg00YYk20kTg008ok10iTg009Mk10hTg00Z7k20gTg00:8k20ITg00:[j4oTg00<Mk20dTg00<ok20cTg00=[k30aTg00>:k40`Tg01BJj8XTg00;Fk30]Tg00>lj2~Tg00?hj6nTg00BJj2|Tg00PUk40[Tg01Bgk11LTg01Cjk31HTg01DAS00j2`Tg008Qk11FTg01D[j3rTg01Ehk21ATg01G1k71?Tg01H?R5j2sTg01HYj4STg01IDm<0<Tg01JLR6k10;Tg00Fnk20:Tg00D]j2vTg01Jlk10VTg01Kkk61>Tg01LOk11<Tg01M0k11;Tg01MNk419Tg01N1j6yTg01NZk818Tg01Obk20PTg01Pak30RTg00W>k20STg01QIk216Tg01RUj4xTg01S0k40ZTg01SJk50HTg01TCk30OTg00[>k40WTg01U>k313Tg00H7j7gTg00;ij7iTg00ZZk81BTg01Uak31CTg00CTk11DTg00Efk110Tg01V>k31ETg01V[m<0?Tg01W@m<0~Tg01WemB1JTg01XKk31KTf0R7#5#5#5#5p={%57#4p=<%47#5p=M%57#4#4#4p=w%47#4#4#Hp=Y%U7#Up>0f%U7#U#U#Up=Q%47#4#4#4p==%47#Hp>0Fg00NQR8g00O1R97:7p>0C%47#4p=;%57#5p=Af3R:f2R;f1R<00473:p=qf5R=f4R>19:;P<P7I0Hp>1@g00\6R?f6R@P=P>19:;P<P7I0H40Op=V10<7,0;p=k%G79T;<p=ZP>P:P;P<P7I0H:0O?=p>03%57#5#5#5#5#5#5#5p>0720S<7-04;p=@P?P:P;P<H0W=:>7p=3%47#5#5#4p=a%H7,9<p=W11<7,0;p>0yg00K8RA/1</07p>0611A7p=6P:g00JZRB19;<P7Ccp=CP;PBP<P7Ccp>05AK;<79K>:p=]B13B<7p=EP<g00H[RCg00I:RDPDg00IZREP7g00J:RFFgp>0e1IB7p=L20IB7p=DP;PCPDPDPEPBP<g00MCRGP7CoPFFgp=>P>PCPDPDPEP:PCPDPDPEPBP;PGP<CoPFFgP7Fip=FP;PCPDPDPEPBP<g00MjRHP7CoPFFgp>01P:PCPDPDPEP;P<P7L1Bp=fPBP>P:P;P<P7Enp=pPBPAP:P;P<P7Enp=}g01Y1RI@1CB7p=N&1D<,v;,z:&107'2p=?B1EIB7p=OPIPBP<P7Ccp>00g00OQRJ?:<7p=7g01Z;S01,`7p=j11A@18=>11A:12;</17'0'0'0p=JPBP<PHP7Cop>0>P:PCPDPDPEP;PCPDPDPEP<PFFgP7Fip>0=12;</17,0:,0>,0=p=PP>PCPDPDPEP:P;PCPDPDPEP<P7FiFip>0Xg01ZXS02PBP5P6P3g01[7P=P>P:P;P<P7N<0?p=t12;</17p>0UP;PCPDPDPEP<P7Fip>1=Q02PBPBPBP6P6P=P>P:P;P<P7N<0~p>0EPBPBP3P=P3P>PAPAP:P;P<P7N<0?p>0DPBPBPBPBPBPBP4P7P<P;P4P:P>P=P@f7R4f8R6f9S03NB1Jp>08PBPBP3P4P3P@P=P>P:P;P<P7N<0?p>09P4P@P=P>p-0S04/I<:1K:;P7Eyp=[PBP<PGP7Cop>0QP:PCPDPDPEP;P<PCPDPDPEP7PFFgFip>0N12;</17,0:p=d11A:18;</07'0p=eP?P;P<P7H0Wp>17%l8S05g01[YRFg01\gRG#lR3g01^4R5g01_@#lRHQ051hF3RK/h5P?g01`KRLP9g01aFRMg01bBRN#^RO%^8RP60J=g00KVRQ#4#{#<#M#w#YRRg01cKRSg01dH#^g01eSRTg00]HRU#URV#URW$0fRX#QRY#Q#Q#Q#Q#Q#Q#Q#QRZI1O%^GR[K1IPKP5PFP3P>P:CcP;Cc3:%R=%4Q#{#<#=#<#<$0FRF5:Bg01fPS06%G@+0|$0C%b4g01gN60zS$0C1hH3R5Q05'h%G6@0wTPP5Q05PHP3P=P[CcP>Cc3:&0BNR3P?P@%uARH%4Q#;#A#;#=#<#M#YR5PYI02PNg01hSS07&0KVRK%4QR\#HR]#u40jS08CqP3P?P4PH%4Q#;#A#;#=#M#;#YR^PXI02PN%5\R_#HR`#uS09CqP3P?P6PKPAPVI02PN%5QRa#4#YRb#uS0:CqP3P?Q03PK%HQR3PVI02PN&0F_RN#uS0;CqP?p,3memRcp,1ERdf<S0<H0bp,4regsRep,2spRfp,1wRgp,3canRhp,2R1p,2R2p,3R11K0_PePfPgPhH0^Ri?mSePePcPfPgPhp,2PHRjJ1NP?PiPcPTH0\p,2fxRiP?PLPMfARM@0JOPPRPSPTPZf@S0=f?f>RZPdPcp,3romROPef;S0>P<P7P;ND1M&0G_%4\R\#4R_#4RL#;Rk$0GRl$0YRm+1GRn%bM=md7%GMRo,_dPiPePlPRPcPOJ1@RRPiP7Pl%RMATdcoPOFV3kXBn+0TP0PnfBR0#b=md7%G0Ro,_dPRPiP7Pl%R0ATdcoPOFV3kXBnPiPePcPOPfPgJ1:RoP7fDR0#b=md7%G0Rp,_dPRPiP7Pl%R0ATdcpPOFV3kP1fERp#b=md<%GpR0,_dPRPiP<Pl%RpATdc0POFV'0PoP7fGS0?#b=md:fHS0@#GR0,_dPRPiP>PlQ0@#RATdc0POFV'0P1fIR1#GR0,_dPRPiP=Pl%R1ATdc0POFVPoP7fKR0#G,_dPRPiP6PlfLR1#RAZdc1POFVPBfMR1#RPRPif:S0APlP7fN#GRq9TdcRrPOFVX8BP7PFQ0?EBPRPiQ0319lFRFAZdc1POJ03P?PdPcPqPTPPP0P[fJPpP;PZB15?cd-14GN=12P?PdPrP0H0\PjPcPfPgPhH11P2PcPfPgPhPoP71zlfRo%HLR2+0}Rj=:BA%5Q#<#A#<#w#M#;#YS0B/1o%Aa#{$07$07$07Ra#5#A#{$07#HS0C,1oP?PcPfg00]gH0{%=kR0#4#;#Y/17%4Q#;#<#<#=#=#Y,87'0&0G_Rr$0YRG$0BRZPc19l<S0DO1&0MG3:[^jB%lGRp$0BR[Pc19l^S0EPX19l`9@pXR`D3P[Pc%;Q#a#=#M#;#=,WlPY%AQ#a#A#M#M#;#=,Wl9@pYD3P[Pc19l5RPPY19lgRT9@pYD3%5Q#<#A#M#;#<#w#YRq/1gS0F%5Q#<#A#a#<#M#{$0FR180ygP[Pc%;Q#a#=#w#=,WlPY1Wl09@pYD3P[Pc%;Q#a#=#<#<#A#;,WlPX1Wla9@pXRaD3P[Pc%;Q#a#=#<#A#=,WlPXPaD3P[Pc%AQ#a#M#;#A#M#w,WlPY19lh9@pYD3%HkRk-0x]Ra,8h-06h&0vf%6oRf18oa'01IBAS0G19lA,zlRh=:BA1ImT20udVS0H=:mTPnPZ\mRZPRPiP<PFP7POJ0320Ae<1hmBR0PmPl%<L#=RL#HRs-0toPsCCRtQ0E%H\R\605mRu%H_R_:05mPRvB05mT]Rw%^0Rx5K0Ry5K0Rz5K0R{3KR|:0@c7P[P7PTPW19rbS0I19rNS0J%^G5KGS0K5KG-04pRGD3P[P7PPPY12g],9lS0L9@pYS0MD3P[P7Q0EPXP`D3'03kRr3kXDZ+0TXpnf[RNPZPRPif\RbPFP7POJ0320Aeb;krXDZfoRZ9ZdcRrPRPiPNPFPrPOJ0320AeNROB0@cr|RFP[PrPTPWPGD3S0NP[PrPPPYQ0MD3S0OP[PrQ0EPXP`D3S0P'0S0Q'0R`'0RG'0fQS0RPOPGPdPS%bZPePNfgf`fWL0sPFP`PmPT%l0R`P0PmPl&0rLRL,2oPsCCRFP0PmPl12h^P\CCP0PmPl12h5P_CCP0PmPl1zl7S0S/2ARNP]CCPxD]D];:|X:mP0PFP0PmPl127^S0TP\CCP0PmPl1275S0UP_CCP0PmPl1zlTRe/2AP]CCPxD]D]=:`|X8BPgP0PFP0PmPl12A^RZP\CCRSP0PmPl12A5RGP_CCROP0PmPl127ARWP]CCPxD]D]=:`|X8BP`P`1\0F1\0tRt12gARF,9lS0V>05m]Ri=K0xRR9K0ORb9K0SP{P`\`R{/ItP`P`1\0S1\0uRuPbPz1I{uP`P`1\0O1\0vRvPRPy1I{vP`P`1\0i1\0wPxPxP0P{&0q0RvPvPiPwP{\0/IvPBP0Q0V:0LmBB0LmBTP]P]PmP0\BRv20pmBR{P{Q0VPTPv\m/I{PBPm&0olR{P{PFPgPm\B/I{20no2R{%62%6j[\fRf20m]kRj18A]%6k18Aa[[R2%6]S0Wg00L;RvB0l]k<UW@RkQ0W%6a\v]@Rvg00LWRw#^Ri%lwRw20kB<Ry&0iBRR&0hBROPB20gBQRQ20IBARu'ERzg01i?PQCo+0e20dOERbP7P;1I8920c7;$0CdB0aBA<H0`R9b4b5b6X7BA:BW7^7BP7PgO1b0b1b2b3GXGX%L]GXGX1I`xGXGXGXGXPeP{PfPjP2PkPvPiPwPyPRPOPOPO%DqPQ%D19>OQS0XDFS0Y&0MDRxPOPOPuPQ%D]S0Z>0]BlR8:01OQDFCfPbP9b4b5b6X7BS0[11q71171S0\'0R118<a-06<[^7BS0]P7PgQ0<O2b0b1b2b3,~gDpPhP<C}Q0HP7EnPJP0PmPlPlPd%N7RqPqC?S0^%O7S0_CCX=J1hIBS0`&0KU/|L000sRUQ0`1|H^RI000\RqQ0`1|H5RS000_RtQ0`1|KAR}000]R~Q0`#^D]D]H0[=:`|ePJP0&1LdQ06H0[S0`=:`|R0eP0P`Q0`fq9ZdcS0`>0@c7Xl`PdPcQ06fp#GS0afiQ06:1HJ7Q0017U<17q<17t<17~<#j'`'`PlPd%N;R`P`C?R`P`Pa%O;R0P`P0PaFJP717U;PJPUQ0^Q0^PaQ0_Q0^Q0_PaFJX=JS0_P{PfPjP2PkPvPiPwPyPRPOQ0C#D9>OQPxPOQ0B#D=>OQPxPOPOPu%DL,EQR0POPO20>08POPOPu%DsR`1E0`=>O8DFH0=DFCfCfPbP9b4b5b6X7BQ0C,17Q0B/1<12;LRLPLPaPsPLPsPaFJ[[^7BP7PoQ0?Q0@O3b0b1b2b3PlPd%NURoPoC?RoPoPa%OURUPoPUPaFJeP:P7EBW9P7O117q;17t;17~;#j'`'`Q0017q:17t:17~:#j'`PlPd%N>RUPUC?RUPUPa%O>RoPUPoPaFJP717q>PJPqQ0_Q0T#6S0@Q0T/8aS0B%6\S0CQ0TP\PaEPX8BP{PfPjP2PkPvPiPw&1FBRoPRPOPOPu%D^S0^,EuRUPOPO20>U8POPOPu%D\Rs1EUs=>O8DFH0=DFPbP9b4b5b6%6ZRU18ZaRLQ0C12Z\S0b/1aS0c'0S0d'0S0e'0S0fP7b0b1b2b3S0gPhP6C}PlPd%NqR`P`C?R`P`Pa%OqRqP`PqPaFJeP=P7EBW9P7O117t>17~>#j'`Q0017t=17~=#jPlPd%N@RqPqC?RqPqPa%O@R`PqP`PaFJP717t@PJPtQ0_Q0U#6S0hQ0U/8aS0i%6_S0jQ0UP_PaEPX8BP{PfPjP2PkPvPiPwPoPRPOPOPu%D5S0k,EuR`POPO20>`8POPOPu%D_Rq1E`q=>O8DFH0=DFPbP9b4b5b6%6GR`18GaR0Q0j12G_S0l/1aS0m'0S0n'0S0o'0S0pP7b0b1b2b3S0qPhQ0AC}PlPd%NtS0rQ0rC?S0rQ0rPa%OtRtQ0rPtPaFJeP4P7EBW9P7O117~@#jQ0017~4Q01PlPd%N6RtPtC?RtPtPa%O6S00PtQ00PaFJP717~6PJP~Q0_PmPT%6NS0_18NaS00Q0WPNP]PaEPX:mPg%6WS0r18WaS0sQ0WPWP]PaEPX8BP{PfPjP2PkPvPiPwPyPRPOQ0YPxPOA>OuzS0tPOB01Oz8S0uPOPOPuQ0ZQ0Z,Ez=>O8DFI0XCfPbP9b4b5b6X7B12<AS0v#6S0wQ0v/8aS0xQ0WQ0vP]PaEP\1^7BP7PgQ0?O2Rtb0b1b2b3PeP{PfPjP2PkPvQ0[Q0]Ptb0b1b2b3,~gDpQ0HQ0>EnPlPd%N~RtPtC?RtPtPa%O~R~PtP~PaFJeQ03P7EBW9P7O1Q01Q01PlPdQ0A#NR~P~C?R~P~PaQ0A#ORtP~PtPaFJP7n010000000W9P7O1n200100000021100010000W9P7O1n200100000021100011000W9P7O1n200100000021100011000W9P7O1n200100000021100011000%N<%O<5rdeWMX=JQ06-1AdefTK1?P|P7EBb9Q0NQ0QP?PdPrflS0QPKPAPVQ0:fPS0NfcS061sVV1133R|PVP3%L3S01PVP3Q01EtP{PfPjP2PkPvPiPwPoPR%D3RJ=>OJPbP9b4b5b6P|P7b0b1b2b3CSS0?1sVY113_R|PVP3Q01PYP_%L_S0WEtP{PfPjP2PkPvPiPwPoPRA>OJqPbP9b4b5b6P|P7b0b1b2b3CSS0yN<0<&0;VR|9rd}RtP[Q0a9TdcS0a20:d}S0zPVQ0:,vd9@pVR~D3[P?PdQ0afmPKP3PVQ0;Q0RQ06Q0?Q0yN<0<1|K3S0?=rd|RKP[Q0`Q0?-0:dS06PVQ0;,vd9@pVS0;D3[PmQ0zP[fs9ZdcS0zP<PVP~D3\tX:mP<Q0V&0VAEBP[fr9ZdcS0RQ0VPVP~D3\tPmQ06P[ft9ZdcS06P<PVQ0;D3\KX:mP<12g3RA,9lS0V&0V3EBP[Q0zQ0VPVQ0;D3\KP?Q0zPTQ0IQ0JPgB0U7]aX8BP{PfPjP2PkPvQ04PiPwPyPRPOPOPCPDPDPEP:J1>Q0X61=OPxQ0Z,EQ=>O8CfPbP9b4b5b6X7BWCQ04Q0\,0<B0U<]a[^7B]CP7Q0FPgQ0=O3b0b1b2b3PeP{PfPjP2PkPvQ0[Q0]P7PgQ0=O2S0=b0b1b2b3,~gREDpPBPFP[fu9ZdcQ0DPVP~D3\tX8BP<Pg&1<gEBP[Q06PTPVP~D3\tP7PmPTQ0_Q00%6|R~PNP|PaEPX:mPgQ0rQ0sP~PWP|PaEPX8B%6FRW18FaRN12F|S0s/1aS0r,0~S00'0S0_'0%63Rc12F3S0D/1aS0F'0RD,0NRC,0WPWQ0_PWPCPWPWPWPNQ00PNPDPNPNPNP~Q0rPcQ0FP7X>BRN11<7$1;XtBX>BRDQ0GP|P3PNPNQ02&0;7#LW>S02PVP3Q01J0ERWJ0DS0FPNPDQ0sQ0DPNPNPNPBPBg01if12<7H19#LXmBXnBRCPFPF%LFP|P3PWN:08PaPa%LaRFL09EyG[G[P{PfPjP2PkPvPiPwPyPRPOQ0YPxPOQ0tPOQ0uPOA>OuJS0uPO1EzJ00Q8H0NI0XCfPbP9b4b5b6X7BQ0wQ0xPcQ0vP3PaEP\1^7BP7PgPMO2RMb0b1b2b3CSPeP{PfPjP2PkPvQ0[Q0]PMb0b1b2b3,~gDpQ0HP=EnPlPdP}P}C?R}P}PaP~P}P|PaCdCeePteO1b<PgP[Q061273Rt,9lPVQ0K-04pD3X8BP7PmPTQ0S/23R}P}PaP~P}P|PaCdCeX:mPgPtPtPaP~PtP|PaCdCeX8B%6ARt18AaR}12A|S0S/1aS0K,0~S0]'0S0['012A3S0v/1aS0x,0cRM,0}Rz,0tPtQ0[PtPzPtPtPtP}Q0]P}PMP}P}P}P~Q0KPcQ0xQ0FPNPDQ0SQ0vPNPNPNPCPAPA%LAP|P3PWN:08PaPaPFL09EyG[G[P{PfPjP2PkPvPiPwPyPRPOQ0YPxPOPOPu1EQJRQPOPO20>Q8POQ0uPO1EQJ00Q8H0NH0=DFCfPbP9b4b5b6X7B12<3RQPQPaPcPQP3PaCdCe\1^7BQ0=b0b1b2b3CSPePEDpQ0HP>EnPlPdQ0?Q0?C?R1P1PaP~P1P|PaCdCeePKeO1PePEDpL18b?b<b?b<Q0OQ0PP?PdPrQ0QPHP5PYQ08Q0NfeQ0y1sYY11__REPYP_Q0WPYP_Q0WEtP{PfPjP2PkPvPiPwPoPRA>OqqPbP9b4b5b6PEP7b0b1b2b3CSN<0<&0;YRE9rdSReP[Q0a20:dSRKPYQ08,vd9@pYR|D3[PmPKP[Q0RP<PYP|D3\eX:mP7PPP{PfPjP2PkPvPiPwPoPRPOPOPuQ0kQ0k>01O8DFPbP9b4b5b6185a-065P7b0b1b2b3-0P5EBP[Q0`PPPYP|D3\ePmQ0HP[Q0z@17PYR|PpQ0719l]R580R<-0SYCq\eX:mP7PTP;EBP[Q0RPPPYQ07@0RT5R59@pYD3\ePmP5P[Q06PPPYA@pY<D3\eX:mP7Q0L216g]EBQ0M9:[|\eP7Q0hQ0i%6ER|Q0UPEPaEPX8B12GERg/1aR],0|RP,00R5,0`Q0pP`P5P`Q0oP`P`P`P0PPP0Q0nP0P0P0P|P]Q0jQ0mPNPDQ0GPEP_PNPNQ02PYP_Q0WJ0ER]J0DPNPDPgQ0lPNPNPNPCPGPG%LGPEP_P]N:08PaPaPFL09EyG[G[Q0qCSPhP=C}PlPdPSPSC?RSPSPaP|PSPEPaCdCeePeeO1b;b;b;b;P?PdPrQ0QPHP^PXQ09Q0Nfd1sVX113\RHPVP3Q01PXP\%L\R3EtP{PfPjP2PkPvPiPwPoPRA>OJsPbP9b4b5b6PHP7b0b1b2b3CS1sXY11\_RHPXP\P3PYP_Q0WEtP{PfPjP2PkPvPiPwPoPRA>OsqPbP9b4b5b6PHP7b0b1b2b3CSN<0<&0;XRH9rdIRqP[Q0a20:dIRsPXQ09,vd9@pXRpD3[PmPsP[Q0RP<PXPpD3\qX:mP7Q0EP{PfPjP2PkPvPiPwPoPRPOPOPuQ0^Q0^>01O8DFPbP9b4b5b618^a-06^P7b0b1b2b3-0P^EBP[Q0`Q0EPXPpD3\qP7Q0@Q0B%6HRpQ0TPHPaEPX8B12ZHRB/1aR[,0pR^,0LR9,0UQ0fPUP9PUQ0ePUPUPUPLP^PLQ0dPLPLPLPpP[Q0CQ0cPNPDQ0GPHP\PNPNQ02PXP\P3J0ER3J0DPNPDPBQ0bPNPNPNPCPZPZ%LZPHP\P3N:08PaPaPFL09EyG[G[Q0gCSPhP:C}PlPdPIPIC?RIPIPaPpPIPHPaCdCeePqeO1b;b;CxCxCxCxCxH0ZH0ZbRbfbQWYWXW\W]WWWbWdWcWZW[WaW_W`W^f=Q0<Q0>Q0AQ03P6P4P@P=P>P:P;P<P7O>n4000010000001>110810:10910;10510410=10>10<101107106102103bobFbAWAWKP<P7O2n2001000000121000000W9WHP<P7O2n2001000000121000000W9XenP<P7O2n2001000000121100000bhbEbGWPWVWUWTWSWIWOWJWLWNWiWkWqWrWsWgo"). Qed.
End Package.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x17cc0 pf_sr [] pf_kn 40) [].

(* [comment removed for export] *)
Definition dirsA : list bool := [true; true; false; true; true].  (* [comment removed for export] *)
Definition dirsB : list bool := [false; false; true; true; true].    (* [comment removed for export] *)

Definition dirsC : list bool := [false; false; true; true; true].   (* [comment removed for export] *)
Definition dirsD : list bool := [false; false; true; false; false].  (* [comment removed for export] *)

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

(* [comment removed for export] *)
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

Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x17c14 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
intros. run_case dirsA resA carA.
Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x17c14 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
intros. run_case dirsB resB carB.
Qed.
End VP2.

Section VP3.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x17c14 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
intros. run_case dirsC resC carC.
Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x17c14 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof.
intros. run_case dirsD resD carD.
Qed.
End VP4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x17c14 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x17cc0) mem rom) (mkst regs' (Z_to_bv 64 0x17c14) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x46020, 4);
                          (Z_to_bv 64 0x46048, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x46048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x46020) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2PrintfBuf ()) ["VP5"] "h04mem'h15regs'h21Hh32H0h42H1h52H2h62H3h72PHh82R1h93R11h:2R2h;3canh<3memh=1oh>4regsh?3romh@2sphA1wp;1p;2p;4p;3p;5p;<g000Lj13Tg00TRj1<Tg002cj1PTg003Aj1VTg014;j2[Tg00V:j1TTg00QMj4YTg0011j11Tg01jJj2LTg01jmj3JTg01kPj2HTg004Aj20Tg004gj32Tg02HBj1ZTg00T2j2:Tg01DAR0j2STg01SJj5@Tg01TCj3OTg01=\j2NTg00^dj2XTg005[j2MTg01>]j2KTg007Qj1RTg01?Zj3ITg0081j1WTg00RJj17Tg00[>j4CTg00XFj2DTg003dj2GTg00W>j2FTg002Hj2BTg017Jj2>Tg02IOl<`Tg02JKl<_Tg02KGl<^Tg02LCl<]Tg00bij4\Tg01?:j3UTf0R1#3#3p=5%31#<p=;%<1#<p=E%31#3#3#3p==g00JZR2g00K8R3721p=Qf1R4=221p=4f2R5=224/S1p=8%<1#3p=AP5P2P4P1C\p=6f4R6f3R7AU5413Up=91B41,B5p=?g00KVR8#3R9#<R:#PR;%39R<#3R=#3R>#5#PR?#VR@'[RA%P=RB#VRC#T\@RDP6P5P4P1CYf6R5%18REg02;2RF1L;Ed5J;'H%;8#E#E#=#;#;#5#1,0?RG52@f7RH%19R9PF1L;9d5J;'H=2@6f8RI%<:#1RJPF1L;Jd5J;'H10?352@f5R3#Z%1<R<,:3R;#Q%<8RJ#1RF,4;98;998;E'SP01:5<R;#Q14;F98;998;Eg00\6R;p,2fxRKf=RL%;8#E#E#5#E#5#=#1,0?RMf<RNf;ROD@PKP4PGP1POD@3O1NL41X@2RPf:RQ,M?%A>#=#1R>'K,0?=6@>PP%58#;#A#5#=#A#=#1,0?RR=6@<RSPP%58#;#A#=#;#5#A#5#1,0?R8%1=56@R=PPf9RT,0?RU=6@9%RPRVD9D99IN1%WCRW#TRXP;P1PUg00]H#7#7RUCCPC%=J#1,0BPC%3:#1,0B%RCD9,DWRC32P;P1P8%7U#7R8#7#7#7#7RBCCRJ1GT9,0?,FB,DW52XP;P1PRP8CC%1:,0?,F8,DW52XR8'B3?3?X0D,>DX1A,>AP11:H<R:#QPKPNPOPQPTPIPHP5P1P3P6P7M<`W3P1O114:F98:998:EP01:I<R:/4E14:F98:9PKf?R:PMf>R7PLD@PKP4PGP1PLD@5O;1N:4PP1M?N/K>,0?=6@>PPPSPPP=PP10?OR6=6@9PVD9D99I71P;P1P6PUCC=2XC1GO9,0?,FB,DW92XJ/B83?3?X0D,>DX1A,>AP11:T<R6/4EPKP7PLPNPOPQPTPIP1PHP5P3M<_W4P1O1146F9869P01:Q<R0/49140FPKfAR0PMf@RMP:D@PKP4PGP1P:D@5O;1N04PP1M?7/K>,0?=6@>PPPSPPP=PP10?LRP=6@9PVD9D99IM1P;P1PPPUCC=2XC1GL9,0?,FB,DW92XJ/B83?3?X0D,>DX1A,>AP11:O<R</49PKPMP:P7PLPNPOPQP1PTPIPHM<^W5P1O114<FPKPMP:P7PLPNPOPQP1PTPIPHM<]W6P1O1n200100001021000010000W2P1O1n200100001021000011000W2P1O1n200100001021000011000b=W9W:W8W7X;2XA2X@@X?DW<W>o"). Qed.
End VP5.

