(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_RGb2 () := "C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2InK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=ACONST_globalC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst=global_shadowC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BArr5u8arrI47Corelib4Init5Logic3and00K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Peano2ltC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv;rdn1_of_mrdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_KitBword_to_le_bytes_1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@adenot_of_estartK47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or02C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula05C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst8aglobalsc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb27FIVE_SHK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics5Riscv3Sem7mul_divK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5mulop01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@ASHADOW_BASE_valC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb23q64C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb24q8shK46Stdlib9micromega7EnvRing5PExpr04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC45stdpp9bitvector;definitions;bv_unsignedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?kimg_of_mem_invc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb27five_shC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv:kwr_of_stkC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstI47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC56Stdlib6ZArith6BinInt1Z3subC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7syms_idC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=syms_id_soundC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotK47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics5Riscv3Sem5alu64I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb23KB2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb2:CS_SM_RET2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_RGb2;HTLbARGb2_0C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib7Numbers7BinNums1N00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RGl7LH_HEADK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop06I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition CS_SM_RET2 : Z := 0x100790.
Definition FIVE_SH : Z := 0x80004520.
Definition KB2 : list reg := [1; 3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma five_sh : forall E M, ACONST M -> kentry_ok asegs E M (KWord (SA (ELit 0) FIVE_SH) 1 (ELit 0)).
Proof.
  intros E M HC.
  assert (HIn : In (0x62900, 8, 32) aglobals) by (unfold aglobals; repeat (solve [left; reflexivity] || right)).
  destruct (ACONST_global M 0x62900 8 32 HC HIn) as (HA0 & HA8 & HU).
  destruct HU as [B _]. cbn [kentry_ok].
  assert (HS : estart E (SA (ELit 0) FIVE_SH) = 0x80004520) by (vm_compute; reflexivity).
  split; [lia|]. split; [unfold flat; rewrite HS; lia|].
  rewrite (adenot_of_estart E _ 0x80004520 HS ltac:(lia)).
  cbn [edenot]. rewrite word_to_le_bytes_1 by lia.
  destruct B as (_ & _ & B). specialize (B 0%nat ltac:(vm_compute; lia)).
  assert (HN : nth_error (global_shadow 8 32) 0 = Some (Z_to_bv 8 0)) by (vm_compute; reflexivity).
  rewrite HN in B.
  replace (Z_to_bv 64 0x80004520) with (Z_to_bv 64 (sh 0x62900 + Z.of_nat 0)) by (f_equal; vm_compute; reflexivity).
  apply rdn1_of_mrd. exact B.
Qed.

Lemma q64 : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 -> mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_RGb2 ()) [] "h02H0h14__x1h24__x2h34__x3h46__sat6h51Hh62H3h72H4h82H5h92Hah:7__arithh;4__ffh<8__varmaph=5__with>1qh?1rh@6__sat7hA6__sat4hB6__sat8hC6__sat9hD2H1hE2H2hF6__sat3hG6__sat5hH1bhI2ffp;1p;2p;3p;4p;6p;8p;5p;7g002Mj1;Tg001oj1ITg001Jj1<Tg00O6j2UTg00OSj21Tg009jj25Tg006Xj28Tg00?Mj1NTg00?kj1[Tg012Cj2FTg012`j2>Tg00W`j2?j1vTg0042j36Tg004cj2ETg013=j2kTg013^j1gTg00Ooj2RTg0147j2cTg014^j2aTg00I8j2TTg015Ej2]Tg015kj2\Tg00TMj2QTg00SAj2PTg00Sij3OTg00<6j1=Tg016Qj27Tg017:j1ZTg017Xj2YTg0189j3@Tg0032j1XTg00D\j1WTg018bj2MTg019@j4VTg00Jcj1yTg00KAj1xTg00Tnj2LTg019^j6wTg01:Bj1uTg01:dj2HTg01;Gj3qTg00V_j3pTg00Klj2oTg00LNj2jTg00M:j3iTg00MYj4hTg01;jj8fTg01<Gj4eTg00JEj1dTg00UQj3STg01=1j2JTg01=]j2bTg01>Fj3lTg01>oj5mTg00WBj6nTg01?fj3`Tg01@Oj2_Tg003Rj3^Tg00V4j4KTg00a9j7rTg01A;j8sTg00bhj7tTg00dbR0f0R1'Tp=3g00dDR2?610p=Af1R3=`21p=0g01A_,_1p=:g00nJR4?^31p=9P2P3g01BKP1CKp=GP3g00g_R5g00h>R6P6g00h^R7P1g00i>Frp=2f3R8P5P6P6P7f2R9P3P1Gsp=4P2P3g00g8P1CKp=DP2P3g011\P1CKp=BP9P5P6P6P7P3P1Ftp=C%31R:g00kMR;#;R<#IR=%<<#<#<#<R>#IR?'UR@,11'5%;<#;#;#;#;RA#IRB,83#A%NARA#[RC1F9BRD,>BRE,?A1?A896C1XHCP2PC%vARFPFPEP9PC\2/EF1k9BRF%ABRC#g1F8B,>B188B'R9628[RE1c8BRG110BRHf4RI/8BRJ#311JB'5[RJ1aIBRK11B0f5RL/8BRM,1B1TM0'5[RM1]LBRNf6RO/FB#A\CRP1\OBRQf7RR/8B=62R\CRS1FRBRTP2f8/8BRUP2PLg0116RV1Q0B'EPHeO1RH111B,5:R:1P=?RW110=RX%3?110@[RY[RZ%3=R[g010ZR\AO=?3UW9R?%3@\\^9[R]g00mkR^#=R_#=R`,72Ra172_R_172^R^'0'0#:%Z;,Y2Rb=@2aA@2b_/0^'0#:%X4Rc'9'9%W4R4P21M29P31M28CVRd%y2Re%x2RfPfPfP5P6P6P71L2BR51L20Rg'G,2fEw%u6R61H2<R<1H2;Rh9q25Ri%<;,H2R;5p2'G,2fC4RjP6Pf1G;g,2fR;P61Gi<,2fC4C41of7R7P1P9g00o6Rkg00oVRl'E1j19=6kldAi203ChRlb;b<b=X12X22X32g01C2\C1>B3/R89629[RC%A8Rk1>B9=628[[^12^22^32P1PIf=R9PLf:f;O5b:b4b@b0b?b>b8b7b6b0b5GfPAg01CO1?AB1?ADCePBPDPFPEPGPJPKPMPNPPPQPSPTP2PUP2PHP:PWPZP?P]1P=BRD%3BRL1U=BRm,10[Rn\XRoAO=B3V\X9[Rp%3m\\^9[R[P31Q0=,EVPXeRXO1PnPIPXO1PYPcP4%d2Pe1Dg5,2f1L2=R==S2ARA,B5,2f5CfP7Plb;b<b=11Bm,5LP1b:b4bAbFbAbGb4b0b?b>b8b7b6b0b5PFPEPGPJPKPMPNPPPQPSPTP2PUP2PHP:PWPZP?P]PDPoPpP[%=`R`#=RL,72R59@2b172`R`9@2b/0_'0Rb10^_#:'J1b2B=l2^RY,0a,0`,05#:/9c'9P4PdPePfPjP6PfP;P6Pf1Dg<,2f%N>9S2=,B<,2f5CfR<P61Dgh,2f1BhA,2f5CfC4C4C4P7Plb;b<b=X12X22X32%38Rh118@'5R@118m,5h[\k\C^12^22^32P1POf?PRf<P9f>O6R9b:b4b@bBbCb0b?b>b8b7b6b0b5PFPEPGPJPKPMPNPPPQPSPTP2PUP2PHP:PWPZP?P]PDPoPpP[10Y_#:,Jb%=L,72105`'0,0Y#:,J^/9c'9P4PdPePfPjP6PfP;P6PfP<P61Dgi,2f1BiA,2f5CfC4C4C4P7Plb;b<b=X12X22X321>B8RB#311Bm'5\@\k\C^12^22^32P9b:b4b@bBbCb0b?b>b8b7b6b0b5DmEnWEWDXI2o"). Qed.

Lemma q8sh : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 -> 8 * (ff / 64) + SHBASE = sh ff.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_RGb2 ()) [] "h02H0h12H7h22Hah34__x1h44__x2h54__x3h64__x4h74__x5h81Hh92H1h:3H10h;2H2h<2H3h=2H4h>2H5h?2H6h@2H8hA2H9hB7__arithhC4__ffhD7__sat11hE7__sat12hF8__varmaphG5__withH2ffhI1qhJ2q0hK1rhL2r0hM1zp;1p;2p;3p;4p;7p;6p;8g002Mj1<Tg001oj1DTg001Jj1ATg00O6j2jTg00OSj20Tg009jj29Tg006Xj21Tg012Cj28Tg012`j2;Tg00Ooj23Tg013=j2XTg013^j1UTg0147j2RTg014^j2QTg00I8j2JTg015Ej2VTg015kj2WTg00TMj2PTg004cj2ITg00SAj2aTg00Sij3`Tg00<6j1CTg016Qj2@Tg017:j1_Tg017Xj2^Tg0189j3HTg01=]j2]Tg01>Fj3\Tg01@Oj2OTg01=1j2[Tg0032j1ZTg003Rj3NTg00D\j1YTg018bj2STg00JEj1qTg019@j4MTg00Jcj1pTg00KAj1oTg00Tnj2FTg01:dj2BTg00V4j4GTg00bhj7nTg01:Bj1iTg01;Gj3KTg00V_j3ETg00Klj2gTg00LNj2fTg0042j3LTg00M:j3eTg00MYj4dTg00WBj6hTg0078j1cTg01?fj3kTg00a9j7lTg019^j6bTg01A;j8mTg00dbR0f0R1'Jp=:%A1#Ap=4%<1#<p=5g00dDR2?L10p==f1R3=L21p=2Ak231p=6P3g00g_R4g00h>R5P5g00h^R6P1g00i>Flp=7P2P3g01BKP1CGp=>P3P4P5P5P6P1Ebp=Tf3R7P4P5P5P6f2R8P3P1Gmp=?%:1R9g00kMR:#<R;#DR<%A;R=#A#4#DR>'jR?,01'9%<;R@#<RA#<#5#DRB,13#=P2%A:RC#4#4#4#4#4#4#4#<#5#5#5#5#5#5#5#DRD%DARA187BRE';/3D187A,31'2XM21X8B%=BRF#U1;BE117B'3,27[1R7B100BREf4RG/1BRH#:10HB'9[1QGB10B0f5RH/1BRI,0B1JI0'9[1VHBf6RI/8B#=\F1WIBf7RJ/1B/2J\F18JBP2f8RJ/1BP2f9/XA%=ARK#Uf:RL18LA,;A11LA'3'2[1RLA100ARLf;RM/1ARN#:10NA'9[1QMA10A0f<RN/1ARO,0A1JO0'9[1VNAf=RO/8A#=\K1WOAf>RP/1A/2P\K18PAP2f?/1AP2PHg0116RP1P0A'IPLeO1101A,99PO1P0B,IPPEeO1%:J10JB'91a<>100<%:>100?[[%:<RJg010ZREA`<>3UW2%:?\E^2Jg00nJRJg00mkRE#CR?#CR>#CR<#CRP#C,@2%_:,^2R91@2<R<5H21@2>R>1@2?R?1]2A1@2ERE5\2'6'6'6'6g01A_RL'O1@2PAH29>AH29?'6,6<'616E?/OL'[%ZJ5NJ3N%YJP2P21S2GP8%q2RJCMP3P21S2HP7PJCMCM%p2%o2RJPJP4P5P5P6P21F20R4g00g81B2=R=CG,7JP2P=g011\1F2ARLCG,7JFn%i5R5PJPJ1>L4,7J,TJP51B2CRC1B2;R;9K2L=E2='>,7JC?P5PJPJ1F2BR=/>4,7J,TJP51B2:R:9K2=1B2@R@5E2,>C,7JC?P5PJ1>@4,7JP5AK2L:1F2DR:5E2AE2:;'>,7JC?C?C?C?1gJ6P1P8g00o6RJg00oVR6'I1f18=LJ6dAe203CdbCbFbGX32X42X52X62X72%:G10GA'9g01C2R3\K1;A7/3I,2G[P3\F1;B7/3I,2H[%=I1;AG/3D13DH'2[[[[^32^42^52^62^72P1PHPNfEPIPOPGPMfBfCO9bBbDbEb0b1bLbJb:bAb@b1b?bKbIb>b=b<b0b8g01D;g01E9Eh188B,;Ag01F>'3%c8'2eW;W9XH2o"). Qed.

Lemma rg_zadd : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma rg_zmul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma rg_zk : forall a b k, a = b + k * 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b k H. subst a. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rg_br_ge : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof.
  intros a b Ha Hb. pose proof (br_lts_small a b Ha Hb) as H. cbn [branch_taken] in H |- *. rewrite H. reflexivity.
Qed.

Ltac rg_zeq H0 := first [ rewrite H0; reflexivity | f_equal; lia | apply (rg_zk _ _ (-1)); lia | reflexivity ].

Lemma rg_b2_a : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff sph D N lo : Z),
  1 <= N <= 3 -> 1 <= D -> D + N <= 2 ^ 47 ->
  ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 128 <= 2 ^ 47 ->
  (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
  sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
  wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 -> stk asegs m lo sph -> lo <= sph - 2592 -> ff + 128 <= lo ->
  mem_inv asegs m -> ACONST m ->
  exists R' M',
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592))
               (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CS_SM_RET2) fc None m ro)
      (MS R' F (Z_to_bv 64 LH_HEAD) fc None M' ro)
    /\ getr R' 19 = Z_to_bv 64 (D + (0)) /\ getr R' 15 = Z_to_bv 64 0 /\ getr R' 16 = Z_to_bv 64 (N)
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + (0)))
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 10 = Z_to_bv 64 ff /\ getr R' 13 = Z_to_bv 64 (sh ff) /\ getr R' 14 = Z_to_bv 64 ff
    /\ getr R' 1 = Z_to_bv 64 CS_SM_RET2 /\ getr R' 2 = Z_to_bv 64 (sph - 2592) /\ getr R' 3 = x3 /\ getr R' 4 = x4
    /\ getr R' 8 = Z_to_bv 64 (sph - 2528) /\ getr R' 9 = Z_to_bv 64 (sph - 2592) /\ getr R' 18 = Z_to_bv 64 N
    /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24 /\ getr R' 25 = x25 /\ getr R' 26 = x26 /\ getr R' 27 = x27
    /\ munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
    /\ stk asegs M' lo sph.
Proof.
  intros until lo. intros HN HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC.
  assert (HQ : ff = 64 * (ff / 64)) by (pose proof (Z.div_mod ff 64 ltac:(lia)); lia).
  assert (HSH : sh ff = 8 * (ff / 64) + SHBASE) by (rewrite q8sh by lia; reflexivity).
  pose proof HSH as HSHu. unfold SHBASE in HSHu.
  remember (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
  assert (S2 : getr R 2 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S8 : getr R 8 = Z_to_bv 64 (sph - 2528)) by (rewrite HR0; reflexivity).
  assert (S9 : getr R 9 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S10 : getr R 10 = Z_to_bv 64 ff) by (rewrite HR0; reflexivity).
  assert (S18 : getr R 18 = Z_to_bv 64 N) by (rewrite HR0; reflexivity).
  assert (S19 : getr R 19 = Z_to_bv 64 D) by (rewrite HR0; reflexivity).
  assert (S20 : getr R 20 = Z_to_bv 64 SHBASE) by (rewrite HR0; reflexivity).
  pose (E := Eseed R [Z_to_bv 64 sph; Z_to_bv 64 (ff / 64); Z_to_bv 64 D; Z_to_bv 64 N]).
  assert (E32 : bv_unsigned (edenot E (EVar 32)) = sph) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (EFF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 33))) = ff)
    by (evs; rewrite rg_zmul, <- HQ, u64_of_Z by lia; reflexivity).
  assert (ESH : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 33))) = 8 * (ff / 64))
    by (evs; rewrite rg_zmul, u64_of_Z by lia; reflexivity).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (8%bv, EAlu ALU_ADD (EVar 32) (ELit (-2528)));
                                     (9%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (10%bv, EMd M_MUL (ELit 64) (EVar 33));
                                     (18%bv, EVar 35); (19%bv, EVar 34); (20%bv, ELit SHBASE)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
      first [rewrite S2 | rewrite S8 | rewrite S9 | rewrite S10 | rewrite S18 | rewrite S19 | rewrite S20];
      evs; rewrite ?rg_zadd, ?rg_zmul, <- ?HQ; first [reflexivity | f_equal; lia]. }
  assert (HK : know_ok asegs E m
     [ KImg 0x10000 0x91000;
       KWr (SA (EMd M_MUL (ELit 64) (EVar 33)) 0) (ELit 128);
       KWr (SA (EMd M_MUL (ELit 8) (EVar 33)) SHBASE) (ELit 16);
       KWr (SA (EVar 32) (-2592)) (ELit 2592);
       KRange (EVar 32) (2 ^ 45) (2 ^ 47);
       KRange (EVar 33) 1 (2 ^ 41);
       KRange (EVar 34) 1 (2 ^ 47);
       KRange (EVar 35) 1 3 ]).
  { unfold know_ok.
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EFF; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite EFF; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ESH; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite ESH; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E32; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E32; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R CS_SM_RET2 m ro HR HK 120%nat [LH_HEAD] (SCR [] [] []) 36%N.
  { first [apply Forall_nil | split_scs].
    all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?rg_zmul, ?rg_zadd, ?rg_br_ge, ?u64_of_Z by lia;
      cbn [a_off a_base]; first [apply negb_false_iff, Z.ltb_lt; lia | lia]. }
  clear HK.
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  exists R', M1. split; [exact Hms|].
  rreg HR' 19%bv G19.
  rreg HR' 15%bv G15.
  rreg HR' 16%bv G16.
  rreg HR' 5%bv G5.
  rreg HR' 20%bv G20.
  rreg HR' 10%bv G10.
  rreg HR' 13%bv G13.
  rreg HR' 14%bv G14.
  rreg HR' 1%bv G1.
  rreg HR' 2%bv G2.
  rreg HR' 3%bv G3.
  rreg HR' 4%bv G4.
  rreg HR' 8%bv G8.
  rreg HR' 9%bv G9.
  rreg HR' 18%bv G18.
  rreg HR' 21%bv G21.
  rreg HR' 22%bv G22.
  rreg HR' 23%bv G23.
  rreg HR' 24%bv G24.
  rreg HR' 25%bv G25.
  rreg HR' 26%bv G26.
  rreg HR' 27%bv G27.
  split; [rewrite G19; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G15; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G16; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G5; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G20; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G10; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G13; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G14; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G1; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G2; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G3; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G4; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G8; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G9; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G18; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G21; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G22; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G23; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G24; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G25; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G26; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G27; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split.
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?EFF, ?ESH, ?E32;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil. }
  split; [subst M1; apply wmono_mem_denot|].
  split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  subst M1; apply stk_mem_denot; exact ST.
Qed.

Lemma rg_b2_b : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff sph D N lo : Z),
  4 <= N <= 8 -> 1 <= D -> D + N <= 2 ^ 47 ->
  ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 128 <= 2 ^ 47 ->
  (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
  sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
  wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 -> stk asegs m lo sph -> lo <= sph - 2592 -> ff + 128 <= lo ->
  mem_inv asegs m -> ACONST m ->
  exists R' M',
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592))
               (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CS_SM_RET2) fc None m ro)
      (MS R' F (Z_to_bv 64 LH_HEAD) fc None M' ro)
    /\ getr R' 19 = Z_to_bv 64 (D + (N - 4)) /\ getr R' 15 = Z_to_bv 64 0 /\ getr R' 16 = Z_to_bv 64 (4)
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + (N - 4)))
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 10 = Z_to_bv 64 ff /\ getr R' 13 = Z_to_bv 64 (sh ff) /\ getr R' 14 = Z_to_bv 64 ff
    /\ getr R' 1 = Z_to_bv 64 CS_SM_RET2 /\ getr R' 2 = Z_to_bv 64 (sph - 2592) /\ getr R' 3 = x3 /\ getr R' 4 = x4
    /\ getr R' 8 = Z_to_bv 64 (sph - 2528) /\ getr R' 9 = Z_to_bv 64 (sph - 2592) /\ getr R' 18 = Z_to_bv 64 N
    /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24 /\ getr R' 25 = x25 /\ getr R' 26 = x26 /\ getr R' 27 = x27
    /\ munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
    /\ stk asegs M' lo sph.
Proof.
  intros until lo. intros HN HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC.
  assert (HQ : ff = 64 * (ff / 64)) by (pose proof (Z.div_mod ff 64 ltac:(lia)); lia).
  assert (HSH : sh ff = 8 * (ff / 64) + SHBASE) by (rewrite q8sh by lia; reflexivity).
  pose proof HSH as HSHu. unfold SHBASE in HSHu.
  remember (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
  assert (S2 : getr R 2 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S8 : getr R 8 = Z_to_bv 64 (sph - 2528)) by (rewrite HR0; reflexivity).
  assert (S9 : getr R 9 = Z_to_bv 64 (sph - 2592)) by (rewrite HR0; reflexivity).
  assert (S10 : getr R 10 = Z_to_bv 64 ff) by (rewrite HR0; reflexivity).
  assert (S18 : getr R 18 = Z_to_bv 64 N) by (rewrite HR0; reflexivity).
  assert (S19 : getr R 19 = Z_to_bv 64 D) by (rewrite HR0; reflexivity).
  assert (S20 : getr R 20 = Z_to_bv 64 SHBASE) by (rewrite HR0; reflexivity).
  pose (E := Eseed R [Z_to_bv 64 sph; Z_to_bv 64 (ff / 64); Z_to_bv 64 D; Z_to_bv 64 N]).
  assert (E32 : bv_unsigned (edenot E (EVar 32)) = sph) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (EFF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 33))) = ff)
    by (evs; rewrite rg_zmul, <- HQ, u64_of_Z by lia; reflexivity).
  assert (ESH : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 33))) = 8 * (ff / 64))
    by (evs; rewrite rg_zmul, u64_of_Z by lia; reflexivity).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (8%bv, EAlu ALU_ADD (EVar 32) (ELit (-2528)));
                                     (9%bv, EAlu ALU_ADD (EVar 32) (ELit (-2592))); (10%bv, EMd M_MUL (ELit 64) (EVar 33));
                                     (18%bv, EVar 35); (19%bv, EVar 34); (20%bv, ELit SHBASE)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
      first [rewrite S2 | rewrite S8 | rewrite S9 | rewrite S10 | rewrite S18 | rewrite S19 | rewrite S20];
      evs; rewrite ?rg_zadd, ?rg_zmul, <- ?HQ; first [reflexivity | f_equal; lia]. }
  assert (HK : know_ok asegs E m
     [ KImg 0x10000 0x91000;
       KWr (SA (EMd M_MUL (ELit 64) (EVar 33)) 0) (ELit 128);
       KWr (SA (EMd M_MUL (ELit 8) (EVar 33)) SHBASE) (ELit 16);
       KWr (SA (EVar 32) (-2592)) (ELit 2592);
       KRange (EVar 32) (2 ^ 45) (2 ^ 47);
       KRange (EVar 33) 1 (2 ^ 41);
       KRange (EVar 34) 1 (2 ^ 47);
       KRange (EVar 35) 4 8 ]).
  { unfold know_ok.
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EFF; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite EFF; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ESH; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite ESH; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E32; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E32; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R CS_SM_RET2 m ro HR HK 120%nat [LH_HEAD] (SCR [] [] []) 36%N.
  { first [apply Forall_nil | split_scs].
    all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?rg_zmul, ?rg_zadd, ?rg_br_ge, ?u64_of_Z by lia;
      cbn [a_off a_base]; first [apply negb_false_iff, Z.ltb_lt; lia | lia]. }
  clear HK.
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  exists R', M1. split; [exact Hms|].
  rreg HR' 19%bv G19.
  rreg HR' 15%bv G15.
  rreg HR' 16%bv G16.
  rreg HR' 5%bv G5.
  rreg HR' 20%bv G20.
  rreg HR' 10%bv G10.
  rreg HR' 13%bv G13.
  rreg HR' 14%bv G14.
  rreg HR' 1%bv G1.
  rreg HR' 2%bv G2.
  rreg HR' 3%bv G3.
  rreg HR' 4%bv G4.
  rreg HR' 8%bv G8.
  rreg HR' 9%bv G9.
  rreg HR' 18%bv G18.
  rreg HR' 21%bv G21.
  rreg HR' 22%bv G22.
  rreg HR' 23%bv G23.
  rreg HR' 24%bv G24.
  rreg HR' 25%bv G25.
  rreg HR' 26%bv G26.
  rreg HR' 27%bv G27.
  split; [rewrite G19; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G15; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G16; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G5; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G20; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G10; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G13; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G14; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G1; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G2; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G3; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G4; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G8; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G9; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G18; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G21; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G22; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G23; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G24; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G25; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G26; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split; [rewrite G27; rewrite ?rg_zmul, ?rg_zadd; rg_zeq HR0|].
  split.
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?EFF, ?ESH, ?E32;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil. }
  split; [subst M1; apply wmono_mem_denot|].
  split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  subst M1; apply stk_mem_denot; exact ST.
Qed.
