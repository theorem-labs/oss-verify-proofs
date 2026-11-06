(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim
  DrainSim StoreOk Footprint SymExec StepTac ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SymTac () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec7regs_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymTac7pins_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymTac7sr_pinsC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec4ridxC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec6sr_updC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec;regs_ok_pinC13~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec6edenotC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec4expr00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec3envC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8v_addi_0C13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_lwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec8b_lw_valC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec;alu32_add_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec9low32_litC13~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecDbv_swrap_add_idemp_rC13~~~C56Stdlib6NArith6BinNat1N2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions?bv_wrap_bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecDbv_swrap_add_idemp_lC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec>bv_swrap_wrap'C13~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec>low32_unsignedC13~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec?sext32_unsignedC13~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z6inj_leI47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymTac8v_addi_ZC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec5saddr01C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec6a_baseC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec6bdenotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec5a_offC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec6adenotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec=u_Z_to_bv64_0C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SymExec5sbase01C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ExitSim7to_exit00C13~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ExitSim7to_exit02C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim:msteps_indC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim5to_wr00C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim5to_wr02C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim7lh_nextC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim<msteps_transC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg9rz_mstepsC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim:mmap_modelC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim?mmap_model_lazyC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
  end.

(* [comment removed for export] *)
Definition pins_ok (E : env) (regs : bvmap 5 word) (ps : list (reg * expr))
  : Prop :=
  Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps.

Lemma regs_ok_pins : forall E ps sr regs,
  regs_ok E sr regs -> pins_ok E regs ps -> regs_ok E (sr_pins ps sr) regs.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "p'0h01Hh11pi001ph24regsh32srh42Hhh52Hth62e0h71li011lh82H0h93Heqh:2Hph;2Hrh<2psh=1Eh>2IHh?1ah@1ei021ehA3ps'hB1rhC4resti031bi041xp;1p;2p;3p;6p;7p;5p;4p-1R0g0000R1p4p710p8P0g000QR2p4p710p8P0P2p4p7210p8g000nj14Tg001Sj1NTg0028j1=Tg002Vj1<Tg0039R0j2MTg003YR3j1ATg0049j2ITg004ej30Tg005oj35Tg0078j28Tg008Aj1BTg008aj37TP2j3;Tg009Aj3:Tg009^j31Tg00:8j6LTg00:Tj2KTP1j39Tg00;3j6>Tg00;Pj1GTg00<Wj3FTg00=`j7ETg00>nj6?Tg00?Lj2DTg00?fj5HTg00@Hj4@Tg00@hj2CTg00B0j2JTf4R2f3R4g00C9R5f2R6f1R7C@f0R837p=21C461J78512p=3P6P5P7P8C@p=6g00DBg00EH#4R9#N#=R:#<R;/M5R<#AR=P<%A5R>%49#4#4#4#4#=#<R9,I:R:A0278f5R??574f6R@1824RA;06[[]2]3X<=A0478%B<RB9527P7W:W;X2:X3>P0P;P5A0@78f7R0?574f8RC?0A6[[^2:^3>A0078A7<?2RD95C7f9REA7<@?RF/84;06[[^2:^3>[^7=P8A0E78f:RG?574f;RH?0A6[[^2:^3>A0G78P<P;P@P?P2D295H7P1P<P9P4A;;58R1f=RAA:;58RID3X1<P<P;PEPCP0D2RJ91=7f?RKP<P;PGPEPCD2/8@;0?RL[P8P<P;P0P@P?D2RM91=BP<P;PCP0P@D2RN91=BP=PBP3P<p-0P8g00Emg00FIRBn10110100020020000000X6=g00FfPJP8ELPB1KL8b8W0P8O1W0P9PCA;;57RLfBRBA:;57ROD3P9PGP1fDRPPID3X1<=9<7A7<46P<P;PKf>RQPAD251=A7<24P<P;f@RAPKPQD251=P=P=P3P<P=P8P?P8n10110100020020100101X6=PDP<P;fARDPAPKD2P8E>A1=2KP=P<P3P<P<P8P0P7n10110100020020100101X6=PFA6;BDRD=7<AP7E>A1<@DfCRD=6;B91<0P8A6;PD91<CP<fER0=6;PA1=EPR@P9PBPLfLRLPOD3P9PPP1fNROPID3X1<RA=9<HP<P;fIRHfHRFfGR3D2/80=0OPRK]5]4[X1<A1=CDP8P@P=P0P9PDA6;F3R@9;;5fMA:;5@D3P9P0P1fOR1PID3X1<=9<7P<P;fJPHPFD2fFRI'8=010]5]4X7=P9PBA6;3IR39;;5PLA:;53D3A9<AIPI%GH=F0FPPPOP0PPPHPFPDP7FEP8O4PKeW5W4PGP8E?b8W0PEP8E?b0W9P8O1b0P8O1b0W9P8P6P7O3W0W5W4XA=X1<P4P6P7P8O4n200210100000020041104101000000A1=8N18J?=0Q2[X7=PMO1P81D=NO1b0W:W;X2:X3>W>XC=X@5XB;P7P8O2n2001100000121103102X?<P8DHW<W=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alu64_add_0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01bh11xp;1p;2p;3p;6g000nj10Tg0028j19Tg002Vj12Tg00GBj21Tg00Ghj28Tg009^j37Tg00I1j13Tg00J=j34Tg00Jej25Tg00>nj66Tg00EH#0#0#0#0#0#0#9R0#2R1P1f0R2g00L0,10R0'8f19712X01%32g00LN?4201520E6W1o"). Qed.

(* [comment removed for export] *)
Lemma aluw_add_0 : forall x : word,
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01bh11xp;1p;2p;3p;6g000nj10Tg0028j18Tg002Vj13Tg00GBj22Tg00M:j11Tg00Mbj37Tg00NJj36Tg00O5j1<Tg009^j35Tg00P=j1;Tg00QHj19Tg00>nj64Tg00RVj1:Tg00EH#0#0#0#0#0R0#0#8R1#3R2%80R0#3R3g00L0R4,20R5g00LNR6f1R7#1f0R8379601%<7R7552X03P3%18R9A6018=527X03%;8A7695%99E41214#1%:4E4W1o"). Qed.

(* [comment removed for export] *)
Lemma aluw_addi_lit : forall (a : word) (k : Z),
  sext 64 (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k))) = v_addiw a k.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh57__arithh64__ffh78__varmaph85__with91ah:1kp;1p;3p;2p;4p;7p;8p;6p;<g000nj17Tg0028j1ATg002Vj16Tg009^j39Tg00Sbj20Tg00TLj3VTg00M:j1;Tg00GBj2:Tg00Mbj3>Tg00NJj3ETg00U0j2CTg00V;j22Tg00Vbj21j1XTg00WHj24Tg00?Lj28Tg00Wej3WTg00Y=R0j2UTg00YYj1?Tg00Z7R1j2TTg008Aj1LTg003Yj1KTg00ZSj1ITg00[1j1HTg00[Oj1GTg00\:j2=Tg00\]j4FTg00]Hj7JTg00]lj2DTg00^Nj2NTg00_:j3OTg00_Yj4PTg00`Kj4QTg00a6j4RTg00adj3BTg00c<j2STg00dNj2<Tg00e=j1@Tg00fOj3^Tg00g4j3]Tg00gbj8\Tg00h?j1[Tg00>nj6ZTg00iRl<YTg00j7R2f1R3f0R439p=3P2f4R5f3R6f2R7P3P4EZp=5g00jUR8P2P0g00k3P1g00kQf5P5P6P7P3P4M<Yp=Mg00EH#7#7#7#7#7R1#7R0#AR9#6%64R:%63R;g00l1%67?93410671063'3R<[10731074'3%66?973[R=%65?967\<AV734P4n2001000000120000000W2W1X38P=^2;^1:^38P4P9%A1R8g00LNR:%;7R;1:93R=#;R<3>R57E9R>1C73R?1085,28R@,191096RA/47,28RB,:9,09,34X021097RC/43,28RD,19%;61:97#;R65>:,08,28,19/34X02P2P2%X9R:P:P@PDP2\2/8:108;R:108<R@'4,181284/3BX02118CRE1086,44,18,28/3BX02109=R6,18118ARF/44,18,28/3BX021193RG1184,4F,18,28/3BX02118GRG,4ERE,28RF134BX02RH14CG,28PH1183RI14A4,28/3BX02PDPH182D14CI,28AW8C3D5PGP8P9P31U89%?1R1%?0R0'TRIP8P11821P9P01820EMg00lLRH#L%KH%I2%H2%G2RHg00m8g00mWRBPBg00n7RBP21=21g00nW1=20CFg00o>FJ1DHBP4P7g00o^RBg010>RH'81N47=9BHdg00L0=O23CPb6b7b8PIP4b5CQCRD5PFAB8CGD5118E,281S8ED5P61<93D5P@%@=D5P:%@7D5A^8;<,08A]8;<D5G\1:9D,091<9DD5109>R>%[5D5109?,3>eO4b4X:2W9o"). Qed.

(* [comment removed for export] *)
Lemma bdenot_var : forall E n, bdenot E (SBVar n) = E n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Eh11np;1p;2g000nj10Tg0028j13Tg002Vj12Tg00?Lj21Tg00DBg010^g00EH#0#0#0#0#0#0#3#2f1f0O1'1W1W0o"). Qed.

Lemma bdenot_lit : forall E, bdenot E SBLit = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Ep;1p;2g000nj10Tg0028j14Tg002Vj12Tg00GBj21Tg00?Lj23Tg00DBg00EH#0#0#0#0#0#0#4R0#2g00L0,10'3W0o"). Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Eh11zp;1p;2g000nj10Tg0028j14Tg002Vj12Tg00GBj21Tg00?Lj23Tg00DBg00j7g00EH#0#0#0#0#0#0#4R0#2f0,10'3W1W0o"). Qed.

Lemma edenot_var : forall E n, edenot E (EVar n) = E n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Eh11np;1p;2g000nj10Tg0028j13Tg002Vj12Tg00?Lj21Tg00DBg010^g00EH#0#0#0#0#0#0#3#2f1f0O1'1W1W0o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_Z : forall (x : word) (i : Z),
  v_addi x i = Z_to_bv 64 (bv_unsigned x + i).
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01ih11xp;1p;2g000nj10Tg0028j16Tg002Vj12Tg00Sbj21Tg00WHj25Tg00GBj24Tg00?Lj23Tg00EH#0#0#0#0#0#0#6R0#2R1g00j7f1,10f0'5,40,31W0W1o"). Qed.

Lemma adenot_var : forall E n k,
  adenot E (SA (SBVar n) k) = Z_to_bv 64 (bv_unsigned (E n) + k).
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Eh11kh21np;1p;2g000nj10Tg0028j16Tg002Vj12Tg00Sbj21Tg00WHj25Tg00GBj24Tg00?Lj23Tg00DBg010^g00j7g00EH#0#0#0#0#0#0#6R0#2f2f1O1,10f0'5,40'3W1W2W0o"). Qed.

Lemma adenot_lit : forall E k, adenot E (SA SBLit k) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP1"] "h01Eh11bh21kh31zp;1p;2p;3p;6g000nj10Tg0028j1?Tg002Vj18Tg00GBj21Tg00Sbj2>Tg00WHj25Tg009^j32Tg00?Lj27Tg00>nj63Tg011=j24Tg012Gj26Tg013Qj29Tg014[j1:Tg015dj2=Tg016mj1<Tg0185j2;Tg00DBg00j7R0g00EH#0#0#0#0#0#0#?R1#8R2g00L0R3,11R4,>1R5f0R6'5,11f1R7,11R89226X12P0P31567,11=228X301116R1,72P5g019>E314461646E3g01:N/96R6#:,=7%<6'4=221e1;76=221eW2W0o"). Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac sym_env_cbn :=
  cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
       a_base a_off e_addr e_width e_val].

Ltac sym_env_norm :=
  sym_env_cbn;
  rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
          ?edenot_lit, ?edenot_var, ?u_Z_to_bv64_0;
  sym_env_cbn;
  repeat match goal with
  | |- context [getr ?rs (Z_to_bv 5 ?z)] =>
      let u := eval vm_compute in z in
      let l := constr:(@BV 5 u ltac:(vm_compute; exact I)) in
      replace (Z_to_bv 5 z) with l by (apply bv_eq; vm_compute; reflexivity)
  end.

Section WithFP3.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP3.
Ltac sym_z_lit k :=
  lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac sym_z_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [Z_to_bv 64 (0 + ?k)] =>
      sym_z_lit k; replace (0 + k)%Z with k by lia
  | |- context [Z_to_bv 64 (?a - ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 - k2)%Z in
      replace (a - k1 + k2)%Z with (a - v)%Z by lia
  | |- context [Z_to_bv 64 (?a + ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 + k2)%Z in
      replace (a + k1 + k2)%Z with (a + v)%Z by lia
  | |- context [Z_to_bv 64 (?a + Zneg ?p)] =>
      replace (a + Zneg p)%Z with (a - Zpos p)%Z by lia
  end.

Ltac sym_addr_norm :=
  imm_norm; rewrite ?v_addi_Z; sym_env_norm; u_norm; sym_z_norm.

Section WithFP6.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP6.
Ltac sym_lit_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [wbytes ?m (Z_to_bv 64 ?z) ?bs] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  | |- context [word_to_le_bytes ?n (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  end.

Section WithFP7.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP7.
Ltac sym_norm :=
  cbn [edenot sr_get nth ridx s_regs s_pc s_log s_next branch_taken];
  rewrite ?alu64_add_0, ?aluw_add_0;
  rewrite ?aluw_addi_lit;
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra;
  rewrite ?v_add_lit, ?v_sub_lit;
  sym_addr_norm.

Section WithFP8.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP8.
Ltac sym_mem_norm :=
  cbn [mem_denot e_addr e_width e_val];
  sym_norm; sym_lit_norm.

Section WithFP9.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msteps_to_exit : forall segs code ms ms',
  msteps segs ms ms' -> to_exit segs code ms' -> to_exit segs code ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP9"] "h02msh11Hh23ms'h32Heh43Hmsh52Hph62Hsh72IHh84codeh93ms1h:3ms2h;4segsp;1p;3p;2p;7g003Yj1>Tg000nj10Tg0028j17Tg002Vj14Tg01;Xj33Tg01<bj31Tg01=nj1;Tg01>Pj16Tg01?Vj15Tg009^j32Tg01@8j18Tg01A@j29Tg01B<j2:Tg01CDj7=Tg01DPj7<Tg01E\#>g00EH#0#0#0#0#0#0#7#4R0g01F[R1f3R2f1R3f0R433f4R5f6R6f5R7;14f7R8f2R9716[X21X01A1754P4W1X01%;0%69%5032%81f8/921:1932f9R0?329f:R:?102f;R0?1:7[A10:5f<P0P8P6P5P2P3P4O1F=W3W7W4W6W5X:1X91X01P9P3P4F<W1X21W0W8W;o"). Qed.

Lemma msteps_to_wr : forall segs LH bs ms ms',
  msteps segs ms ms' ->
  StreamSim.to_wr segs LH bs ms' -> StreamSim.to_wr segs LH bs ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP9"] "h02msh11Hh23ms'h33Hmsh42Hph52Hsh62Hwh72IHh82LHh92bsh:3ms1h;3ms2h<4segsp;1p;3p;4p;2p;8p;7g003Yj16Tg000nj11Tg0028j13Tg002Vj12Tg01;Xj35Tg01Gbj40Tg01=nj1<Tg01>Pj1;Tg01?Vj1:Tg009^j34Tg01@8j17Tg01A@j28Tg01B<j29Tg01Hnj8>Tg01DPj7=Tg01E\#6g01F[R0p-0[g00EH#1#1#1R1#3#2#6f4R2f1R3f0R435f5R5f7R6f6R7P5P4C0f8P6P7f2R8C0[X20X00P7P5P2P4C0P4W1X00%11#1#1#3#2R1#<%;8%:134%70f9R1f3R9'8190834f:R:?598f;R;P:P1P9C0f<R1P;P:P5C0[P1P;P:P2C0f=P1P;P6P7P2P9P3P4O1G>W6W7W3W5W4X;0X:0X00P8P3P4F=W1X20X00W9W8W<o"). Qed.

(* [comment removed for export] *)
Lemma msteps_lh_next : forall segs LH ms ms',
  msteps segs ms ms' ->
  StreamSim.lh_next segs LH ms' -> StreamSim.lh_next segs LH ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP9"] "p'0h03ms'h12H0h21Hh32HLh42Hmh52LHh61mh72msh84segsi001xp;1p;3p;2p;6p;4g003Yj16Tg01;Xj30Tg01J:j32Tg00l1R0j21Tg01KFj65Tg01LTj44Tg01Loj43Tg01E\#6g01F[R1p-0[f3R2f1R3f0R430f4R5?223g01MIP1f6R6?024f5R7P4O1'1X01A2675P4f8R8?074f7P4O1'1P0f9R0?063P8P3O1f:R6?208P4f;R9?082P9P5O1P1f>f<R5;04f=R8P4O1'1X01P7A0897P5P7O1P8P9P6P7P0P3E5P4C4C3W3W4P3P4O2n2001000000120000000W1X61P3P4O2n2001000000120100000W1W2X01X71W5W8o"). Qed.

(* [comment removed for export] *)
End WithFP9.
Ltac sym_halted :=
  solve [ reflexivity
        | eassumption
        | (rewrite ?MmapSim.mmap_model_halted, ?MmapSim.munmap_model_halted;
           solve [ reflexivity | eassumption ])
        | (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].

Ltac sym_no_lazy :=
  cbn [cfg_model];
  repeat first
    [ rewrite MmapSim.mmap_model_lazy
    | apply MmapSim.munmap_model_no_lazy ];
  solve [ reflexivity | eassumption ].

Section WithFP10.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP10.
Ltac chain_mst :=
  first [ eapply CatSim.msteps_to_wexit
        | eapply MmapSim.msteps_twm
        | eapply MmapSim.msteps_twm_tail
        | eapply MmapSim.msteps_tmw
        | eapply StreamSim.msteps_to_rd
        | eapply msteps_to_wr
        | eapply WallSim.msteps_to_wall_tail
        | eapply WallSim.msteps_to_wallexit
        | eapply DrainSim.msteps_to_rd
        | eapply DrainSim.msteps_to_out
        | eapply msteps_to_exit
        | eapply msteps_lh_next
        | (eapply ShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
        | eapply msteps_trans ].

Section WithFP11.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma chain_mst_realizes : forall segs scfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs scfg (mkCfg ms' model) T ->
  ShapeAlg.realizes segs scfg (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP11"] "h02Hhh15Hlazyh23Hmsh32Hrh41Th55modelh62msh73ms'h84scfgh94segsp;1p;3p;2p;4p;:g003Yj13Tg000nj10Tg0028j15Tg002Vj14Tg01=nj1>Tg01Mcj1;Tg01?Vj1:Tg009^j31Tg0039j26Tg01NZj12Tg008Aj17Tg01;Xj38Tg01ORj29Tg01PGj4=Tg01QUl:<Tg01E\#3g01Rbg01F[R0g01S\g01TRg00EH#0#0#0#0#0#0#5#4R1#>f1R2#;%:1311611R1#3R3f2R4#2%71R131f7R5f5R6f4R738f8R8P51967f3R9C=f9P8P5f6P6P7P9P4%26=131eP2f0M:<W3W2W1W0W4W5X70W6W8W9o"). Qed.

(* [comment removed for export] *)
Lemma chain_mst_realizes_mmap : forall segs scfg ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs scfg (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  ShapeAlg.realizes segs scfg (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
ltac2:(KReplay.run1 (kr_t_SymTac ()) ["WithFP11"] "h02Hhh15Hlazyh23Hmsh32Hrh41Th51ah61lh75modelh82msh93ms'h:1nh;4scfgh<4segsp;1p;3p;2p;4p;6p;:g003Yj14Tg000nj10Tg0028j17Tg002Vj15Tg01=nj1ATg01Mcj1;Tg01?Vj1:Tg009^j31Tg0039j26Tg01NZj12Tg008Aj18Tg01;Xj39Tg01UZj33Tg01ORj2@Tg01PGj4?Tg01Vgj3>Tg00>nj6<Tg01QUl:=Tg01E\#4g01Rbg01F[R0g01S\g00EH#0#0#0#0#0#0#7#5R1g01TR%A1f3R2#;%:1311611R3#4R4f4R5#2%83R331f9R6f7R7f6R839f:R9P6f5R:?358,@7P2C?f;P9P6f8A38:7R6P5P2P4%27f0R2=143X64f2%26R6A>8:7E<A1463ef1P2M:=W3W2W1W0W4X:1W5W7X90W8W;W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP11.
Ltac sym_close :=
  first [ reflexivity
        | (f_equal; lia)
        | (apply bv_eq; u_norm; lia)
        | bveq ].

Ltac sym_regs H :=
  getr_resolve; regupd_resolve;
  rewrite <- ?getr_nz by reg_neq_tac;
  rewrite ?(H _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end;
  sym_norm.

Section WithFP13.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP13.
Ltac sym_reg H R r v tac :=
  assert (getr R r = v) by (sym_regs H; tac).

Section WithFP14.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP14.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @cons _ _ ?t => let n := list_len t in constr:(S n)
  end.

Section WithFP15.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP15.
Ltac sym_pc_Z :=
  lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] =>
      lazymatch p with
      | Z_to_bv 64 _ => idtac
      | _ => check_closed_term p;
             let u := vm_eval (bv_unsigned p) in
             replace p with (Z_to_bv 64 u) by bveq
      end
  end.

Section WithFP16.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP16.
Ltac sym_pc_lit :=
  try lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] => wlit p
  end.

Section WithFP17.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP17.
Ltac sym_sc_auto :=
  first [ reflexivity | (repeat split; lia) ].

Section WithFP18.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP18.
Ltac sym_pin_auto :=
  first
  [ reflexivity
  | multimatch goal with
    | H : regs_ok _ _ _ |- _ =>
        sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
    end ].

Section WithFP19.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP19.
Ltac sym_block segs fuel dirs rds ps pvals rvals R H :=
  sym_pc_Z;
  lazymatch goal with
  | |- context [ mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom ] =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    let Hms := fresh "Hms" in
    let Heq := fresh "Heq" in
    let Hlf := fresh "Hlf" in
    let msx := fresh "msx" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 (mkst regs (Z_to_bv 64 pc) mem rom));
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_sound segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (msx & Hms & (R & Heq & H & Hlf));
        clear Hsc Hst;
        chain_mst; [ exact Hms | ];
        rewrite Heq; clear Heq Hms msx;
        cbn [s_pc s_log]; try sym_mem_norm;
        norm_pc; sym_pc_lit ] ]
  end.

Section WithFP20.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP20.
Ltac sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms :=
  lazymatch ms with
  | mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 ms);
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_ex segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (R & H & Hms);
        clear Hsc Hst;
        cbn [s_pc s_regs s_log mem_denot] in Hms ] ]
  end.

Section WithFP21.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP21.
Ltac sym_chain Hms :=
  sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.
