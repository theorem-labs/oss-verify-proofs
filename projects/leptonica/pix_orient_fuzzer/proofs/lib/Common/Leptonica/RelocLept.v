(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec StepTac StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocLept () := "C47Corelib7Classes?RelationClasses9ReflexiveI47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib6Common9Leptonica9RelocLept?wr_readable_chkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC47Corelib4Init9Datatypes5implbC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common9Leptonica8WalksLib;wr_readableC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00i69OSSVerify5KrLib6Common9Leptonica9RelocLept9RelocLept00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLeptArl_wr_readable_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLeptEwr_readable_chk_soundC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLept;rl_pages_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLept9pages_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_rw_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib6Common9Leptonica9RelocLept:strs_checkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLept7str_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib6PArith6BinPos3Pos3eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6PArith6BinPos3Pos6eqb_eqC56Stdlib6ZArith6BinInt1Z6eqb_eqc69OSSVerify5KrLib6Common9Leptonica9RelocLept7str_okbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8WalksLib9rostr_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9rostr_winC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLept7str_okPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib6Common9Leptonica9RelocLept6str_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common5Reloc5Reloc:rl_delta_uC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4xorbC47Corelib4Init9Datatypes4negbC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9lxor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z9ldiff_0_lC56Stdlib6ZArith6BinInt1Z@ldiff_ones_r_lowC56Stdlib6ZArith6BinInt1ZAsub_nocarry_ldiffK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op204C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions7Z_to_bvc69OSSVerify5KrLib6Common9Leptonica9RelocLept;lxor_ones64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc4rl_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_xoriC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica9RelocLept;spans_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorc69OSSVerify5KrLib6Common9Leptonica9RelocLept8span_okbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib6Common9Leptonica9RelocLept6span_PC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01".      (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition wr_readable_chk (segs : list Segment) : bool :=
  forallb (fun seg => implb (seg_writable seg) (seg_readable seg)) segs.

Lemma wr_readable_chk_sound : forall segs, wr_readable_chk segs = true -> wr_readable segs.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "h01Hh13segh21xh33Hinh42Hwh51bh65lemmah74segsp;1p;3p;2p;6p-1p10000p4p710p9g000\j1=Tg001<j1<Tg002Kj34Tg002bj13Tg003dj12Tg004fj21Tg005Ej35Tg005aj28Tg006:j37Tg006kj36Tg007Nj69Tg007jj1:Tg0094j3;Tg009NR0f0R1g009nR23;p=0g00:NR3#=%<1#0f2R49431f1R5#3#0%31%21'1X13R6f4R7553#0f5R89431P6P5O1#0R9[^23R:'8A5368#0f69431P9[^23;71W6A6367f3R6O2P:P1P6P4O2%36%26'1#0P0%37%28,11#0X50P1P2P4E9%27,12#0P1b0b0b0W4W3X13%:5eW0W7o"). Qed.

Definition pages_chk {RL : Reloc} : bool :=
  (2^16 <=? rl_img_lo) && (rl_img_lo <=? rl_rw_lo) && (rl_rw_lo + 4096 <=? rl_img_hi) && (rl_img_hi <=? 2^32).

Class RelocLept (RL : Reloc) := {
  rl_wr_readable_ok : wr_readable_chk rl_segs = true;
  rl_pages_ok : pages_chk = true;
  (* [comment removed for export] *)
  rl_clr_extra : list (Z * Z)
}.

Lemma rl_wr_readable : forall {RL : Reloc} {RLP : RelocLept RL}, wr_readable rl_segs.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "h02RLh13RLPp;1p;2g00;Mj13Tg00<Xj12Tg00=Wj20Tg00>hj21Tg00@=f0R0#3f1R1#21010'1W1W0o"). Qed.

Lemma rl_pages : forall {RL : Reloc} {RLP : RelocLept RL},
  2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo + 4096 <= rl_img_hi /\ rl_img_hi <= 2^32.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "h01Hh12H1h22H2h32H3h42H4h51mh61nh72RLh83RLPp;1p;2p;3p;4g00;Mj1FTg00A<j2ETg00BGj1CTg00CPj1;Tg00D5j1=Tg00DSj2@Tg00E0j10Tg00F1j24Tg00FNj11Tg00GNj26Tg00Gkj13Tg00Hlj3?Tg00IOR0j2:Tg00Ijj22Tg00JFj2DTg00Jfj4>Tg0094j3ATg00KAj2BTg009NR1f0R2g009nR33Ap=5%;2#;p=<f2R4f1R5/42'Bp=81452=A13p=71245/:2p=9g00@=%F21E52%C5#5g00K_#;R3#=R1%;3#<R3#='@R6%04R7'4%14R8787%;3R3#;#<#<#<#=R7,68%34R838R9%=3,@1R1,48R8;?2%59%58':P0f3R8#0R9,46%18R37891637%38R338#51731f4R3#0R9%13R:16:7%33R:12:139599596P2f5R9#0R:,46%19R;78:16;7%3938#5f6R9#3/71f7R;#0R:,46%1;R<78:R:16<7%3;'4R;;?5%5:%5;':P0f8R;#0R:,46%1;R<78:#516<7%3;'7f9R;#0R<%1;R:16:7%3;R;12;13959<596P2f:R<#0R;,46%1<78;#5f;R;#1/67%3;'7f<R;#0R:,46R=%1;,4:R:;?5%5=%5:':P0f=R:#0R=,76%1:,7=f>R=#0R:%1=R;16;7%3=R=12=13959:596P2f?#0,76f@R:#0%1:'7g00LDR:P017521245[R012521745R=[1284\=1D52P5n2001000000120000000X5:W6R=P0^5:^6:R:P2P6fB#0R0P4O31260P=P:P2fDR0#0R;%10R0P8O312;0P=P:P2fFR0#1/67R;%30R0P<O312;0P=P:P2fH#3R:P1fAO312:1fIR:#0R=,26%1:R6,2=R=1667%3:R:'2R612:1R:':R1':P9P=P1P3P6P:P4P2C>C>C>b4b0b3b0b2b0b1b0W2W1P5P2O2n2001000000121000000b0W3W0P5P2O2n2001000000121000000b0W4W0P5P2O2n2001000000121000000b0b0W8W7o"). Qed.

(* [comment removed for export] *)
Section Strs.
Context {RL : Reloc}.

Definition str_okP (a k : Z) : Prop :=
  rostr_chk rl_segs a k = true /\ 0 <= k <= 200 /\ rl_img_lo <= a /\ a + SSP.rostr_win a k <= rl_rw_lo.

Definition str_okb (e : positive * Z * Z) : bool :=
  let '(b, c, k) := e in
  let a := c + rl_delta b in
  rostr_chk rl_segs a k && (0 <=? k) && (k <=? 200) && (rl_img_lo <=? a) && (a + SSP.rostr_win a k <=? rl_rw_lo)
  && (a + 216 <=? rl_rw_lo).        (* [comment removed for export] *)

Definition strs_check (tbl : list (positive * Z * Z)) : bool := forallb str_okb tbl.

Definition str_eqb (e1 e2 : positive * Z * Z) : bool :=
  let '(b1, c1, k1) := e1 in let '(b2, c2, k2) := e2 in Pos.eqb b1 b2 && Z.eqb c1 c2 && Z.eqb k1 k2.

Lemma str_fact : forall tbl, strs_check tbl = true -> forall b c k,
  existsb (str_eqb (b, c, k)) tbl = true -> str_okP (c + rl_delta b) k.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) ["Strs"] "p'0h03Hokh11Hh21xi001xh33Hinh42Heh51mh61nh71pi011ph81Ah92H2h:2H3h;2H4h<2H5h=2Hbh>2Hch?3Hexh@2HkhA2b'hB2c'hC1fhD2k'hE1lhF1qhG2H1hH2H6hI1bhJ1chK1khL5lemmahM3tblhN1zi021zp;2p;1p;3p;4p;7g00LbR0j2TTg000\j1XTg00MBj1bTg00NLj1Wj2ATg00OSR1j3PTg00OoR2j2KTg00PIj3]Tg002Kj38Tg00Plj2?Tg00QKj2<Tg00KAj2HTg00Hlj3CTg0094j36Tg00Qhj2cTg00RJj2aTg005Ej3STg00RjR3j1RTg005aj2`Tg006:j3_Tg006kj3^Tg00<Xj1\Tg00T1j39Tg00U9j1JTg00CPj1@Tg00D5j1QTg00F1j22Tg00E0j1ZTg00U^j2FTg00FNj1YTg00GNj2DTg00Ijj27Tg00JFj2dTg00IOR4j2GTg00Jfj4LTg00Vjj2VTg007Nj7NTg00X1j4OTg00XQj2UTg009NR5f0R6g009nR736p=0f3R8g00LDR9g00YQR:P9f2R;f1R<COP6COp=3A88;<A6567'Gp=>1U;<,D8/V6p=5P;P9P<P6COp=[A6567,G<p=B1H<6=657p=;1U<6,D;p=1g00Z6R=/26p=41H;</H6p==1D;</26p=IA98;</H6p=E12<6=657p=:1F<6,D;p=M1T:9R7/T9R>#X%b6#0P7P;P<P6C3R?#Wf4R@5P>#0P1p4p710R1P5\6R5%X<RAP4AP;<6#0P@P6P;P8P6O1C>X28,K8[RBP8P6P<P;P6O1C>X2;,K;AP8;<#0RC[f5RDP6P8P@P6O1C>X2@,K@\CA];<6P<n2001000000120000000WEWCW8PB^EA^C5^81P6P>P7P@P8P;C3#Wf6R1P<O4P>P6f7R5P7PDP@P8C3RA/A6C>X2>,K>P2P>P>P6f8R2P7P1PDP@C3RB/A6C>X2>PDp,2RLRCP1P@C5P6P0P7P9P>P6f;REP7f9RFP2P5C3/A6C>PFPCf:RGP2C5[P6P0P:P9P>A[7<6R0f?RHP7f=RIf<RJPEC3/A0C>PIPCf>R0PJC5[^N9P6P>P?fBRKP7f@RLPHP0C3/A?C>P4P7P8P;P<C3R?fCR058>P7fARMPLPHC3/A?#0PMPCPKPLC5P6fERL98>AP7fDRAP0PKC3/AB#01?L51<A1RB'HR?1<0DRD;C6%0?/BDP4fFRD/?21<L5';%0BPDPCfGRBPLC5P6fH/?G1<BFR5';%05fJR5/?JR?fI/<ERE;C<%0?/BEP4fKRE/?I#01<5J#0PEPCfLP5C5P6fMR5/?H#01<5H#0P41?<6#0A6:;<[R5A6:<61?;<#0RE[A6:8;\E1c<6P<n2001000000120000000XF:X7:P5^F:^7:P6fPR5PKP;O3A6:5KP41<<6#0A69;<[R5A69<61<;<#0RK[A698;\K1a<6P<n2001000000120000000X59X69RKP5^59^69R5P6fQREP0P8O3A69E0PKP5P6fRR5PAPGO3A695AP:fUR5P7P6PBPDC3fXRA58>fVRGPCfWRKP5C5]3XA:P7P5PDPLC3=8>KP9P5P7PKP6PBC3fYRL58>PKPCPAPGC5]3XB9P7PGP5PDC3=8>AP9P5P7PAPKP6C3fZRE58>PAPCPLPKC5]3XD9P7PKPGP5C3=8>LAS>3E#0f[R598>6%R<#0RG[^2>R0'`AS>35#0f\RJ98>6PG[^2>;_6WLA^>3EPLO2P0P6P7PLPAPKC3RKP<O2%RK#0%\CRKA1LCER0;9A%4Ag00K_#J#@R3#@#J#@#@#@#QRG,2A3=%ZCRI/201F0A%YCRA5I03=R?%J3#J#@#@#@#QR3=I0AR0;C6%0?/B0P4PKA1EC5R0PL%4LCE12LG12I03=1F0L=I0A';1D03/:AP5PCPJPEC5P6PKf]RE91JCRJP5%45CE125G12IJ3=1FJ5=IJA';f^RJ91EC/D3/:APKf_R391JCR5PE%4ECE12EG12I53=R01F5E=I5AR5;C<%00/B5P4f`R5913CR0=9KJ%4J12JG3=12I0';AM00J/:AP5PCfaR0P3C5P6fbR3910CRJ=9K5%45125G3=12IJ';fcRJ913CR5?M50/:AfdR591JCR0=9K3%43123G3=R312I0R0;C<%03/B0P4PKfeR0915CR3PJ%4JCE12JG';1:I3P0PCffR3P5C5P6PKfgR5913CP0%40CE120G';fhR0915C,:IPKfiR3910CP5%45CERJ125GR5;C<%0J/B5P4fjR5913C=9K0%40';1:0GP5PCfkR0P3C5P6flR3910C=9K5%45';1:0GfmR0fnR571C=9K3RJ%43R3;C<%0J/B3P4foR3915C=9K0#0%40#0P3PCfpR0P5C5P6fq910C=9K3#0%40#0P41:<617;<[R417<61:;<R0[178;\01d<6P<n2001000000120000000X59X69R0P4^59^69R4P6P=frR3P<O317=3P0P4P6ftR3PGP2O3173GP0P4P6PIfwfxR371CR2PHO317I2P0P4P6fyR4fzR071CR2?M23R2PAPDO3172Af{910CR0=9K4#017=4R=174GRG'GRK17I0RIAM004/7ARA'GRC'GPFPKPCP=PGP1P@CLPIPAP;P6CLCLCL1V04eb<b1b;b1b:b1b9b1W9WGP<P6O2n2001000000121000000b0W:W0P<P6O2n2001000000121000000b0W;W0P<P6O2n2001000000121000000b0W<W0P<P6O2n2001000000121000000b0WHW0P<P6O2n2001000000121000000b0b0b0W3PBP;P6FNW3PBP8P6FNW3PBP@PMFNb@b1b>b1b=b1W>W=P<P6O2n2001000000121000000b4W@W4P<P6O2n2001000000121000000b4W4W3P<P6O2n2001000000121000000W1XD9XB9XA:P<P6O2n2001101000121101102X77P<P6O2n2001101000121101102X2>P<P6O2n2001000000121100000b?b1W?XK9XJ9XI:W0WMo"). Qed.

Definition str_at (b : positive) (c : Z) (e : positive * Z * Z) : bool := let '(b', c', _) := e in Pos.eqb b b' && Z.eqb c c'.

Lemma str_far_fact : forall tbl, strs_check tbl = true -> forall b c,
  existsb (str_at b c) tbl = true -> c + rl_delta b + 216 <= rl_rw_lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) ["Strs"] "p'0h01xi001xh11Hh23Hinh33Hokh41mh51nh61pi011ph71Ah82H6h92Hbh:2Hch;2Heh<3Hexh=2b'h>2c'h?1fh@1lhA1qhB2_HhC1bhD1chE2k'hF5lemmahG3tblhH1zi021zp;2p;1p;3p;7p;4g00LbR0j2MTg000\j1QTg00MBj1ZTg00ZTj2Pj39Tg00OSR1j3DTg00OoR2j2>Tg00PIj3WTg00U9j1@Tg00CPj16Tg00D5j1FTg00FNj1]Tg002Kj34Tg00Plj2=Tg00QKj2;Tg00Hlj3LTg0094j32Tg00Qhj2YTg00RJj2XTg005Ej3ITg00RjR3j1HTg005aj2VTg006:j3UTg006kj3TTg00<Xj1STg00T1j3ETg00F1j21Tg00E0j1RTg00U^j2ATg00GNj23Tg00XQj2?Tg00Ijj2<Tg00JFj2\Tg007Nj7JTg00IOR4j2NTg00X1j4CTg00KAj2OTg009NR5f0R6g009nR732p=0f3R8f2R9f1R:34A2567'Np=8f4R;1?89'3/3:/<6p=7P9g00LDR<P:P6CCp=[P8P<g00YQR=P<P9P:CCP6CCp=5A2567,N:p=K1?:6,39p=B1O9:/O6p=:139:/36p=G1M=<R7/M<R>#Q%Z6#01P:6=D>8#0P1p4p710R1P5\6R5%Q:R?P4AD9:6#0P;P6P9P8P6O1C8X08,>8[R@P8P6P:P9P6O1C8X09,>9AD89:#0RA[f5RBP6P8P;P6O1C8X0;,>;\AAW9:6P:n2001000000120000000W@W?W7P@^@?^?5^71P6P>1P89PBP:O4P>P6f6R1A9;86C8X0>,>>P2P>P>P6f7R2A9B;6C8X0>P;p,2RLR5PBg00K_#@#6R?#@#@#6#6#6#FR@%]5RAD7P6P0P7P<P>P6f:RCf8RD?926C8PDP5f9P@PAD7[P6P0P=P<P>A[7:6R0f>REf<RFf;;90C8PFP5f=RFP@PAD7[^H<P6P>P7P9P:P6C5R0fARGf?RH?9E0C8P4P7P8P9P:C5R0fBRI54>f@RJ?9H0#0PJP5PGP@PAD7P6P7PBP;P8C5fDR054>fCRKP7P1PBP;C579I#01=02R;1;K1R1;L6%0;/K1P4fER1/=D#01;02#0P1P5fFP@PAD7P6fGR0/=C#01;0C#0P41=:6#0A2=9:[R0A2=:61=9:#0R2[A2=89\21Y:6P:n2001000000120000000XA=X6=P0^A=^6=P6fJR0PFP9O3A2=0FP41;:6#0A2<9:[R0A2<:61;9:#0RF[A2<89\F1X:6P:n2001000000120000000X4<X5<P0^4<^5<P6fKR0PEP8O3A2<0EP=fMR0P7P6PJPHC5fPRF54>fNR2P5fORDP@PAD7]2X==P7P0PHPEC5=4>DP<P0P7PDP6PJC5fQRE54>PDP5PFP@PAD7]2X><P7P2P0PHC5=4>FAI>3E#0fRRH94>6%H:#0R0[^0>R2'VAI>3H#0fSR;94>6P0[^0>;U6WFAT>3EPFO2P2P6P7PFPDPGC5RGP:O2%HG#0%S5RGABF5ERF;EIg00Z6RD/1I%6?#@#6#6#6#FR?,1I3:%R5R2/1F1AFI,3F/1A3:RI13F@/1ARF;L6%0I/KFP4ABE5HRE=EGK11DK11K?3:112E1AEK,3E/1A3:#013E@/1A#0PHP5P;P@PAD7P6fTRH9B;5R;=EG111D1111?3:112;1A;1,3;/1A3:#0fU,?5=GH@/1A#0P411:6#01<9:[R41<:6119:#0RH[1<89\H1\:6P:n2001000000120000000X4<X5<P4^4<^5<P6fVfW,?5;G@R@PAP:O31<@AP6b8b1W8WBP:P6O2n2001000000120000000b3b3b3W2PJP:P6FJW2PJP9PCFJb:b1b9b1W:W9P:P6O2n2001000000121000000b;W;W2P:P6O2n2001000000121000000W1XE<X><X==P:P6O2n2001101000121101102X67P:P6O2n2001101000121101102X0>P:P6O2n2001000000121100000b<b1W<XD<XC=W3WGo"). Qed.

(* [comment removed for export] *)
Lemma str_span : forall a k, str_okP a k -> 0 <= k <= 200 /\ rl_img_lo <= a /\ a + k + 1 <= rl_rw_lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) ["Strs"] "h01Hh12H0h22H1h32H2h42H3h57__arithh64__ffh78__varmaph85__with91qh:1rh;2H4h<4__p1h=6__sat0h>6__sat1h?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE2H5hF2H6hG2HahH2HkhI2HwhJ2_HhK6__sat2hL1ahM1kp;2p;1p;3p;4p;6p;7p;8g00Vjj2tTg00<Xj1sTg00T1j3YTg00U9j1VTg00CPj1;Tg00D5j1UTg00Ijj21Tg00E0j1aTg00U^j2=Tg00FNj1]Tg00IOR0j24Tg00GNj20Tg00[Zj2PTg00\Kj29Tg00\hj2Sj3lTg00]Ij1dTg00]bj2?Tg00^?j25Tg00^_j2Nj3kTg00_Fj23Tg00_bj2MTg00`Ij2LTg00`oj2KTg00aUj1`Tg000\j1_Tg00b5j1^Tg00bSj1\Tg00c1j1[Tg00c\j2GTg00d?j4ATg00djj6ZTg00eNj2rTg00f0j2qTg00fJj2pTg00g6j3oTg00gUj4nTg00hGj2XTg00i8j1>Tg00iWj2HTg00j@j3RTg00jij2jTg00kUj3iTg00l5j2OTg00lSj4ITg00m1j1hTg00mSj6gTg00n7j2@Tg00nZj3BTg00o=j3WTg00o`j3fTg010Cj2eTg0094j3TTg010`j7mTg011Dj7cTg011hj8bTg009NR1f0R2g009nR33Tp=Jg00Z6R4f1R5'1/42p=8f4R6f3R7'1f2R8/05/12'4p=61142p=21152,48p=C1085/12p=Qg00LDR9?T24p=FAT952p=:P5g012LR:g012kR;P;g013KR<P2g013kFmp=7P8P:P;P;P<P5P2Fcp=EP7P:P;P;P<P8P5P2Gbp=<P9P5g014KP2CAp=D1t52P0p,2RLR=#sR>?Y85#Jg00K_R?#VR@#;RA#;#V#;#;#;#URB,15,85%a=RCP8P81=85%]=R=D6'4%28RD?C8BPCP71078%U?REP=D6'4P2AY>67#J116B,86R>PCf5RFPF1=F6P=D6'4P0%2FRG?CFBRHPCf6RIPI1=IFP=D611IB,8IPCf7RJ10JIPEP=D6'4P211JB,8JPCf9RKPKf8RL,=KP=D6P0f:RM,1C1=MK=QM=11MB,8MPCf;RN10NMPEP=D6'4P2f<RO,1Cf=RP1=PO;Q=f>RO/0PRP%;?RQ#;RR#;#URS1PPS%2P%2SRTf@RUf?RV'0RW/9SRX#2[[10VORV/SS%FSRO#dRY1?SX15WS'0,:W[1NWS134SRXfARZ/0UR[/5SR\#2R]13\S'4[1M[S13S4R\fBR^/0ZR_/5SR`,3S?C`4[1L_SfCRa/0^R^/9SRb#F\O1K^SfDRc/0aRa/5SRd/:a\O19aSP9fERe/0cRc/5SRfP9g0152Rg#`Rh%_gRi%^9Rj%\9Rk%[9RlP:P;P;P<P91G9SRmg015^Rn1G94RoCA,7lEZRp1rl<RqP2P81q131p28#JdAo945CnR3b6b7b8g016E\OR1P2b5b:b9b4b3b2b1b0b=3l19PS,?S15PS'0,:P1XVS%2VP]\T[1PWS%2WR]19_SRP#2\T[1S[S1?SP/0`,:_\Y1N_S15^SRP13PS'8\X1M^S13Sd?Cd4\\1LaS19cS#F\O1KcSfFRr/0eRs/5S/:s\O19sSRtP9fGRu/0rRr/5SRvP9PhPiPjPkP9Pog016bRwPmCA,7lRxPqP3b6b7b8PXP2b5b:b9b;b4b3b2b1b=b>9kVS15VSRV13VS'81XWS%2`\T\]1P[S%2[%2b\T[1S_S1?Sb/0P,:^\Y1N^S13dS,8d\X1MaS13Sf?Cf4\\1LcS%Ft\O1KsS1:vr\O19rSP9fH/0u/5SP9P0%22132SfIR0110B'8PCfJRu10u0PEP=D6'4PK137Sp-0RKg017IRu#>#>#>#>R0#>Rr#>,H91H9r1H901H9u5R95R95R9g017h'j=ighPiP9P91O96P81O9ICIP5P91O9FP7PjCICIPkPlPlPx%h;RxPlP:P;P;P<PLEgP91@9ARAPwPmCA,7l5ElC<PxPlPlPpPxP91@9@R@1@9?R?5B9RpPn%VQ,@9Rn9W9m=B9ACA,7lC<PxPlAW9nm=B9m=f9@9B9@1@9RRR'D,7lPxPl1@9Q/D@,7lR@PxPl1Do?,7l1G9B,D?,7l5ElR?Px1G9E9B9p/DR,7l9El@9El?C<C<C<C<C<PqP3b6b7b8X?9X@9XA9XB9XC9XD9W<13IS,4J\X10681?SI/0J':\11?IS/0S/e6=Q6F116FPIPJ10JFPEPLD6,4H\>[[[[^?9^@9^A9^B9^C9^D9^<KP2PGPFPIP=fNPCfMPMPNPUPZPeO<b5WFX1DP5P2O2n2001000000121000000b:b9bEb;b4b3b2b>bKb1b0WIWGP5P2O2n2001000000121000000W0WHP5P2O2n2001000000121000000W0WJP5P2O2n2001000000121000000W0XM9XL9o"). Qed.

(* [comment removed for export] *)
Lemma rostr_win_bd : forall a k, k + 1 <= SSP.rostr_win a k <= k + 8.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) ["Strs"] "h02H0h17__arithh24__ffh38__varmaph45__with52H1h62H2h72H3h82H4h96__sat1h:4__x1h;4__x2h<4__x3h=4__x4h>1qh?1rh@1HhA2H5hB2H6hC6__sat0hD6__sat2hE1ahF1kp;2p;1p;4p;6p;3p;7p;8g00GNj20Tg00CPj1ETg00D5j1MTg00aUj1XTg000\j1lTg00b5j1`Tg00bSj1\Tg00c1j1ZTg00c\j2BTg00d?j4:Tg00djj6WTg00eNj2UTg00f0j2kTg00fJj2iTg0094j3CTg00g6j3_Tg00gUj4^Tg00\hj3[j2JTg00\Kj29Tg00]bj28Tg00^?j23Tg00hGj2LTg00[Zj2KTg00]Ij1YTg00^_j2Ij3VTg00_Fj22Tg00IOR0j25Tg00_bj2HTg00Ijj24Tg00`Ij2GTg00`oj2PTg010Cj2FTg00i8j1@Tg00iWj2>Tg00j@j3?Tg00jij2TTg018Tj1jTg0192j2hTg019Sj3cTg00kUj3NTg00l5j2QTg00lSj4OTg00m1j1bTg00n7j2=Tg00U9j1aTg00nZj3;Tg00o=j3RTg00o`j3]Tg00U^j2dTg010`j7eTg011Dj7fTg011hj8gTf1R1g012LR2g012kR3P3g013KR4f0R5g013kFep=6g00LDR6g00Z6R77C5p=AAC615p=71475p=1P6P1g014KP5C:p=Df2R8P2P3P3P4P1P5Ffp=Sf3R9P2P3P3P4P8P1P5Ggp=<1015R:g00K_R;#ER<#ER=#E#MR>g0152R?#XR@%l?RA%`6RB%\6RC%Z6RDP2P3P3P4P61B6>R2g015^RE1B67RFC:,6DEWRG1UD4R4P5P8g009NRHg009nRI'k1i58=CHIdA_671C^RIb2b3b4%A>RHg016E[RJP5b13[19:>,8>13:>'0,7:1081R:1L:>%1:%1>RKf4RL/09RM/3>#1[[1098RN/K>%1NROf5RP/0LRQ/9>RR#1\K[1JM>%YHRS18>R13Q>RR'0,7Q[1IQ>127>RTf6RU/0PRV/3>RW#112W>'5[1HV>12>7RXf7RY/0URZ/3>R[,2>14[7'5[1GZ>f8R\/0YRY/9>#A\H1PY>f9R]/0\R\/3>/7\\H19\>R^P6f:R_/0]R`/3>RaP6P@PAPBPCP6PFg016bRbP2C:,6DRcP4PIb2b3b4PTP5b1b?b>b8b7b6b5b0bCb97V>13:>R:#112:>'51LN>%1R\K\O1KM>%1M19V>RM#1\K[1JQ>18>M/0W,7V\S1IV>%1[12[>'5\T1HZ>13Y>RZ,2>14Z7'5\X1GY>%A^\H1P\>17a`\H19`>P6f;R`/0_/3>P6P0%15125>f<R0%M;RH'0188>/0>f='FRa'4100>,4a'5P]%18129>g017IR]#@Ra#@R0,>61>6aRa1>6]R]5?65?6g017hR\'T%@0,>6%j;,h6=c6a=?6]5?6/T\=N?@5N?PAP6P61Q6LP8PBCOP11Q69COPCPDPDPc%b3R31=6=R=,DF,6DP6P=PbP2C:,6D5SDC<P3PDPDPGP3P6%a;,=6RG1=6;R;5;6PE1=6<R<9R62=;6=C:,6DC<P31B6H9;6;AR6<2=;62=]6GRG'D,6DA;6;2,DG,6D5SDC<C<P4PIb2b3b4X:6X;6X<6X=6%1L12L>'5\T10L818>9/0P'7\J108H189>/0>/FLRL'4108>,4L'5[[^:6^;6^<6^=6P5PPfAPUf@P_P`O6b1WBW0P1P5O2n2001000000121000000b?b>bAb8b7b6b5b9bDb0b@105H1d15R1'4105>,41'5eXF6XE6o"). Qed.
End Strs.

(* [comment removed for export] *)
Ltac rl_str_tac tbl ok :=
  lazymatch goal with
  | |- _ (?c + @rl_delta ?RL ?b) ?k => exact (@str_fact RL tbl ok b c k (@eq_refl bool true))
  end.

(* [comment removed for export] *)
Ltac rl_dbounds_rec l :=
  lazymatch l with
  | nil => idtac
  | cons (@rl_delta ?RL ?b) ?t => let h := fresh "Hdbd" in pose proof (@rl_delta_bd RL b) as h; rl_dbounds_rec t
  end.
(* [comment removed for export] *)
Ltac rl_dbounds l := rl_dbounds_rec l; rl_chains l.

(* [comment removed for export] *)
Lemma rl_cell_val : forall {RL : Reloc} n b c, 2^16 <= c < 2^63 ->
  word_to_le_bytes n (rl (rl_delta b) c) = Z_to_le_bytes n (c + rl_delta b).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "h02Hch12RLh21bh31ch41nh51zp;1p;2p;3p;4p;6g00CPj10Tg00D5j13Tg00DSj24Tg00Ijj2;Tg00U9j11Tg00_Fj2ATg00IOj2<Tg00XQj25Tg00GNj26Tg01:<j17Tg01:Zj1:Tg000\j19Tg01;=j22Tg0094j38Tg00f0j2CTg01<:j2BTg01=4j2@Tg01=^j4=Tg01>`j6>Tg01?>j2?Tg00@=g01@Fg00YQg00LDR0g00K_R1#0R2#3R3%02#0R2#0R4#3'4f0R5';%11#1#1#1#1#3,43,A5'<P0f1R3f4R1f2R6'5R7'6R8%72#:#9R21215f5f3R9'5,66,2138X501298R8,C2%04#0#71B73R7'@P1P6P3P5C=E>1?97=828eW0W3W2W4W1o"). Qed.

(* [comment removed for export] *)
Ltac rl_zval := gres; pin; imm_norm; rewrite ?rl_unfold; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
Ltac rl_bare_in H :=
  repeat match type of H with
         | context [(?c + @rl_delta ?RL ?b)%Z] =>
             let z := eval vm_compute in (c + @rl_delta RL b)%Z in
             change (c + @rl_delta RL b)%Z with z in H
         end.
Ltac rl_bare :=
  repeat match goal with
         | |- context [(?c + @rl_delta ?RL ?b)%Z] =>
             let z := eval vm_compute in (c + @rl_delta RL b)%Z in
             change (c + @rl_delta RL b)%Z with z
         end.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall p, 0 <= p < 2^64 -> Z.lxor p (2^64 - 1) = 2^64 - 1 - p.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "p'0h04__x1h11Hh22H0h37__arithh46__sat0h56__sat1h61bi001bh74__ffh88__varmaph95__with:2Hph;1ph<1si011sh=2Hah>3Hneh?4__x2h@4__x3hA1ahB1ei021ehC2H1hD2HbhE3HgehF3HlthG2HnhH1ni031nhI1zi041gi051lp;1p;2p;3p;4p;6p;7p;8g00CPj1:Tg00D5j1STg00DSj2ITg00_Fj20Tg00IOR0j28Tg01@ej1jTg01ACj2BTg01Abj2LTg0094j3ATg01B@j22Tg01Baj2?Tg01C?j1;Tg00KAj26Tg01C]j2yTg01DDj2HTg01D`R1j2MTg00f0j2GTg01E@j2iTg01Ehj3dTg00aUj1cTg000\j1`Tg00l5j2OTg00bSj1^Tg00c1j1]Tg00n7j2KTg00c\j2JTg00m1j1\Tg00eNj2[Tg00fJj2ZTg00g6j3YTg00gUj4XTg01FLj3WTg01>`j6@j7UTg01G3j2VTg00]Ij1>Tg00Ijj2CTg01GSj1xTg01H3j17Tg01HQj3wTg00d?j4=Tg01:<j1vTg01I7j3uTg00i8j1FTg00iWj2NTg00j@j3RTg00jij2pTg00kUj3hTg00lSj4fTg00U9j1gTg01IZj4eTg01JCj3kTg01Jkj3lTg01KOj3mTg01L2j3nTg010Cj2oTg01LUj1bTg01M8j4aTg01Mbj3qTg010`j7rTg011Dj7sTg011hj8tTg00djj6_Tg00Z6R2f0R3'Cp=1g009NR4f1R5;A3p=91023p=<g00LDR6P5g016bP3C=p=EP5g012LR7g012kR8P8g013KR9P3g013kFrp=3P6P5g014KP3C=p=Df2R:P7P8P8P9P5P3Fsp=Qf3R;P7P8P8P9P:P5P3Gtp=4AA632p=5g01NMR<9A43p=PP5P7P8P8P9P3E_p=T%13R7g00K_R=#:R>#SR?%:>#:#:#:#:R@#SRA'IRB,03RC'8RDP6%jARE/B5RF1L:E=A63XI61L5EP412;5RG12E5RH'?f4RI,BE/2:,93X64P4%;G,6H12I:12E:'?/93X641y5A105A1H5A'MP110:ARH1H:Af5RG/2;RJ12E;RK'?%;J,6K'9P310;AP4g009nRKf7RJ/2GRL/?3%;L,63'9X64RMf6RN/2IROP4P41?3K%;3RP,6K'9P3%;K,6K,G4%;<RQ,6K,G4n0110000020000b612EIRR1i?ARS%<?%1ART%<BRU[[RV%1?RWg01NmRXAd?A5UW=RY%1B\X^=WRWP0f8RX#1RZ10XBR[%1JR\10JA'8PJf:R]#1R^f;R_/0BR`g0152Ra#cRb%`aRc1O65Rd%^6Re%]6Rf1K6=Rg1J6ARh'E,3fRi%\8R8Pf1J62Rj/Dg,3fRkP8AQfkiC4C41[f9R9P3P:1G4K1Z3:=A4KdAY625CXRKb7b8b9X06103ARl%15Rm%1:/8H[[^06P3P_PJP]O3b3W2W1P5P3O2n2001000000120000000b4b59WAIE@WFP3O11H;ARHP4P<PM1VN2%5NRM%>M'MP1%5JRM%>M12XN#PP3%5XRMP6P2f9Rn,25#P^:DX;61C22/8URU%xXW:PnP3PXFUWBP3O1%>MPnPJPSPVPYPWP0%1_P`f<RM#1RoP]f=Rp#1f>Rq/0BPbPcPdPePfPkP8PkC4P9PKb7b8b9X06RrPm\7^06RsP3f@P:O2b3W2W1P5P3O2n2001000000120000000b4b5%<5RtP01I?5,0:%7;/0:[Ru%7:/051I?:,0;Rv[%7I/0;\vAw:53P5n2001000000120000000UX66XA6RvPu\t^66^A6RtP3P]PAPSPVPYPWP0Po10MBRu%<pP_%1qRqf?Rw/0BRxPbPcPdPePfP6Pgg015^RyPjC=,3f,TfP8PfPkP81Ejg,3fC4C4P9PKb7b8b9X06Rk%53g016ERz[%<:\m[^06RmP3fAR{PXP:O3b3W2W1P5P3O2n2001000000120000000b4b5PSPVPYPWP0PoPu10pBP_PbPcPdPePf1J6?%v@5u6,Eg,3fR@P8P@C4P9PKb7b8b9X06R@105B\C^06RCP3P{P5O2b3X2xX1qP5P3O2n2001000000120000000b4b5O4b1%7n/0APSPVPYPWP0PoPu%7p/0_P_g017IRp#F#FRu#F#F,N61N6u1N6p5R65R6g017h'p=habPcP61O6:P51O6;CfPePfPiP8PfP6%g=,K6R=PyPjC=,3f,TfP8PfP61K6>R>g01OIRyPhC=,3fP8Pf1Dj=,3fP81Eg>,3fC4C4C4C4P9PKb7b8b9X06X?6X@6%5;R>Pz[%1G10IG[\H[\l^06^?6^@6P3P{Pw%7{PJPXP_P:O7b3XCxX2qP5P3O2n2001000000121000000b4b5b1CeW>P3O1n200110100021010211103b<%POP4P<1?3<16<P'9X6416<Q,G4PLP3E@bDPRPSPVPYPWP0PZP[1CAJ,8TPJPbPcPdPePfP6PgPyPhC=,3fP81Djh,3f1Dhg,3f5QfC4P9PKb7b8b9X061H3A1CA5,8T[^06P3P_PJO2b3X2`X1^P5P3O2n2001000000120000000b4b59kAIE@WEP3O1n200110100021110511104b<1BE;/25AlE;5E@1L;E/25Am;E5E@XG7XH67nF1oE51V52%55RF%>F'MP1%5:R1%>11B;E#5P3P6P21B5E#5^:DX;6%bEX:UPIP3P;FUXB>P3O1%>>PIPAPSPVPYPWP0%1N10NBP\PG10nBPrPsP3P_P:O2b3W2X1ZP5P3O2n2001000000120000000b4b5PvPtP3PGPAPSPVPYPWP0P\10JBRJ%<XPN%1nRn10]BR]PkPmP3PMPXP:O3b3W2W1P5P3O2n2001000000120000000b4b5PSPVPYPWP0P\PJP[PNP@PCP3PMP5O2b3X2]X1nP5P3O2n2001000000120000000b4b5O4b1CaW>P3O1n200110100021010211103b<9qE5E@W:X;6o"). Qed.

Lemma rl_not : forall d c, 0 <= c + d < 2^64 -> v_xori (rl d c) (-1) = Z_to_bv 64 (2^64 - 1 - (c + d)).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) [] "h01zh11Hh21ch31dp;2p;1p;3p;6g00GNj24Tg00Ijj2ETg00CPj10Tg00D5j12Tg00DSj2DTg00_Fj2>Tg00IOj2<Tg01:<j1;Tg01:Zj1:Tg018Tj19Tg01P0j28Tg01Abj26Tg01PVj21Tg010Cj25Tg0094j33Tg00f0j2CTg01Q<j2=Tg01>`j67Tg01<:j2?Tg01=4j2@Tg01RGj3ATg01SCj2BTg00LDR0g00Z6f0R1f1R2'4R3'Eg00K_R4#0R5#2%05#0#0#0#0R5#2'DR6,>3'<P0f2R3,42R7%;5R5#:R8%94R9,85,61,15%24,56R6f3,43'5,15R433X00P01567R:1151=384X00115:R:,C816761=71E71?32R7,@5AA321E71B79=38:eW1X20W3o"). Qed.

(* [comment removed for export] *)
Ltac rl_condZ :=
  pin; rewrite ?rl_not by lia; rewrite ?rl_unfold;
  rewrite ?c_ltu_Z by lia; rewrite ?c_lts_Z by lia; rewrite ?c_eq_Zm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ];
  rewrite ?Z.mod_small by lia; lia.

(* [comment removed for export] *)
Ltac rl_pgbounds := let h := fresh "Hpgbd" in pose proof rl_pages as h.

(* [comment removed for export] *)
Ltac rl_lay := rl_pgbounds; rl_dbounds (dA_1e360 :: dA_1e3b0 :: dA_1e3b8 :: dA_1f3f8 :: dA_1f430 :: dA_2f6b0s :: dA_2f6b0 :: dA_2f848 :: dF_1365c :: dF_13660 :: dF_13694 :: dF_13730 :: dF_15a00 :: dF_15b38 :: dF_15b3c :: dF_1c9b4 :: dF_1cdb8 :: nil).

(* [comment removed for export] *)
Ltac rl_exact t :=
  first [ exact t
        | rewrite ?Z.add_0_r; exact t
        | let H := fresh "RLX" in
          pose proof t as H; rewrite ?rl_unfold in H; rewrite ?rl_unfold; rewrite ?Z.add_0_r in H; rewrite ?Z.add_0_r; exact H ].

(* [comment removed for export] *)
Section Spans.
Context {RL : Reloc}.
Definition span_P (e : bool * positive * Z * Z) : Prop :=
  let '(rw, b, c, n) := e in
  if rw then rl_rw_lo <= c + rl_delta b /\ c + rl_delta b + n <= rl_img_hi
  else rl_img_lo <= c + rl_delta b /\ c + rl_delta b + n <= rl_rw_lo.
Definition span_okb (e : bool * positive * Z * Z) : bool :=
  let '(rw, b, c, n) := e in
  if rw then (rl_rw_lo <=? c + rl_delta b) && (c + rl_delta b + n <=? rl_img_hi)
  else (rl_img_lo <=? c + rl_delta b) && (c + rl_delta b + n <=? rl_rw_lo).
Definition spans_check (tbl : list (bool * positive * Z * Z)) : bool := forallb span_okb tbl.
Lemma span_fact : forall tbl, spans_check tbl = true -> forall i e, nth_error tbl i = Some e -> span_P e.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocLept ()) ["Spans"] "p'0h03Hokh12Hih21Hh32H1h42H2h51nh61zi001zh71mh81pi011ph91xh:1bi021bh;1ch<1eh=1ih>5lemmah?2rwi032rwh@3tblp;2p;1p;3p;5p;4g00LbR0j2ATg000\j1RTg01T>j1MTg01UIj1QTg01Ukj38Tg005Ej3DTg002Kj3CTg01VIR1j19Tg005aj2ITg006:j3GTg006kj3FTg01WQj5PTg01X2j1>Tg00FNj1NTg00F1j22Tg00GNj25Tg00Gkj1LTg00KAj2<Tg00E0j1KTg00Ijj20Tg00IOR2j2;Tg00X1j4:Tg00Hlj3BTg00JFj2JTg00Jfj4ETg0094j3?Tg01Y8j2HTg00XQj2OTg009NR3f0R4g009nR53?p=1f3R6f2R7f1R8/H43?p=7P7g00LDR9P8P4C:p=@f4R:P9P6P9P7P8C:P4C:p=6P3g00YQR;P8P4C:p==1O84,57p=31284=?35p=41A3;R</A9R=/A9R>#R%M4#1g01@F%Q>R?A8>68P>P4C7AD>1:#1f5R@9C>4%98#1RA[^9>RB'IAD>1@#1f6RC9C>4PA[^9>;G4W>AF>1:P6O2PBP4P7P>P@P6P7P8DPO2%97#1P0P=P9%94#1P?f8RB=8>CP>P8C7%>7]1]0P6P0P<P9A@=84#9#1P?f<R1f:RA58>P>A@=78C7A@=67#>]1]0^69P4P0P3P;P=P<P7P8P4D6#9#1P?f@f>R058>P>P=P<P6P7P8D6C7P=P<P:P6P7D6#>]1]0^69^69P4P=P<1=67P8P4D6#9#1P?fCRDfA58>P>P=P<1=:6P7P8D6C7P3P3P3P4p,2RLRE#NRFA3:E@RG'215G6RH%LERI'2'<%KERJ/2G12HF'<n0110300020000#1P?fFfD58>P>P=P<1=8CP@P:D6C7P3p-0P7f7RH93CERG,0F15G@RK/0I';10JG10KF';n0110300020000]1]0P@A36E:RL,2F15L7RM/2I'<#1P?fE=8>DRDP>P=P<P3P;P5P@C:P:P6D6C7A3@ECR5,2FRN155:RO/2IRP;B8%1N%1P';P214FG14KIA3HEBRH,0F15HCRC/0I';P4f9RP93BERN,4FA3PEA/5BRB/4IP214841078[RP10841478RA[1067\A1J84P8n2001000000120000000X79X59RAPP^79^59RPP4PFf;?3E1RQP7O310FQPAPPP4f=RR?3E0/51R1PIP6O3101If?930ERE,0F15ERRR/0IP7P4CEb4b2b3b2W4W3P8P4O2n2001000000120000000b0W1W012JL12MF'<#1P?PDP>P=P<P3P;g01NMP@C:P:P6D6C712J5R512OFRO;B8%15%1O';P214JG14KF10JH10CF';P414JN14BFPAPPP4PJPQP7O310JQPAPPP4P1PFP6O3101F10JE10RFP7P4CEb4b2b3b2W4W3P8P4O2n2001000000120000000b0W1W0n0110200020101P8P4O2P=P<1=@:P6P7D6#>eW1W0X59X;9X:;X?3P8P4O2n2001101000121102101X8<P8P4O2n2001101000121101100X8=P8P4O2n2001101000121101100P4P7O2b0b0W1X<>W=W0W@o"). Qed.
End Spans.

(* [comment removed for export] *)
Ltac rl_jr_fix :=
  repeat match goal with
         | H : ret_ok (rl ?d ?c) |- context [v_jalr (rl ?d ?c) ?e] =>
             replace (v_jalr (rl d c) e) with (rl d c) by (symmetry; exact H)
         end.
