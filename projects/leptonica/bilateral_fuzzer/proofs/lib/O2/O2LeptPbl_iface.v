(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoomBL LeptExecB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptBase O2LeptPixHdr O2LeptPixCreate O2LeptPixCopyT O2LeptBl_iface O2LeptBilCW3 O2LeptBilCW4 O2LeptBilGrayW.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2LeptPbl_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9Leptonica9LeptArith6wpl_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica:LeptRoomBL>RB_pixT_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica:LeptRoomBL7RB_pixTC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib6Common8Mallocng9AllocSure?alloc_margin_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2O2<O2LeptBilCW45RB_bcC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00c59OSSVerify5KrLib2O2?O2LeptPbl_iface<RB_bc_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib2O2?O2LeptPbl_iface6RB_pblC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition PBL_WIN : Z := 112 + 64 + 5120.
Definition PC_pixBilateral : Z := 184884.
Definition RK_pbl : Z := (3 * (RK_pix + RK_bg) + RK_pix)%Z.
Definition RB_pbl32 (w h : Z) : Z := (3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bg w h) + RB_pixT (4 * (wpl_of w 32 * h)))%Z.
Definition RB_pbl (w h d : Z) : Z := if (d =? 8)%Z then RB_bg w h else if (d =? 32)%Z then RB_pbl32 w h else 0%Z.

Lemma RB_bc_nonneg : forall w h, (0 <= h)%Z -> (0 <= RB_bc w h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptPbl_iface ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hah64__x2h74__x3h84__x4h94__x5h:4__x6h;1Hh<2H0h=2H1h>2H2h?2H3h@2HhhA6__sat4hB6__sat5hC1hhD1wp;1p;2p;3p;4p;7p;8g0000j15Tg000Uj13Tg0013j1CTg001Xj20Tg0025j21Tg002Rj2>Tg003Xj1FTg004gj1<Tg005oj1STg006Oj1PTg006oj1OTg007Mj1gTg007kj1dTg008Vj2LTg0099j2ZTg009[j2YTg00:5j2XTg00:aj3WTg00;;j3VTg00;Zj4UTg00<Lj2KTg00=Zj1ETg00>ej2ATg00?Aj2JTg00?jj1;Tg00@Ij2ITg00A5j2RTg00Aaj3HTg00BAj2BTg00B_j2@Tg00CBj1QTg00Cdj2TTg00DLj2NTg00Dhj2fTg00EEj3eTg00Eij2MTg00FRj3DTg00G;j4GTg00GYj1`Tg00H7j3_Tg00HZj2]Tg00ITj4\Tg00J?j7^Tg00Jcj3[Tg00KLj3aTg00Koj8bTg00LSj3cTg00M6R0f0R1'Ap=2%51#5p=6g00MTR2/L1p=8f2R3g00N2R4g00NQR5P5g00O1R6P2f1R7g00OQP1C\g00P8F^p=41J21p=:A[271p=9Aa271p==f3R8P4P5P5P6P3P7P1Gbp=7Ac271p=?%21R4g00PXR9#5R:#5R;#3R<%3:R=%C:R>#CR?#3'0R@,13%5;RA#3RB'>117@'0'0RC#F%<C#2%5?#3R?,18/>B113?'0,0<RC#F%<C#2f4RC/>B/08,0<RD#F%<D#2%5>RD#5#6#3REg00Q=RF#SRG%PFRH%O2RI%g2RJ%d2RK1L20RL%8ERM341ZK6R6P1P3g00QiRNg00RIRO'Y1X13=WNOdAV207CUROb2b3b4%2EP1b1'K%EERN,AEf5RP,0BRQg00RiRR,J2RS%;RRR#;RT#:RU,9Sg00SHRV'I'R=HFGPH1B27PJPK1@29RW94KLRX%Q5R5%8BRY/=W94KLC7P6POb2b3b4X0210B7#2\4^02P1f6R4PPO2b1'K%EQ,AQ%CARZ#3R[,T=1N0=%2[1f=[R\,N0[[%2=R0g00T4R]Ae=[7UW5%2\\]^50%3DRD,M2R0%;TRT#;R]#;R[#;#:5D2%:[%:]9D20%:T9D201M2E%:R5D2/9S,9U'9'9'9'9/IV=HFGPHP2P21B2CP31B24CGP7P21B2PP8PICGCGPJPK%C9R9#5RJ,@2RI,=Y1@2>R>54KP5PK1@2;R;94KMP5PK1@29R994KLP5PK1@2:R:94KLP5PKPXP5PKA4KLIP5%3JRJ#8%6A#6#6#6#6#6#6#3RA#8'=,?W%8<%8=%`Z5_2'='?%8DRZ1?:9'='?1=Z>,?;'?94KLC7C7C7C7C7C7P6POb2b3b4X02X62X72X82X92X:21AQC1AEC%2CREf:RQ#210JA,1410<\'1f7R\f8RA'1,0D'1f9RJ10DQ'1'1#2[\E\E[[[^02^62^72^82^92^:2P1PJ10BJ#EPN1>QB/0J,0<#<11Q?/>B11J?'0,0<#<11Q@/>B11J@'0,0<#<P8PCPPP4P\PAO<b1bAbBb?b>b=b<b;1]37#2eW@XC2XD2o"). Qed.
Lemma RB_pbl_nonneg : forall w h d, (0 <= h)%Z -> (0 <= RB_pbl w h d)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptPbl_iface ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h71bi001bh81Hh92H0h:2H1h;2Hhh<1dh=1hh>1wp;3p;2p;1p;4p;7p;8g00TPj3[Tg00HZj2@Tg0000j18Tg000Uj1=Tg002Rj24Tg001Xj20Tg003Xj1BTg004gj16Tg00UTj2>Tg0025j22Tg0013j1JTg00?jj1<Tg00?Aj27Tg00Jcj3:Tg00@Ij2HTg005oj1VTg00Aaj3FTg006Oj1UTg00BAj2DTg006oj1TTg00G;j4CTg007Mj1STg007kj1RTg008Vj2ATg00B_j2?Tg00CBj1MTg00LSj3;Tg0099j2LTg009[j2KTg00:5j2NTg00:aj3OTg00;;j3PTg00;Zj4QTg00A5j2GTg00KLj3ITg00>ej2ETg00V1j3ZTg00ITj4YTg00J?j7XTg00Koj8WTg00M6R0f0R1'Ep=1g00MTR2f1R3g00OQP1CYp=3P3g00N2R4g00NQR5P5g00O1R6P1g00P8FXp=5f3R7P4P5P5P6f2R4P3P1GWp=9%13R8A[7411@74#1g00PXR9#8R:#8R;#=R<f4R=%8;R;#=R>'4/07'0R?#B%6?#1f5R?%8;#8#=R;'4/0=,0<R@#B%6@#11>=>g00QiR@P@P@P2P1f8RAf7RB'@RC14A>/0B,0<#6RD'2REP@P2f6/>;%J9RF#=RG12DE'014A;/0B,0<#6'2P0n0100000020000n0100000020000#1P1g00Q=RBg00RiRE#<RH#<RI,72RJ172H172ERE5:25:2g00SHRH'H%VBRK3F%UBRLP21D24RMP3%T2RNCC%S2RO%R2RP1A20RQ1?2:R:'3,5PRR%M5R5PP1?29R9,3Q,5PRSP5A;29:,3Q,5PC9C91LP6R6P1P4g00RIRT,K@1N14=O@TdAP203CQRTb3b4b5X02X121247#1\8\8^02^12P1PDPCP7P=O4b21>?;P@P@P@P2P1f9R@/4>/0A,0<#6R>1@@ARC/2>'2,0G14@;/0A,0<#6R<'2P0n0100000020000#1P1%<IRI,72=:2EA:2EJ%<I,729:2E/HH'G'G=FBKPLP2PMP31D27CCPOPP1?2FRF,3Q,5PP5PPPSP5PPPRP51A2GA;2:99;295I2=;2F,3Q,5PC9C9C9P6PTb3b4b5X02X12X62%14%1712=7,27,0G/2?#1[\8[^02^12^62P1P<PCP>P7P=P?O6b2PKPLPNPO13QQ,5PP6PTb3b4b51E00P1b2n0110000020100b7n0110000020001b7b:b9b8AZ743#1eW;X<2X=2X>2o"). Qed.
Lemma RK_pbl_val : RK_pbl = 269%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptPbl_iface ()) [] "p;1p;2g0000j10Tg0013j11Tg000Uj13Tg009[j22Tg00MTg00PX#0#0#0#0#1#1#0#1#3'2o"). Qed.

Section PblIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition pixBilateral_contract : Prop :=
  forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 301120 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pbl <= kR)%Z -> (RB_pbl w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_pbl) (bR - RB_pbl w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.

Definition pixBilateral_null_contract : Prop :=
  forall fr cs C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PBL_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 301120 -> getr regs 10 = Z_to_bv 64 0 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  (forall fr' cs' m' regs', W C A m' md -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateral) m al_rom) md) S.
End PblIface.
