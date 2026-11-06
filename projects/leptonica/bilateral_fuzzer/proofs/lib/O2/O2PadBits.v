(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.OL Require PadBits.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocOL.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2PadBits () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits4lez4C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits8M2_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits2M2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits;M2g_outsideC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits3M2gC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits;padbits_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits3InvC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib2O29O2PadBits3InvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic4True01C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL:o2_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL;o2_sites_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL7o2_leptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL9o2_img_olC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O29O2PadBits>padbits24_L_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSPCspec_lept_stderr_s1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP<sum_contractC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBitsBpadbits24_contractC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits>padbits24_L_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP>spec_padbits24C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_entryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP:ls_sev_gotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9ls_img_loC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9ls_img_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_sp_loC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic3and01C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_fmts1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_addrs00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Section PB.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables pix w h d wpl data sp : Z.
Variables ra s0v s1v s2v : word.
Hypothesis Hpix : (1 <= pix /\ pix + 12 <= 2 ^ 64)%Z.
Hypothesis Hpix64 : (pix + 64 <= 2 ^ 64)%Z.
Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
Hypothesis Hw : (1 <= w <= 20000)%Z.
Hypothesis Hh : (1 <= h <= 20000)%Z.
Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z.
Hypothesis Hsp : (48 <= sp /\ sp < 2 ^ 64)%Z.
Hypothesis Hra : ret_ok ra.
Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
Hypothesis Hwpl : (0 <= wpl <= 20000)%Z.
Hypothesis Hdata : (1 <= data /\ data < 2 ^ 64)%Z.
Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64)%Z.
Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = true.
Hypothesis FR : disj_apart data (4 * (wpl * h)) (sp - 48) 48.
Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true.
Hypothesis FP12 : disj_apart pix 12 (sp - 48) 48.
Hypothesis FP : disj_apart pix 64 (sp - 48) 48.
Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
                           (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
           (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v).
Definition M2g (vw vh : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 vw))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 vh))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
Definition M2 : word -> option byte := M2g (Z_to_bv 64 w) (Z_to_bv 64 h).
Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2PadBits ()) ["VPORT"; "PB"] "h03RLTh11zp;2p;1p;3g0000j2<Tg000Lj10Tg0011j12Tg001Oj23Tg001lj2;Tg002Hj2:Tg002cj11Tg003Bj24Tg004?j15Tg005<j16Tg005Zj27Tg006@j28Tg006jj39Tg007Dg008IR0g008gf0R1'<g009E#0R2#2%02#0#0#0R2#2'3,;1':g009j#1#1#1#1f1R3'4#5%02#6R21723'8590[]1P1b0o"). Qed.

#[local] Notation RS := (4 * (wpl * h))%Z (only parsing).
Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x)
    /\ mem_grows M2 Mi.
Lemma M2_grows : mem_grows M M2.
Proof.
ltac2:(KReplay.run1 (kr_t_O2PadBits ()) ["VPORT"; "PB"] "h03RLTp;9p;2g00:Il92Tg00;Rl91Tg00<Uj20Tp,1MR0p,1wR1p,1hR2p,1dR3p,2spR4p,2raR5p,3s0vR6p,3s1vR7p,3s2vR8M92P0P1P2P3P4P5P6P7P8M91,00f0b0o"). Qed.

Lemma M2g_outside : forall vw vh (x : word),
    (bv_unsigned x < sp - 48 \/ sp <= bv_unsigned x)%Z -> M2g vw vh x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O2PadBits ()) ["VPORT"; "PB"] "h03RLTh12vhh22vwh31xp;8p;1p;2p;:p;3g00=Rj8=Tg000Lj10Tg005<j11Tg00>^j12Tg006@j2<Tg00?Aj1:Tg0011j17Tg00?fj24Tg001lj25Tg0000j26Tg00@Cj23Tg00@]j18Tg00A?l:9Tg006jj3;Tp,1MR0p,1dR1p,2spR2p,2raR3p,3s0vR4p,3s1vR5p,3s2vR6p,3HspG=g009ER7#0#0#0R8#0#0#0#1R9#2R:f0R;,<9R9%:7#0#0#0#0#7,42'51629'3%18#2#8P0P1P2P3P4P5P6f3f2f1R6M:9P0P6O13;[^3:^1:]2P;b0o"). Qed.

Theorem padbits_run : forall regs,
    (d <> 24)%Z -> (wpl = (w * d + 31) / 32)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (0x1b0b8 : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_O2PadBits ()) ["VPORT"; "PB"] "h01Hh12M'h22b1h32b2h41nh54regsh65regs'h71xh83RLTh91bp;Yp;1p;2p;3p;5p;<p;6g00BClYXTg000Lj10Tg00?Aj12Tg005<j1ATg00>^j1;Tg00COj2UTg0011j11Tg006jj34Tg00D;j1MTg00DTj2LTg00E1j2ITg00ENj2WTg00Ekj29Tg00FNj36Tg005Zj2?Tg00@]j1VTg00G1j1TTg00H0j2STg00I0j2RTg00Ijj5@Tg00Jcj3FTg00K^l<OTg00Lbj1NTg00MBj3DTg00MYj3CTg00NUj2>Tg006@j2<Tg00Noj3KTg00OSj2JTg00Omj1PTg00Pbj6QTg00Q>j2GTg00R7j3HTg002HR0j2BTf0R1#0#0p==%21#2p=:f3R2f2R3f1R4'G;41p=3f4R5AH3417H2p=81G23=454/B1p=71B41,B3p=Eg00RWR69641p=5p,2fxR7g00S3R8g00Skg00Tgg00Udg00V]p,1MR9p,3romR:p,3pixR;p,1wR<p,1hR=p,1dR>p,3wplR?p,4dataR@p,2spRAp,2raRBp,3s0vRCp,3s1vRDp,3s2vREp,4Hpixp,6Hpix64p,2Rwp,2Rhp,2Hwp,2Hhp,2Hdp,3Hspp,3Hrap,2Cwp,2Chp,2Cdp,4Cwplp,5Cdatap,4Hwplp,5Hdatap,2HRp,4SOKrp,2FRp,4SOKfp,4FP12p,2FPMYXg009ERF#0RG#2RH#ARI%0GRJ#0RK#=RL#0#ARM#;RN'UROg008IRP%2FRQ#0RR#0RS#0#174>#MRT1L<>%2QRQ#:#1'I%1L'W94P?RLPNP3%1FRUP619IUd56IRVPBC3PNP2%1GRGP619IGd56IRW1?MARXC3PNP5%1KRYP619IYd56IRZPCC3PNf5R[%2JRJ#1R\P619I\d56IR]PDC3PNf6R^%0J#1RJP619IJd56IR_PEC3PNf7R`%0H#1RaP619Iad56IRb1?M;R;C3PNf8Rc%2H#1RHP619IHd56IRdg008g,?MReC3%AK#;#V\NRf%T8P7f;Rg%2S#:#0,S8%2K#:#:#:#=#2#:#=#1'RP9P:D@P7P4PBP1P:D@RK3FP9P<P=P>P?P@PAPBPCPDPEP1M<OPNP4PbPePNP4PWPXPNP4PZPCPNP4P]PDPNP4P_PE%;IRAPAPVPAPWPAPZPAP]PAPbPAPdPA%1SRSP619ISd56IPA%2R#1RRP619IRd56IPA%0Q#1RQP619IQd56IPAP_%NAR_D8D8D8D8D89DA1W7?Cg4D7D7D7D7D73EX1f'>X6O,>O[[[[[[[[[]5g00WXR6%;1Rd%;4RbP0%;3?4411<231<2454PR0[1<341<3154P%;2?434[R]%;5?423\0AK341P1n2001000000120000000W3W2W4P]^3b^2d^46P1PM%2F#0#:#=#=#2#0#2#:#0#=#1RF,?MR615MFRd1JPF1<M61<Md54PdO4b0A4N6dPNP6PNP315IURUPBC3PNP215IGRGPXC3PNP515IYRYPCC3PNP[15I\R\PDC3PNP^15IJRJPEC3PNP`15IaRaP;C3PNPc15IHRHPeC3g00X6P7Pgf<P9P:D@;FK%P1PNP4PaPePNP4PGPXPNP4PYPCPNP4P\PDPNP4PJPEPAPUPAPGPAPYPAP\PAPaPAPHPA15ISPA15IRPA15IQPAPJP_D8D8D8D8D89DA1X7A?Cg4D7D7D7D7D73EX1f,>fX6O,>O[[[[[[[\L\T^5OX9NP4PdP1EQb0b8o"). Qed.

End PB.

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = 0x17bd8 /\ SSP.ls_sev_got L = 0x38470 /\ In 0x11161 (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L <= 0x11161 /\ 0x116f0 <= SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.
Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 0x1b0b8 (48 + SSP.ls_frame L) L).
Proof.
ltac2:(KReplay.run1 (kr_t_O2PadBits ()) ["VPORT"] "h04__p1h14__p2h24__x1h33RLTh47__arithh54__ffh68__varmaph75__with81Hh94__x2h:1ah;2HCh<2HLh=3HLeh>5HLfmth?4HLfrh@5HLimghA4HLsghB1Lp;1p;3p;7p;2p;4p;6p;8g00Y\j1sTg00Z\j1]Tg00\2j3MTg00]Aj7aTg00^Tj2rTg00G1j1lTg000Lj1<Tg00?Aj1>Tg0011j1=Tg00H0j2qTg00E1j2ITg00_cj1OTg00`nj3[Tg00b?j1CTg00cJj1BTg00dWj13Tg0000j20Tg00ecj15Tg002HR0j21Tg00Lbj1`Tg00foj1_Tg00gOj2UTg00gmj1^Tg00hKj1pTg00i6j2JTg00iYj2\Tg00j<j1oTg00j^j2kTg00OSj2jTg00k@j2iTg006jj3NTg00klj3hTg00lKj4gTg00m=j1RTg00nHj3YTg00nkj1fTg00oIj4eTg00ogj4;Tg010Bj1XTg00MBj3ZTg011Mj4dTg0128j7cTg012\j6mTg013@j7nTg013dj8bTf0R1#<#>p=9%>1#>p=4%>1#<p=6%<1#<p=2g008IR2f1R3;N1p=Sg008gR4/03/11p=H%R1,03p=A%O1,04p=8f6R5f5R6#X5Z2f4R7f3R8f2R9'0/13'1/11'1p=?AN293/11p=:1041p=71089%R1,03'1p=G10781093/11'1p=L%B3=N21p=Q%X19Z23p=P1089/13,17%O1,04'1p=W1193/11p=KP2P3g014HP1Cdp=EP3g014oR:g015NR;P;g015nR<P1g016NFcp=DP3P:P;P;P<P1Emp=TP9P:P;P;P<P3P1Fnp=@P8P:P;P;P<P9P3P1Gbp=F1131,19p=Vg016n%s1g00X6p,2fxR:%]33MP:g00S3R=g00Skg00Tgg00Udg00V]P9Fa1r=9%l=R>%]87M:g009ER?#<R@#<#9RA#>#4#4#6#9#4#2#=%6?RB#<RC#4#6,q='I%2C#=RC%O7R='I;[79M>:[[P1P0%C8%9?#4#6#4#4#9#6#2#=RD'S%B8%>?#6#2#9#2#9#4#2#2#=RE%<ARA#<RF#9#9#6#2#9#=RGP8%38RH10HG'H%>A#6#4#4#2#2#=RA%58RH1AH8%88F?3:%C7%B7PGP7%37RH#7PHPGPH%4F#4#2#6#9#=RF%>B#6#2#=RB,IGRH%57RI1IFBRJPIPIP7CGDL%7=F?7:E7:DP9%C6/SD%B5PGP5%35R=10=G'HPA%55R=1A=5%85F?7:EP0f7R5/QEPGP5%35R=10=G'HPA%55R=1A=5%85F?f8R5#C%B5PGP5%35R=#7P=PGP=PFPH%55R=PJP=P=P5CGDL%85F?7:E7:DP1f9R5/QEPGf:R=%3=RI10IG'HPA%5=RI1AI=%8=F?P0f;R=,PG%3=RI10IG'HPA%5=RI1AI=P=DWf<R=#C%B=PGP=%3=RI#7PIPGPIPFPH%5=RIPJPIPIP=CGDL%8=F?7:E7:DP1f=R=,PGf>RI#3RK10KG'HPA%5IRK1AKIPIDWP0f?R0#3RI#710IGPA%50RIPIP0CG3K%80f@R0#C%B0PGP0%30RI#7PIPGPIPFPH%50RIPJPIPIP0CGDL%80F?7:E7:DP1fAR0#3RI#710IGPA%50RIPIP0CG3KfBRI#8fCRK#C/SDRD1QKERE1PGKRL%3KRM#7RN10MGRO10MFRM%5KRP,0HRQ10JPRR1APKRP'1RS'1RT'1RU'1RV'1RW%8KRK'1RX'1RY'1RZP=PEPYP5PLPXP6PWPKPNPV11DZRZP0P1PIO2W:RI%6?#4#2#2#6#4#6#2#=fDR0#O,IC;[09M>:^:ZRZp-0R>g018;R:#`R0%_:R:1U23RC%^2RD%p2RV1J241\2?R?'E,DVRN1TV8RK5@V1TV7R75@V%o;R;PNCF1kV<R<P1P9g018gRNg019GRW'j1i19=NNWdAh243CgR4b5b6b7X22X0>W1%71?K39%73[^22^0>^1>P1fERW#5RN,0ARX%RWRL,0NR5'1RY%3WRW/0GREPWP8O4b4b3POPUPIPZP0P:PCPDPV1J2GRU,E?,DVRO9@VK=@V7R=P;POCFP<P4b5b6b7X22X0>X1>101G=K39RO103G[^22^0>^1>P1PY%7WRYPWP8O4RWb4b3PMPTPIPZP0P:PCPDPVP=P;1J2FR=,E?,DVCFP<P4b5b6b7X22X0>X1>103F\O^22^0>^1>PWb4b3PQPSPIPZP0P:PCPDPV1J2A/E?,DV=@V79@VKRKP;1J2BRB9Y2U/E?,DVCFP<P4b5b6b7X22X0>X1>10A1=V39RA10H3[^22^0>^1>P1P511YERYPNP8O4REb4b3PRPPPIPZP0P:PCPDPVPKP;AY2=B/E?,DVCFP<P4b5b6b7X22X0>X1>10J3\A^22^0>^1>PEb4b3PIPZP0P:P21U29P3%f2CePDPV1TV61\2@,E?,DVR?5@V9@V7P;P?CFP<P4b5b6b7X22X92X0>X1>10139V981039[^22^92^0>^1>P1PXPYPLPNP8O5b4b3C;C;C;C;C;P1C;C;C;C;W?W@P3P1O2n2001000010121000000W8W>P3P1O2n2001000010121000000W8WAP3P1O2n2001000010121000000W8W=P3P1O2n2001000010121000000P3O2b3W;W<WBo"). Qed.

End VPORT.
