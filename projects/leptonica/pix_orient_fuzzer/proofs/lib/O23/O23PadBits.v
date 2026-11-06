(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require PadBits.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocOL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23PadBits () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits4lez4C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits8M2_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits2M2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits;M2g_outsideC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits3M2gC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits;padbits_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits3InvC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib3O23:O23PadBits3InvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL;o23_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL<o23_sites_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL8o23_leptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL:o23_img_olC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23:O23PadBits>padbits24_L_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSPCspec_lept_stderr_s1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP<sum_contractC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBitsBpadbits24_contractC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL7PadBits>padbits24_L_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP>spec_padbits24C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_entryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP:ls_sev_gotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9ls_img_loC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9ls_img_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_sp_loC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic3and01C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_fmts1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8ls_addrs00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
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
ltac2:(KReplay.run1 (kr_t_O23PadBits ()) ["VPORT"; "PB"] "h03RLTh11zp;2p;1p;3g0000j2<Tg000Lj10Tg0011j12Tg001Oj23Tg001lj2;Tg002Hj2:Tg002cj11Tg003Bj24Tg004?j15Tg005<j16Tg005Zj27Tg006@j28Tg006jj39Tg007Dg008IR0g008gf0R1'<g009E#0R2#2%02#0#0#0R2#2'3,;1':g009j#1#1#1#1f1R3'4#5%02#6R21723'8590[]1P1b0o"). Qed.

#[local] Notation RS := (4 * (wpl * h))%Z (only parsing).
Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x)
    /\ mem_grows M2 Mi.
Lemma M2_grows : mem_grows M M2.
Proof.
ltac2:(KReplay.run1 (kr_t_O23PadBits ()) ["VPORT"; "PB"] "h03RLTp;9p;2g00:Il92Tg00;Rl91Tg00<Uj20Tp,1MR0p,1wR1p,1hR2p,1dR3p,2spR4p,2raR5p,3s0vR6p,3s1vR7p,3s2vR8M92P0P1P2P3P4P5P6P7P8M91,00f0b0o"). Qed.

Lemma M2g_outside : forall vw vh (x : word),
    (bv_unsigned x < sp - 48 \/ sp <= bv_unsigned x)%Z -> M2g vw vh x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_O23PadBits ()) ["VPORT"; "PB"] "h03RLTh12vhh22vwh31xp;8p;1p;2p;:p;3g00=Rj8=Tg000Lj10Tg005<j11Tg00>^j12Tg006@j2<Tg00?Aj1:Tg0011j17Tg00?fj24Tg001lj25Tg0000j26Tg00@Cj23Tg00@]j18Tg00A?l:9Tg006jj3;Tp,1MR0p,1dR1p,2spR2p,2raR3p,3s0vR4p,3s1vR5p,3s2vR6p,3HspG=g009ER7#0#0#0R8#0#0#0#1R9#2R:f0R;,<9R9%:7#0#0#0#0#7,42'51629'3%18#2#8P0P1P2P3P4P5P6f3f2f1R6M:9P0P6O13;[^3:^1:]2P;b0o"). Qed.

Theorem padbits_run : forall regs,
    (d <> 24)%Z -> (wpl = (w * d + 31) / 32)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (0x6ed1c : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_O23PadBits ()) ["VPORT"; "PB"] "h01Hh12M'h22b1h32b2h41nh54regsh65regs'h71xh83RLTh91bp;Yp;1p;2p;3p;5p;<p;6g00BClYXTg000Lj10Tg00?Aj19Tg005<j1@Tg00>^j1<Tg00COj2WTg0011j11Tg006jj35Tg00D;j1NTg00DTj2LTg00E1j2JTg00ENj2ITg00Ekj28Tg00FNj34Tg005Zj2?Tg00@]j1VTg00G1j1UTg00H0j2TTg00I0j2STg00Ijj5ATg00Jcj3FTg00K^l<OTg00Lbj1MTg00MBj3ETg00MYj3DTg00NUj2>Tg006@j2=Tg00Noj3KTg00OSj2PTg00Omj1QTg00Pdj6RTg00Q@j2GTg00R9j3HTg002HR0j2BTf0R1#9#9p=;f3R2f2R3f1R4'G;51p=2%91#0p=:f4R5AH3417H2p=61G23=554/B1p=71B41,B3p=Cg00RYR69441p=3p,2fxR7g00S5R8g00T0g00Tog00Uog00Vkp,1MR9p,3romR:p,3pixR;p,1wR<p,1hR=p,1dR>p,3wplR?p,4dataR@p,2spRAp,2raRBp,3s0vRCp,3s1vRDp,3s2vREp,4Hpixp,6Hpix64p,2Rwp,2Rhp,2Hwp,2Hhp,2Hdp,3Hspp,3Hrap,2Cwp,2Chp,2Cdp,4Cwplp,5Cdatap,4Hwplp,5Hdatap,2HRp,4SOKrp,2FRp,4SOKfp,4FP12p,2FPMYXg009ERF#0RG#9RH#@RI%0GRJ#0RK#0#0RL#0#@RM#<RN'WROg008IRP%9FRQ#0RR#0RS#0#175>#NRT1L<>%9QRQ#;#1'J%1L'I95P?RLPNP3%1FRUP618IUd54IRVPBC2PNP2%1GRGP618IGd54IRW1?MARXC2PNP5%1KRYP618IYd54IRZPCC2PNf5R[%9JRJ#1R\P618I\d54IR]PDC2PNf6R^%0J#1RJP618IJd54IR_PEC2PNf7R`%0H#1RaP618Iad54IRb1?M;R;C2PNf8Rc%9H#1RHP618IHd54IRdg008g,?MReC2%@K#<#V\NRf%U8P7f;Rg%;S#:,T8%;K#;#;#:#0#;#:#0#1'SP9P:DAP7P4PBP1P:DARK3FP9P<P=P>P?P@PAPBPCPDPEP1M<OPNP4PbPePNP4PWPXPNP4PZPCPNP4P]PDPNP4P_PE%<IRAPAPVPAPWPAPZPAP]PAPbPAPdPA%1SRSP618ISd54IPA%9R#1RRP618IRd54IPA%0Q#1RQP618IQd54IPAP_%MAR_D6D6D6D6D69EA1W7?Dg4D7D7D7D7D73CX1f'>X6O,>O[[[[[[[[[]5g00WiR6%<1Rd%<4RbP0%<3?5411=231=2455PR0[1=341=3155P%<2?534[R]%<5?523\0AK341P1n2001000000120000000W3W2W4P]^3b^2d^46P1PM%:F#;#:#9#:#:#0#0#;#:#0#1RF,?MR613MFRd1PPF1=M61=Md55PdO4b0A5N6dPNP6PNP313IURUPBC2PNP213IGRGPXC2PNP513IYRYPCC2PNP[13I\R\PDC2PNP^13IJRJPEC2PNP`13IaRaP;C2PNPc13IHRHPeC2g00XGP7Pgf<P9P:DA;FK%Q1PNP4PaPePNP4PGPXPNP4PYPCPNP4P\PDPNP4PJPEPAPUPAPGPAPYPAP\PAPaPAPHPA13ISPA13IRPA13IQPAPJP_D6D6D6D6D69EA1X7A?Dg4D7D7D7D7D73CX1f,>fX6O,>O[[[[[[[\L\T^5OX9NP4PdP1ERb0b8o"). Qed.

End PB.

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = 0x63080 /\ SSP.ls_sev_got L = 0x1125c8 /\ In 0x161d5 (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L <= 0x161d5 /\ 0x18b66 <= SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.
Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 0x6ed1c (48 + SSP.ls_frame L) L).
Proof.
ltac2:(KReplay.run1 (kr_t_O23PadBits ()) ["VPORT"] "h04__p1h14__p2h24__x1h33RLTh47__arithh54__ffh68__varmaph75__with81Hh94__x2h:1ah;2HCh<2HLh=3HLeh>5HLfmth?4HLfrh@5HLimghA4HLsghB1Lp;1p;3p;7p;2p;4p;6p;8g00Ynj1sTg00[0j1]Tg00\Fj3NTg00]Uj7bTg00^hj2rTg00G1j1mTg000Lj1GTg0011j1;Tg00H0j2`Tg00E1j2JTg00`7j1OTg00aBj3[Tg00bSj1?Tg00c^j1ATg00dkj16Tg0000j20Tg00f7j17Tg00?Aj1HTg002HR0j21Tg00Lbj1aTg00gCj1_Tg00gcj2UTg00hAj1^Tg00h_j1qTg00iJj2ITg00imj2\Tg00jPj1pTg00k2j2lTg00OSj2kTg00kTj2jTg006jj3MTg00l@j3iTg00l_j4hTg00mQj1RTg00n\j3XTg00o?j1gTg00o]j4fTg010;j4<Tg010Vj1YTg00MBj3ZTg011aj4eTg012Lj7dTg0130j6nTg013Tj7oTg0148j8cTf0R1#G#Gp=2%H1#Hp=5%H1#Gp=4%G1#Hp=3g008IR2f1R3;M1p=Sg008gR4/03/11p=F%R1,03p=@%O1,04p=9f6R5f5R6#Y5Z2f4R7f3R8f2R9'0/13'1/11'1p==AM293/11p=:1041p=81089%R1,03'1p=E10781093/11'1p=L%A3=M21p=Q%Y19Z23p=P1089/13,17%O1,04'1p=V1193/11p=KP2P3g014\P1Cep=BP3g015CR:g015bR;P;g016BR<P1g016bFdp=CP3P:P;P;P<P1Enp=TP9P:P;P;P<P3P1Fop=>P8P:P;P;P<P9P3P1Gcp=D1131,19p=Wg017B%s1g00XGp,2fxR:%]33NP:g00S5R=g00T0g00Tog00Uog00VkP9Fb1r=9%m=R>%]87N:g009ER?#GR@#2#5#5#5#4#3#5#2#;%4?RA#GRB#5#4,`='J%2B#;RB%O7R='J;[79N>:[[P1P0%?8%4?#2#5#2#2#4#2#2#2#;RC'S%A8%2?#3#2#4#3#3#5#2#4#2#;RD%3?#4#2#3#5#3#3#3#;REP8%68RF10FE'F%4?#2#4#5#3#4#3#4#;RF%78RG1@G8%98F=3:%?7%A7PEP7%67RG#8PGPEPG%3?#5#3#4#5#3#2#3#;RG%HA#4#2#;RA,JERH%77RI1JGARJPIPIP7CEDL%8=F=7:D7:CP9%?6/SC%A5PEP5%65R=10=E'FPF%75R=1@=5%95F=7:DP0f7R5/QDPEP5%65R=10=E'FPF%75R=1@=5%95F=f8R5#?%A5PEP5%65R=#8P=PEP=PGPH%75R=PJP=P=P5CEDL%95F=7:D7:CP1f9R5/QDPEf:R=%6=RI10IE'FPF%7=RI1@I=%9=F=P0f;R=,PE%6=RI10IE'FPF%7=RI1@I=P=DVf<R=#?%A=PEP=%6=RI#8PIPEPIPGPH%7=RIPJPIPIP=CEDL%9=F=7:D7:CP1f=R=,PEf>RI#6RK10KE'FPF%7IRK1@KIPIDVP0f?R0#6RI#810IEPF%70RIPIP0CE3K%90f@R0#?%A0PEP0%60RI#8PIPEPIPGPH%70RIPJPIPIP0CEDL%90F=7:D7:CP1fAR0#6RI#810IEPF%70RIPIP0CE3KfBRI#9fCRK#?/SCRC1QKDRD1PEKRL%6KRM#8RN10MERO10MGRM%7KRP,0HRQ10JPRR1@PKRP'1RS'1RT'1RU'1RV'1RW%9KRK'1RX'1RY'1RZP=PDPYP5PLPXP6PWPKPNPV11CZRZP0P1PIO2W:RI%4?#5#4#5#3#2#3#5#2#;fDR0#O,JB;[09N>:^:ZRZp-0R>g018OR:#aR0%_:R:1U23RB%^2RC%q2RV1I241\2?R?'B,CVRN1TV8RK5>V1TV7R75>V%p;R;PNCD1lV<R<P1P9g019;RNg019[RW'k1j19=MNWdAi243ChR4b5b6b7X22X0>W1%81?K39%83[^22^0>^1>P1fERW#7RN,0FRX%RWRL,0NR5'1RY%6WRW/0ERDPWP8O4b4b3POPUPIPZP0P:PBPCPV1I2ERU,B?,CVRO9>VK=>V7R=P;POCDP<P4b5b6b7X22X0>X1>101E=K39RO103E[^22^0>^1>P1PY%8WRYPWP8O4RWb4b3PMPTPIPZP0P:PBPCPVP=P;1I2GR=,B?,CVCDP<P4b5b6b7X22X0>X1>103G\O^22^0>^1>PWb4b3PQPSPIPZP0P:PBPCPV1I2F/B?,CV=>V79>VKRKP;1I2ARA9X2U/B?,CVCDP<P4b5b6b7X22X0>X1>10F1=W39RF10H3[^22^0>^1>P1P511YDRYPNP8O4RDb4b3PRPPPIPZP0P:PBPCPVPKP;AX2=A/B?,CVCDP<P4b5b6b7X22X0>X1>10J3\F^22^0>^1>PDb4b3PIPZP0P:P21U29P3%g2CfPCPV1TV61\2@,B?,CVR?5>V9>V7P;P?CDP<P4b5b6b7X22X92X0>X1>10139W981039[^22^92^0>^1>P1PXPYPLPNP8O5b4b3C<C<C<C<C<P1C<C<C<C<W?W@P3P1O2n2001000010121000000W8W>P3P1O2n2001000010121000000W8WAP3P1O2n2001000010121000000W8W=P3P1O2n2001000010121000000P3O2b3W;W<WBo"). Qed.

End VPORT.
