(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocPF () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9Leptonica5PFLib=seg_rom_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_loC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7RelocPF>rl_segs_lo_valC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7RelocPF>rl_segs_hi_valC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib6Common4Musl7RelocPF<rl_pf_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7RelocPF=pf_bounds_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_rw_loC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6eqb_eqc69OSSVerify5KrLib6Common4Musl7RelocPF<rl_pf_prefixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7RelocPF<pf_prefix_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pf_bounds_ok (img_lo rw_lo img_hi dT dS dF1 dF2 : Z) : bool :=
  (img_lo <=? 0x102e7 + dS) && (0x102f1 + dS <=? rw_lo)
  && (img_lo <=? 0x114a8 + dT) && (0x117c0 + dT <=? rw_lo) && (rw_lo <=? 2 ^ 31)
  && (0x117c0 + dT <=? 0x17f6c + dF1) && (0x18d9c + dF1 <=? rw_lo)
  && (0x117c0 + dT <=? 0x18d9c + dF2) && (0x18ed0 + dF2 <=? rw_lo)
  && (img_hi mod 8 =? 0) && (2 ^ 16 <=? img_lo) && (img_hi <=? 2 ^ 31).

Definition pf_bounds_chk {RL : Reloc} : bool := pf_bounds_ok rl_img_lo rl_rw_lo rl_img_hi dA_114a8 dS_102e7 dF_17f6c dF_18d9c.

(* [comment removed for export] *)
Definition pf_prefix_ok (segs : list Segment) (a : Z) : bool :=
  match rdn segs (fun _ => None) (Z_to_bv 64 a) 1 with
  | Some (b :: nil) => bv_unsigned b =? 45
  | _ => false
  end.

Class RelocPF (RL : Reloc) := {
  rl_segs_lo_val : segs_lo rl_segs = rl_img_lo;
  rl_segs_hi_val : segs_hi rl_segs = rl_img_hi;
  rl_pf_bounds : pf_bounds_chk = true;
  rl_pf_prefix : pf_prefix_ok rl_segs (0x102e7 + dS_102e7) = true
}.

Section PF.
  Context {RL : Reloc} {RP : RelocPF RL}.

  Lemma rl_rom_range : forall (x : word) b, seg_rom rl_segs x = Some b -> rl_img_lo <= bv_unsigned x < rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "h01Rh14__x1h24__x2h34__x3h41zh51Hh67__arithh74__ffh88__varmaph95__with:1bh;1xp;1p;2p;3p;4p;6p;8p;7g0000j12Tg000Uj1=Tg0013j1:Tg001Vj1ATg0028j1[Tg0037j2UTg0043j2LTg004Uj39Tg004oj4CTg0068j1BTg007;j23Tg007ej20Tg008Aj1>Tg008_j24Tg009<j1VTg00:?j21Tg00:Zj1TTg00;[j2NTg00<bj68Tg00=>j1KTg00>?j2ITg00?Fj1HTg00?fj1ETg00@Fj2<Tg00@dj4DTg00ABj1FTg00A`j1GTg00BKj26Tg00Bnj45Tg00CYj2JTg00D<j3@Tg00D_j1MTg00EDj1?Tg00Efj8OTg00FJj2PTg00Flj2QTg00GFj2RTg00H2j3STg00HQj4ZTg00ICj2YTg00I_j7XTg00JCj7WTf1R0g00JgR1g00KFR2P2g00KfR3f0R4g00LFFXp=7f2R5P1P2P2P3P0P4FWp=;g00LfR6#2R7#2#2R8#2#2#2#=R9#:%=8#:R8%A8p,2RLR:#[R;/U01L8439P;P5P0P4CC%B;R81395R<'0%>6R=,4<%V;R;'0'1g00MKR<P8f4,39R8,04148=R>/0;'1X4<P4%T:R?p,2RPR@,N:E8f3RA,39RB,0?14B=/0;'1P<P;f5,39R;,0?14;=/04'1X4<P4%K:R;1I:@E810?810>;'1g00MiR>#H%E>P<1<<5P01<<ACD%F<%G<R>P1P2P2P3P<16<6g00NUR116<7R7C5,7>R8P<1J<=9@<7P1%M6,6<R6C5,7>5;>%?2P<P7g00O<P6C5,7>9;>8GO1P>3P4P5g00OcR>g00PCR3'Q1R45=9>3dg00Pc=S<0CZb7b8b9X1<X2<X3<1040140=/05'110051Y5A'1[^1<^2<^3<P4P;f6,39P?P0O4b6b0b0b0W5W:W;o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_pf_facts :
    rl_img_lo <= 0x102e7 + dS_102e7 /\ 0x102f1 + dS_102e7 <= rl_rw_lo
    /\ rl_img_lo <= 0x114a8 + dA_114a8 /\ 0x117c0 + dA_114a8 <= rl_rw_lo /\ rl_rw_lo <= 2 ^ 31
    /\ 0x117c0 + dA_114a8 <= 0x17f6c + dF_17f6c /\ 0x18d9c + dF_17f6c <= rl_rw_lo
    /\ 0x117c0 + dA_114a8 <= 0x18d9c + dF_18d9c /\ 0x18ed0 + dF_18d9c <= rl_rw_lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "h01Hh12H8h22_Hh32H0h42H1h52H2h62H3h72H4h82H5h92H6h:2H7h;1mh<1np;2p;1p;3p;4g00QAj2ITg00RFj1HTg00:Zj1ATg0000j15Tg008Aj19Tg00D_j1:Tg00SLj2?Tg008_j2<Tg00TLj23Tg00Tij1GTg00Uij2;Tg00VGj2@Tg00=>j1FTg00Vdj2ETg00WDj2DTg00Waj38Tg00:?R0j21Tg007ej26Tg00XDj2CTg00Xdj4>Tg004Uj3BTg00Ocf0R1g00PC3Bp=0%51#:p=7%:1#:p=4%:1#5p==%51#5p=2p,2RLR2p,2RP'I%H2#0%A2R3g00LfR4#5R5#5R6#5R7#5R8#5#7#7#4R9#5#7#4#9%:4R4#:#4R:#5#=#2#2,?2R;'<R<'3R=%:9#2#7#9/<;R;%G2R9'3R>';R?%:7#7R@#2#=#=#=#2#9%46#=#7#2#2,?2R6'<RA,33RB';RC%4@#4#2#2#2#9/<6R6/39R@';RD%95RE%9:'@R:,39RF';RG%:5#4#4#4#7#=#4#2#9%:8#7#2R5#5,?2RH'<RI,36RJ';RK%54#2#4R4#7#=#7#4#2#9RL/<HRH/39RM';RN%:5,?2R5,<LRL,36RO';RP%=4#4#7#2#2#9/<5R5/39R4';RQ%F2R2%97'Eg00Pc'DR7';RR%98,@E/33RE';R8132:R2;81%08R8%02R2'1P0P8P2163<RS16;9RT163ARU1669RV169:RW166IRX16H9RY166LRZ1659R['1R\'1R]'1R^'1R_'1R`'1Ra'1Rb'1RcP1f1Rd98RE%0RRR%0ERE'1P0PRPEPcP1A8Q7d%0QRQ%07R7'1P0PQP7PcP1A8P4d%0PRP%04R4'1P0PPP4PcP1A8NOd%0NRN%0ORO'1P0PNPOPcP1A8KMd%0KRK%0MRM'1P0PKPMPcP1A8GJd%0GRG%0JRJ'1P0PGPJPcP1A8DFd%0DRD%0FRF'1P0PDPFPcP1A8C@d%0CRC%0@R@'1P0PCP@PcP1A8?Bd%0?R?%0BRB'1P0P?PBPcP1A8=>d%0=R=%0>R>'1P0P=P>PcP1g00MKRcP013d1#0f2R0/6d[Re16d1130d#0Rf[f3/60\f1Cd1Pdn2001000000120000000X;cW<RfPe^;c^<cRcP1P5P9fTO3P[PfPcP1P6PLfQO3PZPfPcP1PHP9fNO3PYPfPcP1P6PIfKO3PXPfPcP1P9P:fHO3PWPfPcP1P6P9fEO3PVPfPcP1P3PAfBRAO3PUPfPcP1P;P9f?O3PTPfPcP1P3P<PAO3PSPSPbP1PTPaP0PUP`f4PVP_f6PWP^f8PXP]f:PYP\f<PZP[f>f@C>C>C>C>C>C>C>C>b0b1b:b1b9b1b8b1b7b1b6b1b5b1b4b1b3b1X:>X0=PdP1O2n2001000010121000000b0X9BX0?PdP1O2n2001000010121000000b0X8@X0CPdP1O2n2001000010121000000b0X7FX0DPdP1O2n2001000010121000000b0X6JX0GPdP1O2n2101000010121000000b0X5MX0KPdP1O2n2101000010121000000b0X4OX0NPdP1O2n2101000010121000000b0X34X0PPdP1O2n2101000010121000000b0X27X0QPdP1O2n2101000010121000000b0X2EX0RPdP1O2n2101000010121000000b0X22X08PdP1O2n2101000010121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_img_hi_mod8 : rl_img_hi mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "h01Hh12_Hh21mh31nh42H0p;2p;1p;3g00QAj2HTg00RFj1GTg00:Zj1BTg0000j11Tg008Aj15Tg00D_j13Tg00SLj2;Tg008_j27Tg00TLj2<Tg00Tij1FTg00VGj2ATg00=>j1ETg00Vdj2DTg00WDj2?Tg00Uij2=Tg00Waj3@Tg00:?R0j2>Tg004Uj3:Tg00Y?j2CTg00Ocf0R1g00PC3:p=6%11#3p=4%31#3p=2%31#1p=8%11#1p=0f2R2f1R3/<1'=p=9p,2RLR4p,2RP'H%G4#6%B4R5g00LfR6#1R7#1R8#1R9#1R:#1#4#4#2R;#1#4#2#5%36R6#3#2R<#1#8#0#0,;4R='7'<%3;#0#4#5/7=%F4R=39%39#4R;#0#8#8#8#0#5%28#8#4#0#0,;4R8'7795%2;#2#0#0#0#5/78R8;9=%57R;%5<'AR<79=%37#2#2#2#4#8#2#0#5%3:#4#0R7#1,;4R>'7798%16#0#2R6#4#8#4#2#0#5R?/7>;9=%37,;4R7,7?798%86#2#4#0#0#5/77;9=R=%E4R4%59'DR9g00PcR7'?R6'=R8%5:,A;/<5R5'=R;1<4<R4;@1%6;R;%64R4'>P0P;P4g00MKR<?:97R:P1A@853%68R8%65R5'>P0P8P5P:P1A@=63%6=R=%66R6'>P0P=P6P:P1P01?31#6A:<23[R0A:<311?23#6R?[f3=:<2\?1C31P3n2001000000120000000X2<X3<P0^2<^3<P1P9P7P3O3P:P1b0b4X06X1=P3P1O2n2101000000121000000b0X15X08P3P1O2n2101000000121000000b0X14X0;P3P1O2n2101000000121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_img_lo_ge : 2 ^ 16 <= rl_img_lo.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "h01Hh12_Hh21mh31nh42H0p;2p;1p;3g00QAj2JTg00RFj1ITg00:Zj1ATg0000j13Tg008Aj15Tg00D_j16Tg00SLj2:Tg008_j28Tg00TLj22Tg00Tij1HTg00VGj2@Tg00=>j1FTg00Vdj2ETg00WDj2DTg00Uij2<Tg00Waj3>Tg00:?R0j2?Tg007ej2;Tg00XDj2CTg004Uj3BTg00Ocf0R1g00PC3Bp=9%31#6p=4%61#6p=1%61#3p=7%31#3p=0f2R2f1R3/21'<p=G1<23/<1p==p,2RLR4p,2RP'J%I4#9%A4R5g00LfR6#3R7#3R8#3R9#3R:#3#4#4#1R;#3#4#1#5%66R6#6#1R<#3#7#0#0,:4R='8'2%6;#0#4#5/8=%H4R=3G%69#4R;#0#7#7#7#0#5%18#7#4#0#0,:4R8'8,25%1;#1#0#0#0#5/88R8/2=3=%57R;%5<'@R<,2=%67#1#1#1#4#7#1#0#5%6:#4#0R7#3,:4R>'8,283=%36#0#1R6#4#7#4#1#0#5R?/8>/2=%67,:4R7,8?,283=%76#1#4#0#0#5/87/2=%F4R4%59'Eg00Pc'D3=R9%5:,@;R;/25R:'<R=124<R4;>1%9=R=%94R4'?P0P=P41;;5R<P1A>9:3%99R9%9:R:'?P0P9P:P<P1g00MKR7P01231#91;23[R01;311223#9R6[f3/;2\61C31P3n2001000000120000000X27W3P0^27^37P1P;P5P3O3P<P1b0b4X0:X19P3P1O2n2101000000121000000b0X14X0=P3P1O2n2101000000121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_img_hi_le : rl_img_hi <= 2 ^ 31.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "h01Hh11mh21nh32H0h42_Hp;2p;1p;3g00QAj2ITg00RFj1HTg00:Zj1?Tg0000j11Tg008Aj16Tg00D_j15Tg00SLj2;Tg008_j27Tg00TLj23Tg00Tij1GTg00VGj2>Tg00=>j1FTg00Vdj2ETg00WDj2DTg00Waj3CTg00:?R0j2BTg007ej2<Tg00XDj2ATg004Uj3@Tg00Uij2=Tg00Ocf0R1g00PC3@p=9%11#5p=4%51#5p=2%51#1p=8%11#1p=0f2R2f1R3'=/=1p=:p,2RLR4p,2RP'I%H4#9%?4R5g00LfR6#1R7#1R8#1R9#1R:#1#4#4#2R;#1#4#2#6%56R6#5#2R<#1#8#0#0,;4R='7'3%5;#0#4#6/7=%G4R='3%59#4R;#0#8#8#8#0#6%28#8#4#0#0,;4R8'7,353:%2;#2#0#0#0#6/78R8/3=%67R;%6<'>R<,3=3:%57#2#2#2#4#8#2#0#6%5:#4#0R7#1,;4R>'7,38%16#0#2R6#4#8#4#2#0#6R?/7>/3=3:%57,;4R7,7?,38%86#2#4#0#0#6/77/3=3:%F4R4%69'Eg00Pc'D%6:,>;/353:R5134<R;;C1%95R5%9;R;'BP0P5P;1<4<R:P1g00MKR9P01331#91<23[R01<311323#9R=[f3/<2\=1A31P3n2001000000120000000X19W2P0^19^29P1P4P<P3O3P:P1b0b3X0;X45P3P1O2n2101000000121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_pf_prefix0 : rdn rl_segs (fun _ => None) (rl dS_102e7 0x102e7) 1 = Some [Z_to_bv 8 45].
Proof.
ltac2:(KReplay.run1 (kr_t_RelocPF ()) ["PF"] "p'0h01Hh12H0h21nh31li001lh42b1h52b2h61mh71bi011bh82b0i022b0h91eh:1oi031oh;1zi042l0i052l1i061xp;2p;1p;4p;3p;6p;8g00Y_j2TTg0028j1STg0000j12Tg00D_j13Tg008Aj1?Tg00SLj2MTg008_j2LTg00Zdj2HTg000Uj1@Tg0013j14Tg00EDj1DTg00[ij2CTg00\Oj1RTg00\nj4ATg00?fR0j1PTg001VR1j1OTg007;j21Tg00WDj2<Tg00?Fj1NTg00]fj38j2Bj1GTg0043j27j1JTg004Uj30Tg00<bj6KTg00^Fj2=Tg00Y?j2ITg00Flj2;Tg00^ej3FTg00_Ij6ETg00_gj8>Tg00`Dj2QTf0R2#2#2p=:%32#3p=9g00OcR3g00PCR4702p=6g00MKR5f1R6;02p=5p,2RLR7p,2RP'T%S7R8g00LfR9#2R:#:R;#2#:R<#3#2#3#9#:#3#9#?R=%99#9#2#3#2#:#:,M7R7'LR9'H#6P8%@<R<#4%@;R;#4R>#DUR?1C<9g00a>#RR<CA%P>R9#OR@P1P9P1P9P3P2P0P>P3P2g00a]R1P0P>P3P211;6%9:#2#3#?R:'<RAP1n10110400020020102105n10110000020020101104RBP1n10110600021010000#61C;:RC%N>RD58>RE,79RF90@6]0P2P0P>%6B1796=0@F]0P2A0314RBP3P1P3p-0P2g00b=RGg00bZn0110100020000X93g00c6P4P2EKR4PG179D=0@F/=2b1W0P0P>P0P>P3P2f2R3,1;/<:P1n10110400020020102105#6f3R1=8>6,79=0@F]0P2%6Ag00:?RA1<62#61536[R015621<36#6RH[1513\H1I62P6n2001000000120000000X65X25P0^65^25P211;1R0P:P6O3150:P9P@%J9R0P0f4RH=8>DPEP@\9/;0P9P91B>H1B>CPDPDP>P9\9R0%G>REPEPHPCP0\>/;Eg00cRRE%42R0%46RIPA%43?06211131116'5RA[11361132'5%41?036[RJ%4H?013\AAF362P2n2001000000120000000W5W4W2PJ^5I^40^2EP2P;f5REPCP5P:11;CRC,52X;51;5C11;EP6EEO4b1G>1;9DG>G>b0b1W0P4PGf7A8>1358>,79=0@F/=2b1X0BX39X8>P6P2O2n10110000020120101100X39X7>P6P2O2n10110000020021101100X39P2O1P4PG%D9=0@F/=2b1X0Bn10110300021110000P6O1b:P8P?1Q7=P<CA=0@Feb0o"). Qed.
End PF.
