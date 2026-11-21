(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (aslots_update_gen, aslot_shadow_update_gen, slot_shadow_bbatch)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ADepot_iface ARep ARepQ ARepFrame ARepKit AFreeRep AQConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeStoreK () := "C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@aslot_busy_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:fill_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List:repeat_appC59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef6repeatC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep6bbatchC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06K59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xb7008, 0xb7030); (0xbb500, 0x13c530); (0x149d88, 0x149d8c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p10000p4p70p1000gp4p710p8p1001Ep4p710p1001gp4p710p8g002Cj2WTg0038j20Tg003Tj22Tg0041j11Tg004Vj1;Tg0054j16Tg005Yj23Tg0064j29Tg006Qj2VTg006kj1UTg007Kj1TTg007kj2PTg008Ij1OTg008gj4NTg009Ej1LTg009cj1KTg00:Nj2:Tg00;1j2ATg00;Tj1ITg00<6j3>Tg00<Yj3=Tg00=<j2HTg00=^j2JTg00>8j2GTg00>dj3FTg00?>j3MTg00?]j4ETg00@Oj4CTg00@ij4QTg00ATj7DTg00B8j7RTg00B\j8STf0R0#1#1#1#1p=?%10#1#1#1#1#1#1#1p=5%10#1p=B%60#6p=@%60#6#6#6p=7f2R1g00C@R2g00C_R3P3g00D?R4g00D_R5f1R6g00E=P0CQg00EdFDp=4P1P2P3P3P4P6P0FRp=8f3R7P2P3P3P4P1P6P0GSp=<1W60g00FDR2/011271g00FbR8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g00GGf4R</27%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1020R>%;8R?,00'3R@f6RAf5RB'2190;,2=RC'019:0RD/0A'3'3X75,V5P112B</0=P5f7RE/2A/0C10DE'3,3@X75R@P2g00GaRD#URC%TDRDP51P51P6%O5CNRF%L5RG%K5RH1:52RI1A58R854H%I3R3PH1A599>58R91:5=RJ54HP3A4HII1:5?RK94HIRL58H1:5;RM9=5I9>5J94H91:5:RN==5I=4H858H58HC<C<1HH4R4P0P1g00HMRIg00HmRO'J1G01=FIOdAM526CEROb4b5b6X05X151261/0=1022102?RI'31217RP192;,2='019:2/01'3'3[\>^05^15P0PAPEP<P6O4b3CCW2P0O110:BP5P@P?PCPDPFPGPHA4H9MP3PHA4HN8P3A4HKK98HLA=5KM9>5J94H9A=5NK=4H858H58HC<C<P4POb4b5b6X05X151206/0;10:610??,3I19?;,2=,0P19:?/01'3'3[[^05^15P0PAPEP7P6O4b3CCW2P0O1n200100001021100011000W9W8W2X;5X:5o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) [] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p10000p4p70p1000gp4p710p8p1001Ep4p710p1001gp4p710p8g00IMj2YTg0041j11Tg004Vj1<Tg0038j20Tg0054j1:Tg00GGR0j2DTg003Tj23Tg0064j27Tg006Qj2ETg006kj1VTg007Kj1UTg007kj2TTg008Ij1RTg008gj4QTg009Ej1PTg009cj1NTg00;1j2BTg00<6j3@Tg00:Nj28Tg00;Tj1KTg00<Yj3>Tg00=<j2JTg00=^j2ITg00>8j2HTg00>dj3MTg00?>j3GTg00?]j4OTg00@Oj4CTg005YR1j2?Tg00@ij4FTg00ATj7STg00B8j7XTg00B\j8WTf0R2#1#1p=L%12#1#1#1#1#1#1#1p=5%12#1#1#1p=Af2R3f1R4'3/02p=;1034/?2p=61?42,?3p==P3g00C@R5g00C_R6P6g00D?R7g00D_R8P4g00E=P2CFg00EdFSp=2P3P5P6P6P7P4P2FXp=4f3R9P5P6P6P7P3P4P2GWp=91Y42g00FbR5#1R:#1#L#5R;#AR<#5#5#5#5#5#5#<R=9;34P1%<;R;/09R1%<<R<9;93%:5#1#A#:#:#:#:#A#5#<R>/09'Dg00FDR?%<5R@,02762RAf5RB,0;RCf4RD,3B172=,3<RE17>2RF/0B363=X38,E8P4f6RG?;B<10>G'DP0f7R0?;G<10>0f9RG,0;f8RB,3G10FG76E5=AX38,E8P2A;B0<P8f:RH,0;13HG10FH76E5=AX38RAP?g00GaRE#VRF%UEREP81T83P4%R8CQRI%P8RJ%N8RK1B85R51B8:5@8R:188<RL52K%K6R6PK188;=2K5RMP6188?RN=2KN188@RO92KNRP54K188=RQ9>8N9@8L92K:188>RR=>8N=2K554K94KM54KC9C91JK7R7P2P3g00HMRNg00HmRS'I1H23=MNSdAG8?4CORSb6b7b8X08X181324RN/0<10;410?@RT96??10;3R;133917?=,3<17>?/03363=[[^08^18P2PGPHP4PDO4b5CCW2P2O110>BP8PAP@PFPEPIPJPKA2K:QP6PKA2KR5P6PKPMP6A2KOO94KPA>8OQ9@8L92K:A>8RO=2K554K94KM54KC9C9C9P7PSb6b7b8X08X1810N=10>410@@,?T139D17@=,3<17>@/09367=1\;[[^08^18P2PGPHP0P4PDO5b5CCW2P2O1n200100000021100011000W2X4CP4P2O2n2001000000121000000W9W4X;8X:8o"). Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62rch72H1h87__arithh94__ffh:8__varmaph;5__with<2H0h=2hih>2lop;3p;1p;2p;4p;6p;7p;8p10000p4p70p1000gp4p710p8p1001Ep4p710p1001gp4p710p8g00JBj3bTg00K7j1aTg0054j15Tg0041j11Tg004Vj19Tg00L5j18Tg0038j20Tg005YR0j2>Tg0064j2=Tg003Tj2ETg006Qj2JTg00Lkj1DTg00MJj2CTg00N3j3ITg00N\j2VTg006kj1UTg00OHj3TTg007Kj1STg007kj2GTg008gj4RTg009Ej1QTg009cj1PTg00;1j2BTg00Ohj6OTg00;Tj1NTg00:Nj2FTg00<Yj3ATg00<6j3HTg00=<j2MTg00=^j2`Tg00>8j2_Tg00>dj3^Tg00?>j3[Tg00?]j4ZTg00@Oj4KTg00@ij4YTg00ATj7\Tg00B8j7WTg00B\j8]Tf0R1#5#5#5#5p=7%51#5p=X%11#1p=@%11#1#1#1p=:%11#1#1#1#1#1#1#1p=3f2R2f1R3'0/>1p=21>31,>2p=?g00D_R4/F1p=;P2g00C@R5g00C_R6P6g00D?R7P4P3g00E=P1CYg00EdF\p=4P2P5P6P6P7P3P1FWp=6f3R8P5P6P6P7P2P3P1G]p=<1031,>2p=Lg00PLR9Ab231%a8g00FbR:#5R;#5#7#7#7R<#1#5#XR=#5#7#1#@#:#3#3#9R>%88R?%5<#7#7#1#@#:#3#3#9R<,0?32g00GG%5:#1#:#7#:#3#9R?/08R@%:=#3#9R=,02RA'>%1:RB#:#3RC#7#7#7#7#1#@#:#3#9RDf4RE#8,02728g00FDRF%9:RG,01721RHf5RI,0?RJ1=D1RK%1C#@#3#3#3#3#3#3#9RC,=1,E=RLf6RM#8,0ERN52E72I3?X54,J4P3108=92?EP0PJ10E=f7RJ,0?ROf8#8,0M92ML92KJ5?HX54,J4RMP110J=P4f:RP,0?f9RQf;#8RR,0Q72L92KP5?HX54RHPFp-0RKg00GaRLg00QIRS#D#DRT#D,C41C4T1C4S5I45I4g00Qh'V%UL3TRS%SLRLP41G42P31G48CRRT%Q4RU%P4RV%;>1B4;R;54VPVP5P6P6P7PIEOR556V%N6R6PV1B4BRB%;=RW54VP6PV%;?1B4:R:54VRXP61F4FRY=4VY%;GRZ94VYR[56V%;DR\=A4Y=4V:%;CR]9A4Y9H4W94VBA4VB;RY56V56V96VX56VC<C<C<1MV7R7P1P2g00HMR^g00HmR_'`1_12=^^_dA[4F3CZR_b9b:b;X24X34X44W1A2>2810?210FGR?92FF1=DF1=FC,E=10EIRF52E7287?@[\A[^24^34^44^1KP110R<PRPQPPPJP3P2O7b8CKW7X0OP3P1O2n2001000010121000000W0P1O1%8I,0892DEP010DIPNPMP110DJ%8Q,0JP4PHPGPSPLPTPUPV%;<94V;96V5P6PVPYP6PVA4V\:P6A4VZZ96V[AA4\Z=4V:AA4Z]9H4W94VB=6VY56V96VX56VC<C<C<P7P_b9b:b;X24X34X44X1KAL82<102810D2AL?GG1=DG1=GC,E==2EF7287?@[[[^24^34^44^1KP110>RPRPQPPPJP3P2O7b8CKW7W0P3P1O2n2001000010121000000W0P1O1n200100001021100011000b<W0X=4X>4X69P1O1X69P1O1W6o"). Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl : Z).
Definition kfactsF : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6352896 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6352896 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP)   (* [comment removed for export] *)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
  /\ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104)      (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsF.

Ltac kind := pose proof KF as KF'; unfold kfactsF, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Ft4) & F_res & F_slot & F_sh & (Fn1 & Fn2 & Fn3 & Fs1 & Fs2 & Fs3) & (Fc1 & Fc2 & Fc3) & F_lst & F_eb & F_gl);
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma KF_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xb7008 \/ 0xb7030 <= A) /\ (A + k <= 0xbb500 \/ 0x13c530 <= A) /\ (A + k <= 0x149d88 \/ 0x149d8c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_low : forall A k, 2147450880 <= A -> A + k <= 2148244992 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= UB - 16 \/ UB + 8 <= A) ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_obj : forall A k, ((6352896 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma aslots_update_gen : forall st st' X X' c,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
          /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b))
    \/ match busy_of X' c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [(EB & D & WFB)|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk). destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frame; [exact MU| exact WM| exact SL | exact FIT1 |]. unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

Lemma aslot_shadow_update_gen : forall st st' X X' c,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (slot_shadow_bytes (size_of_class c) (busy_of X' c k) = slot_shadow_bytes (size_of_class c) (busy_of X c k)
          /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c)))
    \/ rw_cells bsegs m' (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k))]) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [[EB D]|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL| exact MU| exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
  intros S k24 H. unfold slot_shadow_bytes, bbatch. cbn [xb_n xb_st].
  replace (rz_size 0) with 16 by reflexivity. replace (shlen 16) with 2 by reflexivity. replace (granules 0) with 0 by reflexivity.
  rewrite <- !repeat_app. f_equal. lia.
Qed.
End CANSEC1.
