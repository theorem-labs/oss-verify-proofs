(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ADepot_iface ARep ARepQ ARepFrame ARepKit AFreeRep AQConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeStoreK () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission5BothW4ARep6aslotsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5ndistC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7busy_ofC5ARocqVerifyHarness?AgentSubmission5BothW4ARep:aslot_busyC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7aregionC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7get_clsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl@c_allocated_userC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=c_mapped_userC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7junk_atI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW4ARep:aslot_addrC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=size_of_classC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission5BothW4ARep8xb_classC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7xb_slotC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame7xb_fitsC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8xb_allocC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame@aslot_busy_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame:junk_frameK47Corelib4Init5Logic3and01I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep5aconc00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xbusy00C5ARocqVerifyHarness?AgentSubmission5BothW4ARep<aslot_shadowC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7fill_atK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6to_natK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame;cells_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame:fill_frameC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW4ARepAslot_shadow_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List:repeat_appC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7rz_sizeC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8granulesC47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef6repeatC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission5BothW4ARep4xb_nC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xb_stC5ARocqVerifyHarness?AgentSubmission5BothW4ARepBblock_shadow_bytesC5ARocqVerifyHarness?AgentSubmission5BothW8AFreeRep6bbatchC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06K5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xbusy01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_BATCH_CLASSK5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate03K46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate00".
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
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) ["CANSEC1"; "Frames"] "p'0h01bi001bh11kh22SLh31zh42EBh51Hh63WFBh71oi011oh83C1'h91Dh:2DUh;2E0h<2E1h=2E2h>4FIT1h?2Hkh@2K1hA3NEWhB3OTHhC3UNDhD1XhE2X'hF2_HhG1ahH1chI2sthJ3st'i021xp;5p;2p;3p;1p;6p;:p;9p;4p10000p4p70g000gR0p4p710p8p1001Ep4p710p1001gp4p710p8g00RTj5MTg0038j2VTg00SJj28Tg00T?j30Tg00U6j3JTg00V0j2HTg00Vgj23Tg00Waj19Tg003Tj2ATg00Xdj1:Tg00Ydj2=Tg00ZAj36Tg00[8R1j1UTg00>dj31Tg00[Zj35Tg00\Tj14Tg00]Tj32Tg00^Pj2LTg00_2j1GTg00_jj1BTg00`aj1ETg00GGR2j2KTg00a]j2ITg005YR3j27Tg00=^j2STP0j6CTg00b9j2RTg00c1l:QTg00;Tj1PTg00d6l9NTg00e5j4OTf2R0f1R4f0R5'I'7p=@f4R6f3R7?504%4536p=?g00D_R8?145p=>A0704=165p=<A1804/75p=D1745,70p=FA5704=665p=TA1867A1804/75'7p=;g00ePR9g00fKR:p,1LR;P6P0p,1mR<P5DMP3g00FDR=/V5R>f6R?/80R@7@5P1g00gBRAp-0RBf5RC?074AJ;<5RDP<P;P7P4P7D?n10110200021010000[^181H;413C4RE#9RF'A%:E/=F56<18C0/>@13?7#9f7R@/37#9'>13@6#:f8RF/36RE#:RG'>f:RH/8?9@>5%UARIA0F@4RJf9RK?0@431p,1WRLA5;@4RM%4@RN32PIPHPFP01LA5ROD<%G4RP%B4RQ%E4RR7D7RS7DK[^0A3FP1PAPBPJp,2m'RJ=J;5RTA6JMNn10110200021010000'K[^1813H?RN#:%9NRN'=,I=1H;@f;RM/3@RU#9RV'A%:URU/=V52L[P;PHPFPJP@DM[[[[[P518F69@>5P1PAPBA0@C4PDP<P;PCP4PCD?n10110200021010000[^181H;6%9ERE'A1=GE56<18FC18KC'>13K?#9/>N13H@#:/>Uf=RU/8K9@>5A0MH4RNf<RE?0H451IA5;H4RG%4HRV52LPIPUPMP0POD<ADPES[^0A3FP1PAPBPNPTA6JGVn10110200021010000'K[^1813UKRV#:%9V'=,I=1H;HRVf>RG/3HRN#9RW'ARX%:NRN/=WRY52L[P818GHA@>54P1PAPBA0GU4PTPJP;PUP4%4URZDTn10110200021010000R[[^181H;MR\13GMR]#9R^'A%:]R]/=^56J'7X38P8PWf@RW/8E9@>5P[[^18R[1A\51=]556J'7X38P8PNf?RN/3M#9R],A\1=5]56J,7[X3818NM9@>5R[P1PAPBA0UE4R]PTA5;E4R\%4ER^56Jn10110200021010000R_[^18A6JXYP7P4P5O2A0GE491I]A2L\^A0NU0R^=1IOADPGS[^0A3F/K_P2A0GU0R2=1I^A5;U0R^=2LZA0WG7RS=1IOPPPNPQP6PRD;[^0A3FP1PAPBP2PTA6J^Zn10110200021010000P1PAPBA0NG7R^PTA5;G7RZ%4GR256Jn10110200021010000R\P5A1I^SA2LZ2fAR2?0N6RZ=1IOPPPWPQPCPRD;[^0A3FP3PIPWPNP6PZD<A5;N6%4N52LPIfBRZPWPCPOD<PPP2PQP?PRD;[^0A'7P1PAPBA02WCPTPJP;PWPCPWD?n10110200021010000P5PIPZP2P?fCR^?02?D<A5;Z@%4Z52LPIfERSP^PFPOD<PPfDR]PQPKPRD;[^0A'7P3A5;^F%4^52LPIfFP]PKPOD<PPPSPQPHPRD;[^0AP1PAPBA0S]KPTPJP;P]PKP]D?n10110200021010000P5A5;SH%4S52LfIRSfGR`;0ERa=1IOPPfHRbPQPUPRD;[^0APIPaP1PAPBP5PTPJP;PbPUPbD?n10110200021010000X7IP^PEPMO2P1PAPBPaPDP<P;P`PEP`D?n10110200021010000fJRa?0bUPIP1PAP1PAPBP5PDP<P;PaPNPaD?n10110200021010000PIfLRcfKRdPWP4D<A1I7OPPfNRWPQP^PRD;[^0AP1PAPBP7PTPJP;fMRTPZPTD?n10110200021010000]6]4]2P5PIPTPcP21LA4D<1LA7RB=1IOPPfOR1PQP]PRD;[^0AP5P71SIBO2%G7PW%B7P^%E7D;P3%G6/>1%B6%E67D]AJ;JCP5%G?fQ'>%B@%E@7D`P3%BF/>b%EFAJ;JKP5%BH/>a%EMP;PLP<PJp,2MURKp,2WMRFPEPMP5P8fW%BU95;5%4552LX38P8PcfXR3=5;5%4352LX38P2%BEP4EC%GER3PCEC1R;E%4352LeM:QW>W@P4P5O2n2001000000120000000W5W8P4P5O2n2001000000120000000bGW6W4X2DX0AP5O1P<P;PSPGPSD?PIPdPaPN%PARND<A1INOPPPTPQPZPRD;[^0APLP<PJA5;c2%4cRcP0PKPF1I=cP@WFM9NW6W4W2n10110100021010200P4P@P0O3b7b2A0b`EPCECW6W9P4P5O2n2001000000121000000W5W4P4P5O2n2001000000121000000W5P5O1P5XA\P5O1n200100000021100010000b7X?[X18PLP<PJPXPYPCPKPFP5M9NCO13UHRF#:RKP0EC%9FRFP7EC18UHP6EC18GM9@>5P_[^181AVF1=KF56J'7eP;PUPMPJPHDMeW:WBW=W<W;WCW2P4P5O2n2001000000121000000W5XH8XE:WDXJ9WIo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) ["CANSEC1"; "Frames"] "h01kh11zh21Hh32SLh41Dh52DUh62E0h72E1h82E2h92EBh:2Hkh;3NEWh<3OTHh=3POSh>3UNDh?1Xh@2X'hA1chB1lhC1nhD1ohE2sthF3st'p;5p;2p;1p;4p;3p;6p;9p;:p10000p4p70g000gR0p4p710p8p1001Ep4p710p1001gp4p710p8g00h9j5MTg0038j2KTg00SJj27Tg00\Tj14Tg00i5j13Tg006kj1VTg00V0j2BTg00Vgj21Tg00Waj15Tg00Xdj18Tg0054j1DTg0041j1CTg004Vj1ZTg00inj4?Tg00jej1YTg00kCj1XTg007Kj1WTg00>dj3<Tg00]Tj36Tg005YR1j2:Tg00GGR2j2ITg00a]j2HTg00kfj1JTg00lFj2ETg00m;j1FTg00m[j2RTP0j6@Tg00n9j2QTg00nYj1PTg00o=j1TTg0106l9UTg0116l:aTg00e5j4`Tg00[Zj3_Tg0125j1OTg00T?j3^Tg012mj2]Tg00OHj3LTg013nj4NTg003Tj2\Tg00Ydj2[Tf2R0f1R3f0R4'H':p=>A_034#Op=2f3R5A^034']p=0g014dR6f4R7P5g015YR8%J0/E3;L4CNp==1\34#Op=;1[34#3p=9g00D_R9?<34p=AP6P5P0AL834CNp=G1E03=L84p=Sg00ePR6g00fKR:p,1LR;P7P0p,1mR<P4DMP1g00FDR=/K4R>f6R?/70R@7>4P<A2;53%45RA#3PAf5RAP5P3C0%V8R8D=[^09P<1B;311A3RB#5RC';%8B/9Cg00FbRC#D#D#D#D#C#D#C#ZRBC?17A0/A@11?5#5f7R@/15#5'A11@7#8f8RD/17RE#8RF'Af:RG/7?9>>4%CC#C#C#Y#X#WRC%4@RHPDP@P3C0RIPHf9RJP@P3C03<p,1WRKA2;@3RL%3HRH36':p,2m'RMPLPHPIP8D='I[^0911G?RI#8%5IRI'9,H=1B;@f;RL/1@RN#5RO';%8NRN/9O56K[1K=HP;PLPJPMPDDM[[[[[[P417D79>>4P<A2;A3%4ARH#3PHP@PAP3C0P8D=[^09P<1B;7%5ERE';19FEPBC?17DA17JA'A11J?#5/AI11G@#8/ANf=RN/7J9>>4%4GRIPLPGP3C0REPIf<RFPGP3C05<CA2;G3RH%3IRI56K':PMPHPIPEP8D='I[^0911NJRE#8%5E'9,H=1B;Gf>RE/1GRH#5RO';%8H/9O56K[1K=IP9f?RI/7LA>>43PMA2;E3%4ER=#3RO#JRHP=PIPEP3C0'EP8CGRP[^09PM1B;FRQ11IFRR#5RS';%8RRR/9SPBC?':X19P911ILRS#5RTfARU/7N9>>4PP[^09RPPM1;Q419R4PBC?':X19P9%8SRSPMf@RR/1F#5RV,;Q194VPBC?,:PX1917RF9>>4RPPMA2;N3RV%4NRQ#3RWPQPEPNP3C0RXP8D=RY[^09PM1B;LRZ/;TR[19STRSPBC?P7P3P4O2PQPIPNP3C09<CXA6KVW':/IYP2P=PIPEP0C0R2P=PRPEP0C05<CA2;E0R0=6KO':PMP01EH2P8CGPMA2;I5R2%4IRH#3R0PHPRPIP5C0ROP8D=R=P4PHPUPIP5C09<COA6K20':P1%4RR1PUPRP7C0P1fBR0PRP7C05<CA2;R7%3156KPMA2;UA%4UR1#3P1P0PUPAC0P8D=P4%40RUfCR1P0P?C0PUfDRUP0P?C05<CA2;1@%41#356KPC%4UR1fFR0PUPDC0R2PMfERO=2;JRH%4ORW#3RV#JRX/E4P8CGXBCPRPDP@O2P<A2;UD%31P2P8D=PKP<PMPHPWfGPOPJC0=SX8R8P4p,2MURJp,2WMRWg016NR2PXA2;0GR0%F456KXC2P9PVA6K04X19P3%FX1RVGE@g00QI,QX%PXE@%T8#F96KHeM9Ub3P1POPUPDC0P3E@W4W9P3P4O2n2001000000121000000W2P4O1P4X;=P4O1n200100000021100010000bDX:PX09PKP<PMP[PSPBP?PJPWP3M:aC`11ELRW#8RJP5E@%5WRWP7E@17ELPAE@17IF9>>4PY[^09PM1;ZW19JWPBC?':eP;PEPFPMPLDMeW=W5W<W8W7W6W>W3P3P4O2n2001000000121000000W2XA9X@:W?XF6WEo"). Qed.
End Frames.

(* [comment removed for export] *)
Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeStoreK ()) ["CANSEC1"] "p'0h02H0h11xi001xh21zh34__p1h44__p2h54__p3h64__p4h74__p5h84__p6h94__p7h:4__x1h;4__x2h<4__x3h=4__x4h>4__x5h?1lh@1HhA3H25hB3H26hC3H27hD3H28hE1ShF7__arithhG4__ffhH8__varmaphI5__withJ3k24hK1yhL3z25hM3z26hN3z27hO3z28i011pp&0p;1p;2p;3p;<p;4p;8p;6p;Bp;7p10000p4p70p1000gp4p710p8g016mR0p4p710g001gR1p4p710p8g0041j1?Tg004Vj1RTg00i5j14Tg0038j29Tg017Lj1gTg00jek100Tg00kCj1vTg007Kj1WTg0054j1<Tg018Fj2XTg018lj1kTg019dj33Tg00>dj30j1_Tg00kfR2j1BTg01:Aj36k204Tg01:`j2dTg00=^j2LTg01;7j2]Tg003TR3j2MTg00m;R4j1`Tg01;Tj2sTg01<7j3rTg01<Tl<nTg01=9j2KTg00a]j2ATg01=[j1mTg01>9j2lTg00Lkj1CTg01>Zj3GTg00MJj2jTg00N\j2PTg006kk10=Tg00OHj3OTg007kj2fTg008Ik10<Tg008gj4VTg009Ek10;Tg009ck10:Tg00;1j2JTg00:Nj2eTg00;Tk103Tg00@ij4STg01?Cj3bTg00<6j3aTg00=<k202Tg00>8j2~Tg00?>j3}Tg00?]j4|Tg01?fj4xTg01@Qj8wTP0j4[TP1j6ITg01@nj1ZTg01Abj1uTg01BWj1yTg01CYj1zTg00^Pj2tTg012mj2{Tg00Ydj2iTg01DSl<cTg01E8mB01Tg005Yj2^Tg00GGj2qTg00N3j3TTg00Ohk605Tg00ATj7pTg00B8k706Tg01E^k707Tg00B\k808Tg01FBk609Tg00D_R1f0R0'Lp=Ef1R5=010p=2f2R6%B0765p=51i65/i0p=7g00FDR7/]0p=@P1g016NR8P1P1P2f4R9P4f3R:g01G9R;P6P5P0M<cp=UP1P8P1P1P2P6P4P5P;P7P7P0M<cp=oP8P8P8P1P1P1g00n9P4P4P4P3g01Gff5R3P9P:P6P5P0NB01p=YA0107p=81^:61^50'qp=:1j10p=DAT1509T16p==AT150p=hP5g00C@R;g00C_R2P2g00D?R<P0J05p=>P1P5g01HIP0CSp=FP5P;P2P2P<P0g00EdFpp=1P6P;P2P2P<P5P0K06p=;P1P5g00E=P0CSp=NP6P;P2P2P<P5P0K07p=QP:P;P2P2P<P6P5P0L08p=Hg01I0P0P7g01J0P7P7J09p=\g00FbR;#?R=#RR>%45'9%g7R?#E%?=R@#?RA#?#RRB/2?P1PB&00ARA#vRC#WRD%<;RE#<#<#<RF#?#<#?#R,XARG%40RH55C%k7RI95CGRJ%49RK?7HI95CG53C53CA5CGK30X21%4BRB#E12>BP1P>A5CG0RK%43RH?70I95CG93CJ53C%BHRJ96CG50DX21%EIA017IP1P7%B>RL96CGRMf6RN#4RO?7>095CG93CK53CA5CGORK50DX21PD%B7RPA7H>7RQ#BRR'dRS96CGRTA3CM0=0DKX?DPD1dLSRU96CGA0D0KX?DP8PD204CGRKPKPUPJPD\8/LKA08UJ%@>RK1]77RV%@QRW'MRX'MRY%@HRZ'2P8P1%_8P4%_1%`5%`0'2A08501s503rXK8X18PUPYPLPKP0X11RY%@0X11RUP>P>%E>DUPSPXPPPV1L179oYUPRPWPYPUPQPQ%EQDUEYEYPJPZPYPUPHPH%EHDUM<n1K7H1A7H12ZH19H7%8ZC:%@OP1f7RO#4?7>7RZ,K71A7Z%@ZRH/2Z19Z7%8HC:f8RH#4?7>7#@P11K771A77RZ%8VRU1977RYPUC:PVP11K7>1A7>RV12K>19>7RU%8KC:PKP1p-0RKg00GaRJ%m;,l1RQg00QIRW#CRX#CR8#CR4#CR[#CR\#C#DR]5G1%D\R\9G1QR^%D[R[%D4R49G1Q%D8R81j1WRW3=R_'h3=g00QhR`'PAG1Q8R8%DX/hW5=49=]\/P`A=48W9=\[/P`AG1Q[==^_/P`&0=J5OJ5OJ5OJ3O%WJP1P11f19P6&0<1RJCVP5P11f13P:PJCVCV&0;1&0:1RJ1>JO1J1;R;1e1>R`'F,1J5;J1e17R_,N`,1J1>JH5;J5QJ&032R2PJP1P_g01JhP_CS,1Jf9R^,>J5;Jf:,>J1J1=R[/F_,1J5;J5QJP2PJf;RQ,>J1J1ERE%<=,J1R==b1`=b1_R\'F,1J5;J1N\_,1J1FE_,1J5;J5QJP2PJf<R\,>J1J1@R@/F=,1J5;J1N=_,1Jf=R_,>J5;J5QJP2PJ1N`=,1JP2Aa1[E9a1;/F@,1JCHCHCHCHCH202J<P0P6g00HMRJg00HmR<'L1~06=0J<dA}175C|bGbHbIX:1X;1X<1X=1X>1X3KX4KX5KX6KX7KX8KW9P3120>PUPNC:PZPHP^%86C:PQA7N>7RQ,2919Q7%89C:P_12NO19O7f>R_C:19>H1MNO,M3/2H[[[[[^:1^;1^<1^=1^>1^3K^4K^5K^6K^7K^8K^9KP0%8O%4_R_,A7A7_>7,A7PY%8:%85PVP_POP3P:P5P6P9PNPHP\OAbFbObDbNbCbMbBbLbACxGwA3CMTPCPGPLPSC[EIA6CGPA6CGR53CPCPGPPPRC[EIPIP0EIb0PBP0EIb0P?P0EIb0%\5R0#ZR?#g#4RB95CGg01KOPD%u0%\6#Z#y%<F#?#<#R,XA%k?R?#BRA56CA6CGAn011000003101010000%46RA?7B?95CG53C53CA5CGARA50Deg00gB%z5't,{6=0DAeW@XJ1XE1o"). Qed.
End CANSEC1.
