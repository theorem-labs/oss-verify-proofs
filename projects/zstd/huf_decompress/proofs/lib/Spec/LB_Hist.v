(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (LRX_cons, n63X_cons, bc_kv and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt PState Prog
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_PCaps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Hist () := "C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consI46Stdlib5Lists4List6Exists00C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec7LB_Hist2bcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist2BCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum=zcount_nonnegC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6LB_Sum8zsum_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appK47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib4Spec7LB_Hist3N24C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec7LB_Hist2N4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6LB_Raw3LRXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw4n63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw4R63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA4bigbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist2YWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4lminC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List6filterC46Stdlib5Lists4List?Forall_cons_iffI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib4Spec7LB_Hist8LRX_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist:bigb_kv_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec8LB_PCaps8lmin_posC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8LB_PCaps<kv_class_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib4Spec6MI_Cnt@size_to_class_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib4Spec7LB_Hist5bc_kvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw9R63X_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist9n63X_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist7N4_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist8N24_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Hist7BC_consC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec7LB_Hist4AMBZC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic4True00C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib5Lists7ListDef6Forall02C46Stdlib9micromega;ZifyClasses5mkappK47Corelib5Lists7ListDef6Forall01".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bc (n : Z) : Z := if n =? 24 then 1 else n / 4 - 1.
Definition BC (Y : list (bptr * Z)) : Z := zsum (map (fun b => bc (snd b)) Y).
Definition YW (Y : list (bptr * Z)) : Prop := Forall (fun b => snd b = 24 \/ exists l, 0 <= l /\ snd b = 4 * (l + 1)) Y.
Definition N24 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 24) Y.
Definition N4 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 4) Y.

Lemma BC_cons p n Y : BC ((p, n) :: Y) = bc n + BC Y.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Yh11nh21pp;2p;1p-1R0p10000p4p710R1p8P0p1000Lp4p710R2p8P0p1000mR0p4p7210p8g001JR3p4p70R4P1p8P4P2p8P4P0p4p710p8P4p1002Cp4p710p8P4p1002ep4p710p8P4p1003Ep4p710p8P4p1003bR0p4p710p8P4p1004?p4p710p8P0p4p7210p1004\p4p710p8g005:j25Tg005Zj14Tg006:j10Tg006nj11Tg007bj23Tg008?j22Tg008YR01530#4R4f1R2#0f0R1#1'3,20X04X10X23f2P2P1O3W0W1X23o"). Qed.
Lemma BC_app Y1 Y2 : BC (Y1 ++ Y2) = BC Y1 + BC Y2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02Y1h12Y2h21bh31lh41zp;2p;1p;3p;4p;6p;5p-1p10097p4p710R0p8g001JR1p4p70R2P0p8P2p1009np4p710p8P2p100:jp4p710p8P2p100;ep4p710p8g005:j2=Tg005Zj17Tg00<cj3<Tg006:j19Tg0000j41Tg003Ej36Tg00=@j10Tg007bj23Tg00>5j32Tg008?j2;Tg00>Oj28Tg004\j65Tg00?Hj5:Tg006nj14Tg008YR2,=1R0#7R3%72R4P0P2f0R59<12#9X20R1f1R6C1R7P0P2P1P5C1R8562R9%05P0P2P1f2C1#0%07R:'3R;522X34P2%08,3:R:A225;X421;2:%091878E5P0P2P1A6065R8C1P0P2P1P6P5D:E5%48%46%45'3522eX13X03P6P5O2X13W0o"). Qed.
Lemma N24_cons p n Y : N24 ((p, n) :: Y) = (if n =? 24 then 1 else 0) + N24 Y.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Yh11nh21ph31bh41zp;2p;1p;4p;3p;6g005:j2?Tg005Zj1>Tg00?dj49Tg00<cj36Tg00@Dj1=Tg00@ij12Tg00ANj15Tg00Alj21Tg0097j33Tg007bj20Tg00>5j34Tg008?j28Tg00BIj3:Tg009nj4<Tg004\j6;Tg00Bij17Tg001JR0g008YR11?01R2#>R3P1g00C^R4P1P0P1f2R5f1R6C9R79601g00D>R8#=#2#2#2#5R9'1%58R8g00DcR:n0100000020000f0R;9601/19X32R<=32;R='0P4P11159P8P:n0100000020000A32<6'0941;X41P4P11169P8P:n0100000020000R:/0=,81A:27;R=932<P2P<P7P;C<E;%7=%7;,0:541eX03X11X20P5P6P;O3W0W1W2o"). Qed.
Lemma N4_cons p n Y : N4 ((p, n) :: Y) = (if n =? 4 then 1 else 0) + N4 Y.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Yh11nh21ph31bh41zp;2p;1p;4p;3p;6g005:j2>Tg005Zj1=Tg00?dj4;Tg00<cj33Tg00@ij17Tg00ANj15Tg00Alj20Tg0097j32Tg007bj21Tg00>5j34Tg008?j28Tg00BIj39Tg009nj4:Tg004\j6<Tg00EAj16Tg001JR0g008YR11>01R2#=R3P1g00C^R4P1P0P1f2R5f1R6C;R79301g00D>R8#7#7#5R9'0%58R8g00DcR:n0100000020000f0R;9301/09X32R<=22;R='1P4P11059P8P:n0100000020000A22<6'1941;X41P4P11069P8P:n0100000020000R:/1=,81A927;R=922<P2P<P7P;C:E<%6=%6;,1:541eX03X11X20P5P6P;O3W0W1W2o"). Qed.
Lemma N24_app Y1 Y2 : N24 (Y1 ++ Y2) = N24 Y1 + N24 Y2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02Y1h12Y2h21bp;2p;1p;3p;4g005:j2;Tg005Zj1:Tg00<cj33Tg00@Dj12Tg00@ij11Tg00ANj19Tg00Alj26Tg00:jj44Tg003Ej35Tg00Bij10Tg007bj27Tg00>5j38Tg001JR0g008YR1';R2#:R3P2f0R49301g00D>#2#1#1#1#9'6X22f1R0P4C4A5204#0%00%04'7581eX13X03P0P4O2X13W0o"). Qed.
Lemma N4_app Y1 Y2 : N4 (Y1 ++ Y2) = N4 Y1 + N4 Y2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02Y1h12Y2h21bp;2p;1p;3p;4g005:j2:Tg005Zj19Tg00<cj33Tg00@ij11Tg00ANj18Tg00Alj27Tg00:jj45Tg003Ej34Tg00EAj10Tg007bj26Tg00>5j32Tg001JR0g008YR1':R2#9R3P2f0R49301g00D>#1#1#8'7X22f1R0P4C5A4204#0%00%04'6521eX13X03P0P4O2X13W0o"). Qed.
Lemma LRX_cons p n X c : LRX ((p, n) :: X) c = (if negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c) then 1 else 0) + LRX X c.
Proof. unfold LRX. rewrite zcount_cons. reflexivity. Qed.
Lemma LRX_app X1 X2 c : LRX (X1 ++ X2) c = LRX X1 c + LRX X2 c.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02X1h12X2h21ch32xbp;2p;1p;3p;4g005:j2<Tg005Zj1;Tg00<cj32Tg00F5j21Tg00FRj1:Tg00G0j17Tg00Alj23Tg00Gnj24Tg00:jj45Tg003Ej36Tg00HLj20Tg007bj28Tg00>5j39Tg001JR0g008YR1'<R2#;R3P2g00I@f0R49201R0'1#:%70f1R0'3'4X32f2R5P0C5A6250/0410541004'8591eX21X13X03P5P0P4O3X21X13W0o"). Qed.
Lemma n63X_cons p n X : n63X ((p, n) :: X) = (if MMAP_THRESHOLD <=? n then 1 else 0) + n63X X.
Proof. unfold n63X. rewrite zcount_cons. reflexivity. Qed.
Lemma n63X_app X1 X2 : n63X (X1 ++ X2) = n63X X1 + n63X X2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02X1h12X2h22xbp;2p;1p;3p;4g005:j28Tg005Zj17Tg00<cj32Tg00F5j21Tg00:jj46Tg003Ej33Tg00J?j10Tg007bj24Tg00>5j35Tg001JR0g008YR1'8R2#7R3P2g00I@f0R49201'1X22f1R0P4C6A3204#0%00%04'4551eX13X03P0P4O2X13W0o"). Qed.
Lemma R63X_app X1 X2 : R63X (X1 ++ X2) = R63X X1 + R63X X2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h02X1h12X2h21lh32xbh41zp;2p;1p;3p;4p;6p;5g005:j2>Tg005Zj17Tg00<cj3;Tg00F5j2:Tg007bj21Tg00K4j1<Tg0000j42Tg003Ej36Tg00=@j10Tg00>5j33Tg008?j29Tg00>Oj28Tg004\j65Tg00?Hj5=Tg00L0j14Tg001JR0g008YR1'>R2#7R3%71R4P2P1g00C^P1g00I@f0R59;01R0':g00Le,10g00MX'1#<g00Dcn0100000020000X32R0f1R6C2R7P2P1P0P5C2R8561R9%05P2P1P0f2C2#0%07R:'1R;531X24P1%08,1:R:A315;X41191:%091878E5P2P1P0A6265R8C2P2P1P0P6P5D=E5%48%46%45'1531eX13X03P6P5O2X13W0o"). Qed.
Lemma LRX_nonneg X c : 0 <= LRX X c.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Xh11ch22xbp;2p;1p;3g005:j2:Tg005Zj19Tg00<cj30Tg00F5j21Tg00FRj18Tg00G0j12Tg00Alj23Tg00Gnj24Tg00;ej35Tg00HLj26Tg00NMj27Tg001JR0g008YR1':R2#9R3g00I@f0R49001R0'1#8%20f1R0'3'4X22=520g00Dc1604'7eX11X03P0P4O2X11W0o"). Qed.
Lemma n63X_nonneg X : 0 <= n63X X.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Xh12xbp;2p;1p;3g005:j26Tg005Zj15Tg00<cj30Tg00F5j21Tg00;ej34Tg00J?j12Tg00NMj23Tg001JR0g008YR1'6R2#5R3g00I@f0R49001'1X12=424g00Dc%24'3eX03P4O1W0o"). Qed.
Lemma N24_nonneg Y : 0 <= N24 Y.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Yh11bp;2p;1p;3g005:j29Tg005Zj18Tg00<cj32Tg00@Dj11Tg00@ij10Tg00ANj17Tg00Alj23Tg00;ej34Tg00Bij15Tg00NMj26Tg001JR0g008YR1'9R2#8R3f0R49201g00D>#1#0#0#0#7'3X12=424g00Dc%54'6eX03P4O1W0o"). Qed.
Lemma N4_nonneg Y : 0 <= N4 Y.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h01Yh11bp;2p;1p;3g005:j28Tg005Zj17Tg00<cj31Tg00@ij10Tg00ANj16Tg00Alj22Tg00;ej33Tg00EAj14Tg00NMj25Tg001JR0g008YR1'8R2#7R3f0R49101g00D>#0#0#6'2X12=324g00Dc%44'5eX03P4O1W0o"). Qed.

Lemma bc_kv l : 0 <= l -> bc (4 * (l + 1)) = (if l =? 5 then 1 else l).
Proof.
  intros Hl. unfold bc. destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia.
Qed.

Lemma bigb_kv_le l : 0 <= l -> bigb (4 * (l + 1)) <= 5 * (if l =? 5 then 1 else l).
Proof.
  intros Hl. unfold bigb, MMAP_THRESHOLD, IB, UNIT. destruct (Z.leb_spec 131052 (4 * (l + 1))); [|destruct (l =? 5); lia].
  destruct (Z.eqb_spec l 5); [lia|]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (4 * (l + 1) + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * (l + 1) + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Lemma hist_Y : forall Y, YW Y ->
  0 <= BC Y /\ N24 Y <= BC Y
  /\ LRX Y 0 <= N4 Y + BC Y
  /\ LRX Y 1 <= BC Y
  /\ (forall c, 2 <= c < 48 -> LRX Y c * lmin c <= BC Y)
  /\ n63X Y * 32762 <= BC Y
  /\ R63X Y <= 5 * BC Y.
Proof.
  induction Y as [|[p n] Y IH]; intros HW.
  - unfold BC, N24, N4, LRX, n63X, R63X, zcount, zlen. cbn. splits; intros; lia.
  - apply Forall_cons_iff in HW as [Hn HW]. cbn [snd] in Hn. specialize (IH HW). destruct IH as (I0 & I1 & I2 & I3 & I4 & I5 & I6).
    rewrite BC_cons, N24_cons, N4_cons, !LRX_cons, n63X_cons, R63X_cons.
    destruct Hn as [-> | (l & Hl & ->)].
    + (* [comment removed for export] *) change (bc 24) with 1. change (size_to_class 24) with 1. change (MMAP_THRESHOLD <=? 24) with false.
      change (24 =? 24) with true. change (24 =? 4) with false. change (bigb 24) with 0. change (1 =? 0) with false. change (1 =? 1) with true. cbn [negb andb].
      splits; try lia. intros c Hc. rewrite LRX_cons. change (size_to_class 24) with 1. change (MMAP_THRESHOLD <=? 24) with false. cbn [negb andb].
      replace (1 =? c) with false by (symmetry; apply Z.eqb_neq; lia). specialize (I4 c Hc). lia.
    + rewrite bc_kv by lia. pose proof (bigb_kv_le l Hl) as HB.
      replace (4 * (l + 1) =? 24) with (l =? 5) by (destruct (Z.eqb_spec l 5); destruct (Z.eqb_spec (4*(l+1)) 24); try reflexivity; lia).
      replace (4 * (l + 1) =? 4) with (l =? 0) by (destruct (Z.eqb_spec l 0); destruct (Z.eqb_spec (4*(l+1)) 4); try reflexivity; lia).
      destruct (Z.leb_spec MMAP_THRESHOLD (4 * (l + 1))) as [Hbig|Hsmall]; cbn [negb andb].
      * (* [comment removed for export] *) unfold MMAP_THRESHOLD in Hbig. destruct (Z.eqb_spec l 5); [lia|]. destruct (Z.eqb_spec l 0); [lia|].
        splits; try lia. intros c Hc. rewrite LRX_cons. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with true by (symmetry; apply Z.leb_le; unfold MMAP_THRESHOLD; lia). cbn [negb andb]. specialize (I4 c Hc). pose proof (lmin_pos c ltac:(lia)). nia.
      * pose proof (kv_class_len l Hl Hsmall) as [Rc Lc]. set (c0 := size_to_class (4 * (l + 1))) in *.
        replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false in * by (symmetry; apply Z.leb_gt; lia).
        assert (U : 4 * (l + 1) + IB <= UNIT * size_class c0) by (pose proof (size_to_class_ok (4 * (l + 1)) ltac:(lia)) as [_ U]; exact U).
        assert (HBIG : bigb (4 * (l + 1)) = 0). { unfold bigb. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite HBIG.
        assert (GEN : forall c, 2 <= c < 48 -> LRX ((p, 4 * (l + 1)) :: Y) c * lmin c <= (if l =? 5 then 1 else l) + BC Y).
        { intros c Hc. rewrite LRX_cons. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb andb]. fold c0.
          specialize (I4 c Hc). pose proof (lmin_pos c ltac:(lia)). destruct (Z.eqb_spec c0 c) as [<-|NE]; [|destruct (l =? 5); lia].
          destruct (Z.eqb_spec l 5) as [->|N5]; [exfalso; subst c0; change (size_to_class (4 * (5 + 1))) with 1 in Hc; lia| nia]. }
        destruct (Z.eqb_spec l 5) as [E5|N5].
        -- (* [comment removed for export] *) assert (E1 : c0 = 1) by (subst l c0; reflexivity). rewrite E1 in *.
           change (1 =? 0) with false. change (1 =? 1) with true. subst l. change (5 =? 5) with true in *. change (5 =? 0) with false. cbn [negb andb]. splits; try lia. exact GEN.
        -- replace (l =? 5) with false in * by (symmetry; apply Z.eqb_neq; lia).
           destruct (Z.eqb_spec l 0) as [E0|N0].
           ++ (* [comment removed for export] *) assert (Ec : c0 = 0) by (subst l c0; reflexivity). rewrite Ec in *. subst l.
              change (0 =? 0) with true in *. change (0 =? 1) with false. cbn [negb andb]. splits; try lia. exact GEN.
           ++ assert (B1 : (c0 =? 1) = true -> 3 <= l).
              { intros E. apply Z.eqb_eq in E. rewrite E in Lc. change (lmin 1) with 3 in Lc. exact Lc. }
              replace (l =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. splits; try lia.
              ** destruct (c0 =? 0); lia.
              ** destruct (c0 =? 1) eqn:E1; [specialize (B1 eq_refl)|]; lia.
              ** exact GEN.
Qed.

(* [comment removed for export] *)
Definition AMBZ (Z0 : list (bptr * Z)) : Prop := (length Z0 <= 3)%nat /\ Forall (fun b => 0 <= snd b <= 2^26 + 64) Z0.

Lemma amb_counts : forall Z0, AMBZ Z0 -> (forall c, LRX Z0 c <= 3) /\ n63X Z0 <= 3 /\ R63X Z0 <= 3 * (2^26 + 8192).
Proof.
  intros Z0 [Hl HF]. 
  assert (G : forall Z1, Forall (fun b => 0 <= snd b <= 2^26 + 64) Z1 -> (forall c, LRX Z1 c <= Z.of_nat (length Z1)) /\ n63X Z1 <= Z.of_nat (length Z1) /\ R63X Z1 <= Z.of_nat (length Z1) * (2^26 + 8192)).
  { induction Z1 as [|[p n] Z1 IH]; intros HF1.
    - unfold LRX, n63X, R63X, zcount, zlen. cbn. splits; intros; lia.
    - apply Forall_cons_iff in HF1 as [Hn HF1]. cbn [snd] in Hn. destruct (IH HF1) as (A1 & A2 & A3). cbn [length]. rewrite Nat2Z.inj_succ.
      splits.
      + intros c. rewrite LRX_cons. specialize (A1 c). destruct (_ && _); lia.
      + rewrite n63X_cons. destruct (_ <=? _); lia.
      + rewrite R63X_cons. assert (bigb n <= 2^26 + 8192); [|lia]. unfold bigb. destruct (_ <=? _); [|lia].
        rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
        pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  destruct (G Z0 HF) as (A1 & A2 & A3). splits; [intros c; specialize (A1 c); lia| lia| nia].
Qed.

Lemma AMBZ_cons p n Z0 : AMBZ Z0 -> (length Z0 <= 2)%nat -> 0 <= n <= 2^26 + 64 -> AMBZ ((p, n) :: Z0).
Proof. intros [Hl HF] Hl2 Hn. split; [cbn; lia| constructor; [exact Hn| exact HF]]. Qed.
Lemma AMBZ_nil : AMBZ [].
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Hist ()) [] "h07__arithh14__ffh28__varmaph35__with41bp;2p;1p;3p;4p;7p;<g005:j2OTg00Phj17Tg002ej2@Tg00W3j12Tg01KVR0j28Tg00<cj3LTg00NMR1j23Tg00@ij10Tg00ANj11Tg00@Dj16Tg01L0j2<Tg007bj2:Tg00`Gj29Tg000Lj3NTg008?j24Tg005Zj1KTg00QHj1HTg00Qfj1ETg00RDj1ATg00Roj25Tg00d[j4BTg00fMj7?Tg00SRj2CTg00T4j2DTg00>5j3>Tg00T`j3FTg00U?j4GTg01Rjj4=Tg01T[j2ITg01HPj4JTg01Phl<;Tg01QMg008YR2P0g017KP1g01Qlg00nPR1g00DcR0f3f2R3f1R4f0R5M<;p=Mg001JR6/O2R7%77R8'@%21#2#2R9'8R:AL625R6,30g00D>R;#0R<#1%6;R;#0#6#0#1'<%0<#0#0#0#0#1':,36'9X47R6=N781819%1;R;,30R11420P9P;142;CMg00mDR9#7%K9%H2%E2%A2R9g00j2g00jQR8P8g00k1R8P21520g010O152;CBg00l8F?1C98P5P3g00C^R8g00n0R9'41D53=>89dAF204CGb1b2b3P1P5b0C=P:e1I76CJo"). Qed.

