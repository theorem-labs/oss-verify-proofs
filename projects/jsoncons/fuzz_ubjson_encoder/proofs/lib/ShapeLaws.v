(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import CatSim ShapeAlg Spec.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ShapeLaws () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg?is_prefix_app_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgCis_prefix_app_splitC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimBis_prefix_app_monoC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_altC13~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~C47Corelib4Init5Logic3iffC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic7and_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws<t_alt2_assocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8t_eq_symC13~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws>t_emit_has_nilC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List7map_appC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec1WC13~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List9app_assocc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws5W_appC13~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_alt_wallC13~~~C47Corelib4Init6Specif9proj1_sigC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnK47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg=t_emit_nil_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws5W_nilC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9exit_codeC13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws>t_exit_has_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws<t_emit_W_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLawsAexit_code_and_255C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt2_comm : forall A B : TSet, t_eq (t_alt2 A B) (t_alt2 B A).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h11Hh21Ah31Bh42trp;1p;2p;3p;6p;4p10000p4p710R0p1000Mp4p710R1p8p1000kp4p70R2p1001Yp4p710p8P2p1002lp4p710p8P2P0p8P2p1004Cp4p710p8P2P1p8P2p1005=p4p710p8P2p1006Qp4p710p8P2p1006np4p7210p8p1007Kp4p711p1008Wp4p710p8g009`j19Tg00:@j20Tg00:Zj32Tg00;4j31Tg00;Nj65Tg00;jj48Tg00<Ej33j24Tg00=Oj26Tg00=hj27Tg00?0R2g00@8#9f2R1f0R0O1R3f1R4P0O1R5'0R6P1P4O1R7f3R8P4O1R9'0R:[1053R51097R3[P9P7P:P8P1O1R8f4P1O1R:;20X09A18:0X07P0E5X16P7P9P3A2:80X07A1:80X09P0E5X15C8A3140A3410'6eW414401404'7eX32W2o"). Qed.

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Hh12H0h21Ah31Bh41Ch52trp;1p;2p;3p;6p;4g009`j19Tg00:@j20Tg00;4j33Tg00:Zj31Tg00;Nj64Tg00;jj48Tg00<Ej22j35Tg00=Oj26Tg00=hj27Tg00?0R0g00@8#9f3R1f0R2O1R3f2R4P2O1R5'0f1R6P2O1R7'0R8f4R9P6O1R:P1P6O1R;P4P6O1R<'0R='0R>[1057,03R310:;R;/0<R7[P;P<P>f5R>P4O1R5P9P4O1R?P1P4O1R@,0?RA,05f6P1O1RBP>P1O1R>P9P1O1R9'0RC;32X05A3>9291BCX0?P2E4X1;A1?@2915AX1<P2E4X08P:P=P7105?R7A35?273@X1:P?P@107@10B>R7A1B>2739X0?A1792X0@P2E4X1=P2E4X03C81214?5621246R3=512'6eW512321262,24'7eX40X30W2o"). Qed.

Lemma t_alt2_idem_eq : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) A.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h12H1h22H3h32H2h41Ah51Bh61Hh72trp;2p;1p;6p;3p;4p;5g00=hj22Tg009`j19Tg00=Oj20Tg00:@j21Tg00;Nj68Tg00;4j37Tg00;jj44Tg00@nj53Tg00<Ej35j26Tg00?0R0f1R1f0R2'2g00@8#9P1P2O1f3R3P2O1R4f2R5P2O1R6'0f4R7P1O1R8P7P5O1R9[R:P3P1O1R;f5R<P5O1[118;/08f6R8P3O1R;\9P<P3O1,1;R9f7R=P7O1R>[P8P7O1R?,1>\;P>P?P>P4P=P<O1P4f9P8O1R=P2b1b0X2>P6f8R>P<O1R<P7P2O1P>P8O1R8P1b3b0X2?P2E8X09P6P?P6P<A7=82b1b2X0;C4W3X1:P2D3b0A5352/04eW71651/25eW6X50W4o"). Qed.

Lemma t_alt2_idem_eq_r : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) B.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h12H2h22H3h32H1h41Ah51Bh61Hh72trp;2p;1p;6p;3p;4p;5g00=hj22Tg009`j19Tg00=Oj20Tg00:@j21Tg00;Nj68Tg00;4j37Tg00;jj44Tg00@nj53Tg00<Ej35j26Tg00?0R0f1R1f0R2'2g00@8#9P1P2O1R3f3R4P2O1R5f2R6P2O1R7'0f4R8P1O1R9P8P6O1R:[R;P4P1O1R<f5R=P6O1[119</0<f6R<P4O1R9\:P=P4O1R:,19R9P<P8O1R>[f7R?P8O1R@/1>\:P@P>P>P5P?P=O1R?P5f9P<O1RAP1b3b0X2@P7f8RBP=O1P8P2O1PBP<O1R<P2b1b0X2>P2E8X09P3P@P5P?A7A<1b1b2X0:C4W1X3;P2D3b0A5462/07eW71661/21eW6X50W4o"). Qed.

(* [comment removed for export] *)
Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Hh12H0h21Ah31Bh42trp;1p;2p;3p;6p;4g009`j19Tg00:@j20Tg00;4j33Tg00:Zj31Tg00;Nj64Tg00;jj48Tg00<Ej22j35Tg00=Oj26Tg00=hj27Tg00?0R0g00@8#9f2R1f0R2O1R3f1R4P2O1,03R3'0R5f3R6P4O1R7P1P4O1R8'0R9[1079R:\3P7P9P9f4R;P1O1R<P6P1O1R=;32X17P<P=10<=R>f5P6O1R?P;P6O1R6;32X0<A1?62X0=P2E4X19P2E4X05P7P8P:A3<>2X17A1<=291<>X18P2E4X03C81214=512A5142'6eW41242R2,24/72eX30W2o"). Qed.

Lemma t_alt2_congr_l : forall A A' B : TSet, t_eq A A' -> t_eq (t_alt2 A B) (t_alt2 A' B).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h12H3h22H1h32H2h41Ah52A'h61Bh71Hh82trp;2p;1p;3p;6p;4p;5g00=hj27Tg009`j1:Tg00=Oj21Tg00:@j20Tg00;4j36Tg00:Zj35Tg00;Nj64Tg00;jj49Tg00@nj58Tg00<Ej33j22Tg00?0R0f2R1f1R2'7g00@8#:P2f0R3O1f4R4P3O1R5f3R6P3O1R7'1f5R8P2O1R9P8P1O1R:[R;P4P2O1R<f6R=P1O1[P6P2O1R>,0910<>'1f7R>P6O1R<\:P8P6O1R:,0<R<P>P4O1R9P=P4O1R?'0R@[P=P6O1/0:R:f8RAP4O1RB/0?RC[PBP?P@P7PAP8O1RAP7f:R7P=O1P7P>O1f9R7P>O1R@;62b2b0X1BP>P8O1RB=5A3X1?P3E4X0<P9P?PCP1P3O1P7P8O1R8P5P7P=O1f;P>O1?6@2b3b0X19A58B3X1?P3E4X0:C9W3X2;P3D8b0A3413A3613'1eW812621212'7eW7X60X50W4o"). Qed.

Lemma t_alt2_congr_r : forall A B B' : TSet, t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A B').
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h12H3h22H1h32H2h41Ah51Bh62B'h71Hh82trp;2p;1p;3p;6p;4p;5g00=hj27Tg009`j1:Tg00=Oj21Tg00:@j20Tg00;4j36Tg00:Zj35Tg00;Nj64Tg00;jj49Tg00@nj58Tg00<Ej33j22Tg00?0R0f1R1f0R2'7g00@8#:P1P2O1f3R3P2O1R4f2R5P2O1R6'1f4R7P1O1R8P7P5O1R9[R:P3P1O1R;f5R<P5O1[P<P1O1R=/0810=;'1f6R=P3O1R;\9f7R9P3O1R8/0;R;f8R>P7O1R?P=P7O1R@'0RA[P<P3O1,08R8P9P7O1RB,0?RC[P?PBPAf9RAP<O1RDP9P<O1RE;62X1?P4PEP4PAP=O1f;P9O1R4PAP9O1;51b2b0X1BP2E4X0;P?P@PCP>P<O1R<=6D2X1?P6P<P7P2O1P>P=O1f:P9O1=541b3b0X1@P2E4X08C9W3X2:P2D8b0A3732A3752'1eW812351231'7eW7X60X50W4o"). Qed.

(* [comment removed for export] *)
Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Ah11Bh21Cp;2p;3g00<Ej20Tg00AKj32Tg00B\j31Tg00?0R0f2R1f1R2'0f0R3'01023,01A212331X20X10W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Hh12trh22H0h32H1h41Tp;1p;3p;2p;6p;4g00Chj1:Tg009`j19Tg00DHj30Tg00:@R0j21Tg000Mj68Tg00:Zj37Tg00;jj44Tg00<Ej33j26Tg00=Oj25Tg00=hj22Tg00?0f0R1g00@8R2#:R3O1%92R2A0213f2R4P1O1R5'1R6f3R7f1R8O1R9[A0283R:/19\5P0P:P9f4R0P4O1R;P1A0243P2P3f6P1O1X12P0P7P1E8W0P1O1P1X0;P1O1n200100000021000010000X36A7:91X05C4g00DbR:?341/55eW116:8/28eW2W4o"). Qed.

Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Hh12trh22H0h32H1h41Tp;1p;3p;2p;6p;4g00Chj1:Tg009`j19Tg00DHj30Tg00:@R0j21Tg000Mj68Tg00;4j37Tg00;jj44Tg00<Ej33j26Tg00=Oj25Tg00=hj22Tg00?0f0R1g00@8R2#:R3O1%92R2f2R4P1O1R5A0213'1R6f3R7f1R8O1R9[A0283R:,19\5P0P9P:f4R0P4O1R;P1P1X0;P1O1A0243P2P3f6P1O1X12P0P7P1E8W0P1O1n200100000021000010000X36A79:1X05C4g00DbR:=341/55eW1168:/28eW2W4o"). Qed.

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Th13evsh23tr'p;1p;3p;2g009`j19Tg00Chj18Tg00Ekj30Tg006Qj31Tg00DHj37Tg00Faj22Tg00G<j23Tg004Cj24Tg00;4j35Tg00GVj36Tg00@8R0#9R1g00?0%80R2f1R3500f2f0R45109712P3P4O1'2X21,31140335A6342eW0W1o"). Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h04codeh12fsp;1p;2p;3g00H`j10Tg00IEj17Tg00Icj12Tg00JFj21Tg00Chj16Tg00K<j35Tg00K\j23Tg00Loj34Tg00N9#0#0#0#0#0#0#7#2g000kg00@8R0f1R1f0R2'1%60R035g00Db'3A4120eW1W0o"). Qed.

Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01Ah11Bh21Hp;1p;3g00Chj12Tg00;4j31Tg00<Ej30Tg00?0R0f1R1g00@8#2R2O1R3f2R4P2O1f0713A0412eW2X10W0o"). Qed.

(* [comment removed for export] *)
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "p'0h03tr'h11Hh22trh32H0h42H1h52Hph61Th71ei001xp;1p;3p;2p;4p;6g009`j1GTg00Chj1FTg00DHj34Tg00FaR0j20Tg00:@R1j28Tg00G<R2j26Tg00;4j3>Tg00N^j2=Tg00;jj49Tg00O8j4ETg00:Zj3<Tg000Mj6;Tg00GVj27j3CTg00<Ej3Dj2ATg00=Oj2@Tg00=hj2BTg00Ekj3?Tg006Qj3:Tg00@8R3f1R4f0R53?p=2f3R6f2R7A:34534p=31645,87p=1A:345p=5%G3R8g00?0P5%F3R3O11256R9P8P4f4R:P5C3R;A4853R<'0X08718P6P5O1,0;X089198R9'8R;124:R=P8P7f5R>P5C3R?P:P5O1'0X08718R@[10?<X0891=8R=/8@\9P1P=P@127>R?P8P6f6RAP5C3RBP>P5O1'0X08718RCP510B<X0891?8P1126AP8P:f7R1P5C3/0<X08,6812:1R?P8P>f8RBP5C3RDP1P5O1'0X08718P512>BP8PAf9REP5C3RFPBP5O1'0X08,68;>5X5?P5O110D<X08,68P2P810F<X0812AEP8P1f:R1P5C3PEP5O1'0X08718P5P8PBf;RBP5C3/0<P0P8PEf<REP4C3A4843f=R0,21P8PBf>R1P5C3P0P5O1'0X08718P5P8PBP1P6C3P8f?RB/5:A48>3fAR0,24fBR</55RA9487P0P5O1RF'0X08718[X28A48:3P8P31505R:/2015<4=48A/0FX08718X08f@RF/53RA/2F1503=48:PFP5O1'0X08RF,68P8PFP3A48AAPBP3O11=8AP1C9CE3<P>P5E;W1PEP5E;W1P4P5O2n2001000000120000000W1X08P4P5O2n2001000000121100000W1P5O1n200100000021000011000W1P5O1P5X1CP5O1n200100000021100010000X4;A<=@5X19C9g00DbR9,761767;D5AC675'@eX2817791774R7'A/B7eW3W6W7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01ah11bh22chp;1p;2p;5p;3g00H`j10Tg00IEj14Tg00Icj15Tg009`j12Tg00ORj29Tg00P8j18Tg00Pnj57Tg006Qj33Tg00QJj21Tg00DHj36Tg00RKg00N9#0#0#0R0#4#5R1#2R2P1g00@8R3%00#0#0#4f2R0'9#8f1R4f0R5D7%23A3145,101104110553336eX12W0W2o"). Qed.

Lemma W_nil : forall ch, W ch [] = [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02chp;1p;2g009`j12Tg00Chj11Tg00N^j20Tg00RKg00@8R0#2%10'0W0o"). Qed.

Lemma t_emit_W_app : forall ch (a b : list byte) (T : TSet),
  t_eq (t_emit (W ch a) (t_emit (W ch b) T)) (t_emit (W ch (a ++ b)) T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "p'0h03tr'h11Hh22Hph32b'h42trh51lh62HTh71Th81ah91bh:2chh;4tr''i001xp%0p;1p;2p;5p;3p;4p;6g00H`j1ETg00IEj1STg00Icj1QTg009`j1HTg00QJj20Tg00GVj2>j3FTg00=hj2ITg00G<R0j24Tg00:@R1j28Tg002lj5RTg00FaR2j2:Tg00;4j3DTg00DHj39Tg00N^j2CTg00;jj4?Tg00O8j4BTg00:Zj3ATg000Mj6<Tg00Rij4GTg001Yj5PTg005=j5OTg00=Oj2NTg00B\j3MTg006Qj3=Tg00SGj3LTg00Ekj3JTg00@8R3f1R4f0R53=p=1f4R6f3R7f2R8==3439/:5p=2AJ3781445'8p=3AJ345p=5A=3459978p=71845,:8p=@1445,88p=KA9784/:5p=6A=384==35p=;g00RKg00N9#E#E#E#S#QR9#HR:g00?0%H3R;1078R<1074R='1R>1067R?1068R@/>4RA'>1>54'IX5;1>>5R>1>=5,><R<P511?@R@P;P;P4f5R=/06RB10=7RC'1RDP5P8P5O1D2X0;C3RE154BS00P;P8f6RF/0=RGP5P510F6RHP;P;P4f7RI/0=RJP5P6P5O1RKD2X0;C3D2X0;,4;S01'8[P5P?P;P;P4PBP5P5PCP;P;P4PHP5P7P5O1RCD2X0;C3D2X0;C3RB154DRDP;P811GHRHP5PCD2X0;,4;RC'8[P1PDPC158GRGP;P710IFRCP5P5PJP;P;P4f8RD/0FRLP5P=P5O1RMD2X0;C3D2X0;,4;RN'8P5158HRHP3PCPJP7P5DRP7PCP;P;P610DIROP5C7RP155LRQ':X3;C3P1156ORRP;P=f9RS/0DRTP5C7RU10SIRV,55RW':X3;,4;15=TRXP;PFf:RY/0SRZP5C7R[10YDR\,55R]P;P4f;R^/0SR_P5PDP5O1D2X0;,4;3@R`X0;7K;P515FZP;PI10^YRaP5C7Rb155_RcP;P4f<Rd/0YRe/15S02PSP5O1S03C6X0;,4;3@X0;,4;;D5X2XP5O11:[]X3;,4;P0P;1:bcX3;PIPaP;P;PD10d^RcP5P5PeP;P;P4f=Rb/0^R]P5PYP5O1S04D2X0;C3D2X0;C3P5P;PS10bdR[P5C7RX155]Rf':P2P;PYf>Rg/0bRhP4C710gdRi,54P^f?Rj/0gRkP;P;Pdf@Rl/0jRm/15RnP510lgRoP;P;P4fARp/0jRq/15S05PgP5O1RrC6X0;C3RsC6X0;C3P5P;PdPmP7C7P;10plRt/16fBRu/0lRv,5=RwP4fCRx/0uRyP;P;P8fDRz/0xP5P510zuR{P;P;P4fER|/0xS06P5PuP5O1D2X0;C3D2X0;C3[X4;156q10upR}/1=R~/5}P;11yFPyP5P510xpRxP;P;P411{5S07PpP5O1S08C6X0;C3D2X0;Rp,4;P;PpP=A9;~~P;PFPxP5PlP5O1RlD2X0;,4;Rp,8w1C;~ADwp5C?CB3AW2PbP5E<W1P4P5O2n2001000000121000000W1X3;P4P5O2n2001000000121100000W1P5O1n200100000021000011000b2W2P5O1P;P711CJRpP5PKD2X0;,4;RKP0P;P;P611OLROP5PMD2X0;RMP;P4P\P5PIP5O1RLD2X0;,4;9@UWX0;9KR;P5P;PFA;Z\5PLC6P2P;PI11a_P4C7PDP4O1PDPcP;P;P4PiP5P^P5O1D2X0;,4;9@XfX0;C3P5P;PS11[]R]P7C7P;A;hi6PdP=O1RfP4PmP;P;P8PtP5P5PqP;P;P411v5RXPjP5O1RLC6X0;C3D2X0;C3[X4;P^P6O110jbRj=;k=R\/5kP;11moRZ/1FRRPnPsC6X0;Rs,4;P;Ps11j=Rs11ksRn99;\15sjRWP;11oF11o5RUPbP5O1RwC6X0;R~,4;R{'8P;P\A9;R5X5;1C;\PnP3PkPjP=CGE<P;P~P=A9;ssPf1C;sP5C?CB9AW{C?CB3AW6PYP5E<W1P4P5O2n2001000000121000000W1X0;P4P5O2n2001000000121100000W1P5O1n200100000021100011000X1EP1Q00Q0118HKP5157p14;MP3PCPJP7P5DP3DX2GP5O1P0P;P;P4PVP5PFP5O1RGD2X0;,4;9@PQX0;P6POP;P;P=A;TV5PGC6X0;C3P5P2P;PIPaP4C7P4P_P;P;P8Q02Q03C6X0;C3PD11ceP;P;PSP]P5Q04D2X0;C3P5P;PSP[P7C7P;11h615=jRhP;PFPUPwC6X0;,4;Rw'8P4PZP;P;P811tqRU/15R[PrC6X0;C3[X4;P6PiP;P;P=PjP5PdP5O1D2X0;C3P1PhPw11mFPZP;P;11tIRZP[PrC6X0;C3P515Fo15ZUP;11}DRZ11}vR}P5PLD2X0;,4;P3PtPIPqP5DO3DW2P5O1P;PIQ05PrC6X0;,4;P0P;P;PDPXPLC6X0;PZP}P;P;11ySA;yx5PlC6X0;C3P5P;PYQ07Q08C6P2P;P^Q06P4C7PuP4O1fFRu/0|R^/1d10uz,1^P;P;fGR^/0uRd/1b10^|R2=;d5PzP5O1C6X0;C3P5P;PbP2P7C7P;fHR2/0u/16PuP=O1RufJRbfIRz'0Rd/1410b2Rl,1dRxP;P;fKRy/0bRb/1810yz=;b5P2P5O1C6X0;C3[X0;P|P6O110z2R210z^Rz/1='1R6112zR|'5P;11lF,1dPxP5P^P5O1D2X0;Rd,4;P;PdP=P;11|=R|P;P5PxPFP^PFO1D2X5;A9;||Pu1C;|P5C?P6P3P2PzP=CGE<CB3AW6PgP5E<W1P4P5O2n2001000000121000000W1X;;P4P5O2n2001000000121100000W1P5O1n200100000021000011000W1PYP5E<W1P4P5O2n2001000000121000000X1`X0;P4P5O2n2001000000121100000X1NP5O1n200100000021000011000X1BC?AF@45AF?A5'NeX4;1I><e3MA=984,07AL784E<W7X9:W8W:o"). Qed.

(* [comment removed for export] *)
Lemma t_alt_W_wall : forall ch (bs : list byte) (K : TSet),
  K [] -> (1 <= length bs)%nat ->
  t_eq (t_alt (fun i : wr_index bs =>
          t_emit (W ch (firstn (proj1_sig i) bs)) (t_emit (W ch (skipn (proj1_sig i) bs)) K)))
       (t_emit (W ch bs) K).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02HKh13Hnbh21Kh32bsh42chh51ih61np;1p;2p;5p;3g00H`j10Tg00IEj15Tg00Icj1<Tg009`j16Tg00Chj1BTg00TQj1=Tg00U0j24Tg00UPj22Tg00ORj2;Tg00Ujj5:Tg007Kj17Tg00Faj28Tg00W8j39Tg00WXj3ATg00QJj21Tg00X7j3@Tg00GVj23Tg008Wj2>Tg00=hj2?Tg00RKg00N9#0#0#0R0#5#<R1#6g00?0f0R2g00@8#BO1g00XU#=R3f2R4,41'2%00#0#0#5f4R0';f3R5P4f1P2D:%75R6f5R7g00Y4R812321417,22'8X68;92R2=A10'1A@120,17/35'3X56'>1105/34'?eW1W0W2W3W4o"). Qed.

(* [comment removed for export] *)
Lemma t_emit_W_nil : forall ch (T : TSet), T [] -> t_eq (t_emit (W ch []) T) T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02H0h11Th22chh31lp;1p;2p;6g00Chj11Tg009`j1:Tg00GVj23Tg00=hj22Tg00YSj29Tg00H`j10Tg00IEj18Tg00Icj14Tg00QJj25Tg00Zdj16Tg000Mj67Tg00RKg00?0f0R0g00@8R1#1R2O1%:1R1P2f2R2,30/22X31f1/90g00N9#0#0#0#8#4#1,52%62E7W0W1W2o"). Qed.

(* [comment removed for export] *)
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "p'0h03tr'h11Hh22trh32HAh42HBh52Hph61Ah71Bh81ei001xp;1p;2p;3p;4p;6g009`j1GTg00FaR0j20Tg00:@R1j21Tg00G<R2j25Tg00;4j3<Tg00DHj38Tg00N^j2@Tg00;jj4:Tg00O8j4=Tg00:Zj39Tg000Mj6?Tg00<Ej2>j3ETg00GVj3Fj2;Tg00=Oj2DTg00=hj2CTg00Ekj3BTg006Qj3ATg00@8R3f1R4f0R53Bp=4f3R6f2R7AA34538p=31145,07p=61545,17p=2AA345p=7%G3R3g00?0R81456R9P3P4f4R:P5C3R;P6P5O1R<P7P5O1R=36X03723R>144:R?P3P7f5R@P5C3RAP:P5O1RB'0X03723RC10A<X0392?3RD'1[10;<X03929310;=X039293'1R9A6AB<X03,53RA,1?[P1P?PA147@RAP3P6f6R?P5C3R<P@P5O1R='0X03723R;10<BX0392A3RE'1P5146?RFP3P:f7RGP5C3RHP?P5O1RI'0X03,53RJ'110H=X03,53RK,1FA<FJ53<X5AP5O1A6<=BX03,53R<P2P3A6HI=X0314:GRHP3P@f8R=P5C3RBPGP5O1RL'0X03,53RM'110BIX03,53RN,1H'1P5P3P?f9ROP5C3RPP=P5O1RQ;6LRRP0P3PGf:RSP4C3POP4O1P=P4O1'1f;RT,4=RUP3POf<RVP5C3RWPTP5O1'0X03723PSP5O1RX,0WX0392U3'1P5P3POPVP6C3P3f=RU/7:PUP@O1RWPVP@O1RY'1f?RZ,44R[f@R\/75R]9837R^PZP5O1R_'0X03723f>R`P5O1Ra,0^X0392[3'1[X23PVP:O1PTP:O1'1P1PWPY17Z?/4ZRY17\GRW=83]R]/0_X0372310]aX0392Y3'1P5P`P?O114W\RYfAR]/7=17]5Ra583R[P\P5O1R^'0X03Rb,53Rc'1Rd10[_X03R[,53Re,1YRfP3PbPGA83WWRbPZPGO11@3WRWP5C:C=99Yc3<W3P5O1PUP?O1P3P[PGPbP`PGO1PWP5C:C=99Ye99dfW4P5O1n200100000021000010000W1PSP5E?W1P4P5O2n2001000000121000000W1X03P4P5O2n2001000000121100000W1P5O1n200100000021000011000X1>P1PCPD11A<P5P1PFPJA6BLIX0392H3RBP514@=PRX03,53;<5X5HP5O1RHP2P310PQX0314?OP3PGPSP5C3POP5O1RG;6QX03723RQP5P3P=PTP5C3R=/0XP0P3POPVP4C3ROPTP4O114SUP3PTP`P5C3PUP5O1PVP5O136X03723RXP5P3PTP`P6C3RTP317Z:RRPZP@O1RZ144]P3P7fBP5C3P]P5O1;6^X03723RI[X23P`P:O117\@RJ/4\R\17]?=83a?6^_X03R^,53R_P3P^P@A83JJRaP`P@O1R`,1ZR]1@3JRJA<Z`5C:C=39W3PVP5E?W1P4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000X1MP5O1n200100000021000011000X1;P5O1P1PFPKPBP5PHP2P310PLX03PQP510=GP0POPSP4O1PXP5P3PRPI\`X23PUP:O1P3P^P@PaP]PJA9Z`5C:C=99\_W4PVP5E?X1TP4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000X1NP5O1n200100000021000011000X1EP5O1n200100000021100011000X19C:1>74=F651;671;64;E5'DeX231>45,;71;741;75'>'CeX78W6W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_code_and_255 : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = exit_code c.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h01zh11Hh22H0h32Hah47__arithh54__ffh68__varmaph75__with84__x1h96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?1cp;1p;2p;3p;4p;7p;8p;6g00H`j13Tg00[nj1<Tg00\Lj20Tg00FaR0j2;Tg00Icj1:Tg00DHj38Tg00\hj24Tg00]Rj3RTg00IEj1ETg00ORj2?Tg00^6j16Tg00^[j3LTg00_@j27Tg00_^j2CTg00`Dj2ITg00`aj2[Tg00aAj2HTg00aij3FTg00Chj1ZTg009`j1YTg00bMj2XTg00bkj1WTg00cIj1VTg00d4j2UTg00dWj2=Tg00e:j1QTg00e\j3DTg00f?j2OTg00N^j2NTg00faj2PTg00gMj3MTg00glj4STg00h^j3TTg00iAj1eTg00i_j1dTg00j=j3cTg00j`j3JTg00kLj2GTg00l;j3bTg00lij1aTg00n2j2^Tg00nNj4KTg00o9j7]Tg00o]j7\Tg010Aj8_Tg000Mj6`Tg010eR1f0R2'^p=1g00RKR3f1R4;82p=2P3P4g011CP2CKp=@P4g011jR5g012IR6P6g012iR7P2g013IF]p=5P3P4g013iP2CKp=Bf2R8P5P6P6P7P4P2F\p=Af3R9P5P6P6P7P8P4P2G_p=>P3f4R5P9P8P4P2E`p=9%12g00N9R:#3R;#3#3R<#3#3#3R=#3#3#<R>,02R?';g014PR@%:2RA%:4RBP0%:8?84214981494'2RC[14841482'2%:9?884[RD%:5?898\CAR842P2n2001000000120000000W<W;W=PD^<B^;A^=@P2%E=R@1?@8RA%6:#6#6#6#6#6#6#<RB,?@RD5L@RCPA14@ARE14@DRF'71?@9,4@,22X031C@8RG172F/22X031C@BRH1C@9RI/72/2IX03P8172H/22X03PB1792/29X03%<;R;%<<RI'IRJ,[81229X031H;I101;RK%1IRL101J[[%1;RMg014nRNAF;I4UW3%1J\N^3MP0%15RO105>R5f5RP#1RQ10PJ';P9f6#1RRf7/0>RSg015JRT#ZRU%YTRT1X34RV%W3RW%V3RX1U3:R:1=3>'@,5XRY%Q6R6PX1=31RZ/B:,5XR[P61=3;R\%E<5D3,@:,5X9AX[C>C>1OX7R7P2P8g0166R<g016VR]'N1P28=8<]dAM314CSR]b5b6b7X83%14R<%18R^108J';[\?^83P2f9P4P8O3R_b4W2W1P4P2O2n2001000000120000000b9b:9T8J%eI,78P0P^108>PLP410P>PUPT%d3R>PW1=3I,BZ,5XP7P]b5b6b7PLP2b4W2X1OP4P2O2n20010000001200000009c8ID9PH%<=R=,H;RH%1=1I;=RI,01[\KRKAF;=4VNX3MR=%1I\N^3MRMP0POP5%1B10BI';RNP9PUPTP>PW1=3BR>,BZ,5XAD3\@R\,@>,5X5AXP7P]b5b6b7PNP2b4X2SX1RP4P2O2n2001000000120000000b9b:9J@BD9PGPHPKP=PMP0POP510PI,;QP9PUPTPVPWPXPYP6PXP[P61@:\,5X9AX[C>C>P7P]b5b6b7X83108I,;^\<\?^83P_b4X2SX1RP4P2O2n2001000000121000000b9b:9J@8D9PF1G@BD9PE1G@8D914@CAb@ADD9O4b1%:@1?@4=L@D%a438eW>X?3o"). Qed.

(* [comment removed for export] *)
Lemma t_die_unfold : forall msg fs, t_die msg fs = t_emit (W 2 msg) (t_exit (exit_code 2) fs).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02fsh13msgp;1p;2g00H`j10Tg00IEj19Tg00Icj12Tg009`j11Tg00[nj18Tg00QJj27Tg00lij13Tg00Loj24Tg00GVj25Tg00N^j26Tg00N9#0R0#0#0#9#2#1g000kg00?0%80R0f1'7%30f0'4'5'6W0W1o"). Qed.

(* [comment removed for export] *)
Lemma exit_leaf_eq : forall c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs)) (t_exit (exit_code c) fs).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) ["FPX_1"] "h02Hch11bh21ch32fsp;2p;1p;3p;6g00n2j2CTg00H`j10Tg00[nj13Tg00\Lj28Tg00Faj2BTg00IEj16Tg00Icj17Tg00lij14Tg00Chj1<Tg00QJj2;Tg00Loj22Tg00GVj29Tg00=hj2:Tg0176j2ATg018Ij3@Tg00ORj25Tg00^6j11Tg00^[j3>Tg019Zj2?Tg000Mj6=Tg00RKg000kg010ef1R0'Cg00N9R1#0#0#0R2#0#0#0R3#0#0#3,80'B%63R3#7R4f2R5#4R6%31R7%62#7#<';f0R2/25'9f3#4/25':X1412601A605@71535%11#1#1#1#1#1#1#3,535>31?52E=W0W3W2o"). Qed.

End FPX_1.
