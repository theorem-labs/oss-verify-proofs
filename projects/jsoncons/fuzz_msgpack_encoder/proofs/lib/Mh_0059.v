(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require SFModel. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module WdWkKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require SFModel. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.SFModel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025.WdSfBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025.WdSfMul OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025.WdSfConv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdWkKit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_00257WdSfMul9exp_fieldC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC47Corelib4Init5Logic6eq_symI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib7Mh_00258WdSfConv?lxor_sign_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec9SoftFloat6SIGN64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4bool02C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3mulC56Stdlib6ZArith6BinInt1Z7land_wdC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC56Stdlib6ZArith6BinInt1Z6b2z_wdC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z8add_commK46Stdlib;setoid_ring<Ring_polynom5PExpr05c59OSSVerify5KrLib7Mh_00597WdWkKit;addc_land_lC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_mult_compC46Stdlib;setoid_ring6Ncring>ring_plus_compC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc59OSSVerify5KrLib7Mh_00597WdWkKit<land_W_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib7Mh_00258WdSfBase=lor_shift_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_comm".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac show_regs := let v10 := getreg 10%Z in let v11 := getreg 11%Z in let v12 := getreg 12%Z in let v13 := getreg 13%Z in
  let v14 := getreg 14%Z in let v15 := getreg 15%Z in let v16 := getreg 16%Z in let v17 := getreg 17%Z in
  idtac "a0=" v10; idtac "a1=" v11; idtac "a2=" v12; idtac "a3=" v13; idtac "a4=" v14; idtac "a5=" v15; idtac "a6=" v16; idtac "a7=" v17.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc=" pc end.
Ltac show_cond := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => idtac "cond=" c end.
Ltac zrun := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_Zlit pc; zstep end).
Tactic Notation "br_true" tactic(t) := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let H := fresh "BR" in assert (H : c = true) by t; rewrite H; cbv iota; clear H end.
Tactic Notation "br_false" tactic(t) := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let H := fresh "BR" in assert (H : c = false) by t; rewrite H; cbv iota; clear H end.

Open Scope Z_scope.
Lemma w_shl1_shr49 h : 0 <= h < 2 ^ 63 -> Z.shiftr (Z.land (Z.shiftl h 1) 18446744073709551615) 49 = h / 2 ^ 48.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah16__sat1h24__x1h31hh47__arithh54__ffh66__sat0h78__varmaph85__witp;2p;1p;3p;4p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij20Tg002Ej1OTg002jj18Tg003Hj11Tg003mj2NTg004Jj22Tg004fj27Tg005Aj2?Tg005ij3=Tg006Mj2<Tg006nj23Tg007Hj1:Tg007hj19Tg008Hj2MTg008fj1LTg009Dj1KTg009oj26Tg00:Rj2ATg00;5j45Tg00;`j1@Tg00<>j3BTg00<aj7>Tg00=Ej1CTg00=gj8DTg00>Kj2ETg00>mj2FTg00?Yj3GTg00@3j3HTg00@Rj4ITg00ADj2JTg00BBj7;Tf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEF;p=4g00DeR5g00ECR6/04g00EaR7#O#8R8%17#1#1#1#1R9#8R:'NR;,24'7R<1?8:1268R=106:126;[R>[1068R?g00FFR@A=8:0UW0106;\@^0?P0g00Fb1<68'3P=eO1P>g00GHR>#:%9>1M50%L5%K5R>P1P2P2P3P>P1P2P2P3P51656g00H41A57R7C5,4>P5P7g00H[1658%@95B5C5,4>F>R9%C2P9GD1E>3P4f2R>g00IBR3g00IbR9'31F4>=G39dAH560CIb5b7b8X251060120;'7\<^25P4f5f4O2b4b1b6b1,J0UX35P4O1W3o"). Qed.
Lemma swrap32_small x : -2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah16__sat1h24__x1h31xh47__arithh54__ffh66__sat0h78__varmaph85__witp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej12Tg002jj15Tg003Hj13Tg003mj2=Tg00JBj1:Tg001ij20Tg004Jj21Tg004fj24Tg00;`j19Tg005Aj2>Tg005ij3<Tg006Mj2;Tg006nj27Tg007Hj1RTg007hj1QTg008Hj2PTg008fj1FTg009Dj1ETg009oj2DTg00<>j3CTg00J_j2BTg00:Rj2ATg00;5j46Tg00<aj7@Tg00=Ej1?Tg00=gj8GTg00>Kj2HTg00>mj2ITg00?Yj3JTg00@3j3KTg00@Rj4LTg00KBj1MTg00L0j3NTg00BBj7OTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFOp=8g00DeR5g00EaR6#2R7#5R8%36#3#3#3R9#5R:'=R;#:R</04114;'4R=%27#2#2#2#9R71>8:g00ECR>/18R?10>:11>;[R@[10>8RAg00FFRBA<8:0UW010>;\B^0AP0g00Fb1;>8'7P?eO1P@g00GHR@#R%Q@1P50%F5%E5R@P1P2P2P3P@P1P2P2P3P51D58%995C5R9,B5g00H41A56R6C6,8@P5P6g00H[P9C6,8@F@R9%?2P9GG1H@3P4f2R@g00IBR3g00IbR9'71I4@=J39dAK5>0CLb5b7b8X2510<0110;'4\=^25P4f5f4O2b4b1b6b1%M7R7#:/001107'4e7N0UX35P4O1W3o"). Qed.
Lemma land_W_small x : 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h12Hah27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h81xh91zp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij21Tg002Ej10Tg002jj16Tg003mj2=Tg004Jj22Tg004fj28Tg00L]j2CTg00?Yj37Tg005Aj2?Tg005ij3>Tg006Mj2<Tg006nj29Tg007Hj1:Tg007hj1TTg008Hj2STg008fj1RTg009Dj1OTg009oj24Tg00:Rj2NTg00;5j43Tg00;`j1BTg00<>j3ATg00<aj7@Tg00=Ej1DTg00=gj8ETg00>Kj2FTg00>mj2GTg00@3j3HTg00@Rj4ITg00M=j3JTg00M`j1KTg00N>j2LTg00N\j1MTg00O:j3;Tg00O]j6PTg00BBj7QTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFQp=5g00DeR5g00ECR6/14g00EaR7#0R8#6R9%08#0#0#0#0R8#6R:'=R;,24'8R<P51C0;f2R=9754X951?9:R>1269R?116:R@126;[RA[RB1169RCg00FFRDA>9:0UW1RE116;\D^1CRCP0g00Fb1<69'9P?eO1R?PAg00GHRD#:RF%TDRD1S50%R5RG%O5RHP1P2P2P3PHP1P2P2P3P51456R1g00H4RI1N57R7C3,5HP5P7g00H[1459%B85A5C3,5HF@R8%D2P8GE1FH3R3P4P=g00IBR8g00IbR2'91G4==782dAH560CIR2b3b5b6X751160120;'8\<^75P4f5f4O2b2b0b4b09J0;%K:,L0P>PBPEPCP?PAPFPD%M5PGP5P1PI145:C3,5HP3P2b3b5b6P@P4b2b0b4b09;0:EPUX85P4O1W8o"). Qed.
Lemma land_M32_small x : 0 <= x < 2 ^ 32 -> Z.land x 4294967295 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h12Hah27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h81xh91zp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij20Tg002Ej11Tg002jj16Tg003mj2=Tg004Jj22Tg004fj28Tg00L]j2CTg00?Yj37Tg005Aj2?Tg005ij3>Tg006Mj2<Tg006nj29Tg007Hj1:Tg007hj1TTg008Hj2STg008fj1RTg009Dj1OTg009oj24Tg00:Rj2NTg00;5j43Tg00;`j1BTg00<>j3ATg00<aj7@Tg00=Ej1DTg00=gj8ETg00>Kj2FTg00>mj2GTg00@3j3HTg00@Rj4ITg00M=j3JTg00M`j1KTg00N>j2LTg00N\j1MTg00O:j3;Tg00O]j6PTg00BBj7QTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFQp=5g00DeR5g00ECR6/04g00EaR7#1R8#6R9%18#1#1#1R8#6R:'=R;,24'8R<P51C0;f2R=9754X951?9:R>1269R?106:R@126;[RA[RB1069RCg00FFRDA>9:0UW1RE106;\D^1CRCP0g00Fb1<69'9P?eO1R?PAg00GHRD#:RF%TDRD1S50%R5RG%O5RHP1P2P2P3PHP1P2P2P3P51456R1g00H4RI1N57R7C3,5HP5P7g00H[1459%B85A5C3,5HF@R8%D2P8GE1FH3R3P4P=g00IBR8g00IbR2'91G4==782dAH560CIR2b3b5b6X751060120;'8\<^75P4f5f4O2b2b0b4b09J0;%K:,L0P>PBPEPCP?PAPFPD%M5PGP5P1PI145:C3,5HP3P2b3b5b6P@P4b2b0b4b09;0:EPUX85P4O1W8o"). Qed.
Lemma unsigned_neg64 e : -2 ^ 64 <= e < 0 -> bv_unsigned (Z_to_bv 64 e) = e + 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h12Hah27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h81eh91zp;1p;2p;3p;4p;8p;6p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej10Tg002jj17Tg003mj2DTg00JBj1@Tg001ij22Tg004Jj25Tg004fj29Tg00;`j1CTg00P;j2BTg00Paj26Tg00?Yj34Tg00Q>j2>Tg00L]j2<Tg005Aj2^Tg005ij3VTg006Mj2UTg006nj2:Tg007Hj1RTg007hj1QTg008Hj2JTg008fj1ITg009Dj1HTg009oj2;Tg00<>j3ETg00J_j2FTg00:Rj2GTg00;5j43Tg00=Ej1ATg00Q[j3KTg00=gj8?Tg00>Kj2LTg00>mj2MTg00@3j3NTg00@Rj4OTg00M=j3PTg00N\j1=Tg00R>j6STg00Rbj4TTg00SCj6]Tg00S_j2\Tg00TEj2[Tg00Toj2WTg00O]j6XTg00BBj7YTg00<aj7ZTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFYp=1f2R5P1P2P2P3P0P4FZp=8g00DeR6g00EaR7#0R8#7R9%08#0#0#0#0R8#7R:'DR;#@/24g00ECR<,54'9R=P6%C8R8/B0R>165;9464X96R?P6%77R@/>;,60/<;P?160;R?1^9:RA15<9RB12<:15<;[RC[RD12<9REg00FFRFAV9:0UW1R:12<;\F^1EREP0g00Fb1U<9':PBeO1RBPCg00GHRF#RRG%QFRF1J60%I6RH%H6RIP1P2P2P3P61;69=E68R9,F6g00H4RJ1G67R7C3,1IP6P7g00H[RK1;6<RLC3,1I58I%A2P6PLPJAK679R7C3,1IP6P7PKP9C3,1I58IG?1LI3RKP4P5g00IBR7g00IbRJ':1M45=47JdAN6<0CORJb3b5b6X7612<?15?;'9\=^76P4f5f4O2b2b0b4b07P;1<0;P0P@P;PAPDP:PEPBPCPGPF%=6PHPIP1P2P2P3P6P9g00U^PLC3,1IESPKPJb3b5b6A46;<g00VE[P4b2b0b4b0CTE]A46>?e1\80,[81W80EXUX86P4O1W8o"). Qed.
Lemma unsigned_small64 e : 0 <= e < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 e) = e.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah16__sat1h24__x1h31eh47__arithh54__ffh66__sat0h78__varmaph85__with91zp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij21Tg002Ej10Tg002jj15Tg003mj2<Tg004Jj22Tg004fj29Tg00;`j1BTg00P;j2@Tg00?Yj33Tg005Aj2=Tg005ij3;Tg006Mj2:Tg006nj24Tg007Hj1STg007hj1RTg008Hj2QTg008fj1FTg009Dj1ETg009oj26Tg00:Rj2ATg00;5j47Tg00<>j3?Tg00<aj7CTg00=Ej1DTg00=gj8>Tg00>Kj2GTg00>mj2HTg00@3j3ITg00@Rj4JTg00M=j3KTg00S_j2LTg00TEj2MTg00Toj2NTg00O]j6OTg00BBj7PTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFPp=8g00DeR5g00ECR6/14g00EaR7#0R8#5R9%08#0#0#0#0R8#5R:'<R;,24'9R<P5%B8R8/@0R=f2R>9354X951=9:1269R?116:126;[R@[1169RAg00FFRBA;9:0UW0116;\B^0AP0g00Fb1:69'4P?eO1P@g00GHR@#S%R@1Q50%F5%E5R@P1P2P2P3P@P1P2P2P3P51656g00H41A57R7C7,8@P5P7g00H[1659=?58C7,8@FCR9%D2P9G>1G@3P4P>g00IBR@g00IbR3'41H4>=3@3dAI560CJb5b7b8X251160120;'9\<^25P4f5f4O2b4b1b6b19K0;A35=0e1L80,M81N80EOUX35P4O1W3o"). Qed.
Lemma land_mask48_lit x : Z.land x 281474976710655 = x mod 2 ^ 48.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h01xh17__arithh24__ffh38__varmaph45__witp;1p;2p;4p;7p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g003Hj1BTg002Ej10Tg002jj13Tg007Hj12Tg007hj1ATg00N\j1:Tg008fj15Tg009Dj14Tg009oj21Tg00;5j46Tg00BBj77Tg00>Kj28Tg006nj29Tg00>mj2@Tg00?Yj3?Tg00@3j3;Tg00@Rj4<Tg001ij2=Tg00O:j3>Tg00DeR0f0R1g00Ea#B#0#0#0#0#3R2g00GHR3#2%A3%:0%50%40R3g00Bfg00CER4P4g00CeR4P0g00ECR5,10g00H41102C6g00DEF71834P1f2R4g00IBR3g00IbR6'91@14=?36df19;05C<b2b3b41=52P1b13>X00P1O1W0o"). Qed.
Close Scope Z_scope.

Open Scope Z_scope.
Lemma swrap_srl x k : 0 <= x < 2 ^ 32 -> 1 <= k <= 31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr x k.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h14__x1h22Hah34__p1h47__arithh54__ffh66__sat0h78__varmaph85__with96__sat3h:6__sat5h;6__sat6h<1Hh=4__p2h>6__sat2h?6__sat4h@6__sat7hA4__x2hB4__x3hC1khD1xhE1zhF2HkhG2Hxp;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej17Tg002jj1>Tg003mj21Tg004Jj23Tg004fj24Tg001ij22Tg003Hj1@Tg00;`j1DTg00Vbj2?Tg00WBj2LTg00?Yj3CTg00Wij2KTg00JBj1rTg005Aj2;j4STg005ij3<Tg006Mj2`Tg006nj2MTg007Hj1]Tg007hj1\Tg008Hj2GTg008fj1YTg009Dj1XTg009oj2ETg00:Rj2HTg00=Ej1WTg00>Kj2VTg00>mj2UTg00@3j3TTg00@Rj4RTg00N\j1QTg00XFj4tTg00Xgj2sTg00<>j3FTg00J_j2qTg00YXj5pTg00Z?j2lTg00Zhj1JTg00[Gj2ITg00\0j3hTg00\Yj3NTg00]Bj2gTg00]nj3fTg00^Nj4eTg00^lj3aTg00Q>j2bTg00_Oj5cTg00`;j4dTg00`Vj3_Tg00O]j6OTg00a?j2^Tg00L]j2iTg00M=j3jTg00P;j2kTg00;5j4PTg00BBj7mTg00bAj6nTg00<aj7[Tg00=gj8ZTg00ECR0f0R1'2p=0%71#7#7#7p=91301p=8g00DeR2f1R3g00H4P1CPp=:P3g00BfR4g00CER5P5g00CeR6P1g00DEFmp=5P3P4P5P5P6P1Enp=Bf2R7P4P5P5P6P3P1F[p==f3R8P4P5P5P6P7P3P1GZp=6P2P3g00H[P1CPp=A%71#7p=o%03R4g00EaR9#7R:#>R;%9:R<#>R='1R>,33'4R?%>9R@/23RA%@9RB#@#@#@RC#>RD,23'4P2P8%D<RE1?18'Lf4RF/?85C2XE21?87RGP211;7RH,K8RI11;DRJ#rRK/21131J'4XE212KI13IJP8PH1;;=RL%8;RM%0=%8>[RN[RO%0;RPg00FFRQA<;=3UW2R=%0>\Q^2PRRP3g00Fb1`0;'MPMeRSO1RTPNp-0RUg00GHRV#]RW%\VRX1G23RY%Y2RZ%X2R[1E20R\1H29R]':,5[R^1B[8R_5=[%W5R5P^C61V[6R6P1P7g00IBR`g00IbRa'M1U17=C`adAT203CRR0b5b7b8X12W3%01Ra/43P4[^12^3UP1f7R`/3>P`f5RbO3b4b0b6b0P;P7PLPOP=PRPTPNPWPX%Q2PZ1E2;Rc,A\,5[P6P0b5b7b8PMP1b4b0b6b0R\PLPOP=PRPTPNPWPXPYPZP[1E2@Rd/:],5[Re==[_R_P5P^C6P6P0b5b7b8X12X3U12@1/43RfP4[^12^3UP1f6R4/2DP4PFO3Rgb4b0b6b0RhCSRiCt%0IPLPOP=PR11;b,s4%0411;4#0f8RI11;`'K#0[[1;;DRj%0D%8J[Rk\MRlA<;D3VQX2PRm%0J\Q^2PRn1;;If9Ro#0f:Rp,1;#8[\Mf;Rq=<;3VQX2P11;qRr#0\Q^2PPT%0p%8r[RrPFPSO1RsPkPIPSO1PNPWPXPYPZP[P^P5%DC9F2cRC,q2/:],5[C6P6P0b5b7b8X1212K3\a^12P1f?RKf>RI,1;'KPqO2b4b;b9b0b6b0b>b9b?b:b;b<P8PHPJPiP;P@P7P\PLPOP=PRPTPNPWPXPYPZP[P_P5PeC6P6P0b5b7b8X12X3UPA\f^12^3UPgb4b0b6b0Dp11;@Rg/2HPLPOP=PRPjPlPmPn1;;@%0@%8g[Rn\MA<;@3VQX2P%0g\Q^2P1;;oPr\Mf<RM=<;3VQX2P11;MRM#0\Q^2PPT%0q%8M[PsPnP`PSO1PkPpPSO1PN%o<#9#9#9#9#9#9#>,l2g00beR<#JRS#J#J,I25h21I2S1I2<5N25N2g00cD'g=fVWPXP21G27P31G28CePZP[%D99F2c1H2:R:':,5[P5P[1H2B,:d,5[1B[b5=[P5P[1B[4AF2cE,A],5[Rc5=[P5Aa2:C,A],5[C6C6C6P6P0b5b7b8X12XA2XB2X3UX=U12g312@8/4F137>,441bFJ,38[[[^12^A2^B2^3U^=UP1fARU#0f@RJ/2DPJ11;JPUf=PIPKO8b4b@b:b9b0b6b0b>b9b?b:b;b@b<DcCdPGA_87hEO'^1i8>PLPOP=PRPTPNPWPXPYPZP[A=[^cRcP5PcC6P6P0b5b7b8X12131>,4aP?[^12P1P`PbO2b4b0b6b09j8>EO1kE8/?7,LE=C2GeWFWGXC2XD2P3P1O2XC2XD2o"). Qed.
Lemma shiftr_range32 x k : 0 <= x < 2 ^ 32 -> 0 <= k -> 0 <= Z.shiftr x k < 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h14__x1h24__p1h37__arithh44__ffh56__sat0h68__varmaph75__with82Hah96__sat3h:4__x2h;4__x3h<1kh=1xh>1Hh?2Hkh@2HxhA6__sat2hB1zp;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej15Tg002jj1;Tg003mj2:Tg004Jj22Tg004fj28Tg00Wij2YTg005Aj2Hj4MTg005ij3FTg006Mj2NTg006nj2DTg007Hj1KTg007hj1qTg008Hj2CTg008fj1nTg009Dj1gTg009oj2ATg00:Rj2BTg00=Ej1XTg00>Kj2WTg00>mj2VTg00?Yj3UTg00@3j3STg00@Rj4RTg00N\j1QTg00XFj4OTg00YXj5LTg001ij2<Tg00Z?j2ETg00d0j2GTg00dQj4TTg00e2j2pTg00Zhj1>Tg00[Gj2=Tg00\Yj39Tg00]Bj2oTg00]nj3mTg00^Nj4kTg003Hj1hTg00e[j5fTg00;`j1eTg00<>j3bTg00^lj3_Tg00Q>j2`Tg00f?j5aTg00fkj5^Tg00`;j4cTg00Vbj2dTg00`Vj3]Tg00O]j6\Tg00;5j4ITg00BBj7[Tg00bAj6iTg00<aj7jTg00=gj8ZTg00\0j3lTg00ECR0f0R1'<p=0%51#5#5#5p=6g00DeR2f1R3g00H4P1CIp=7P3g00BfR4g00CER5P5g00CeR6P1g00DEF[p=4P3P4P5P5P6P1Eip=Jf2R7P4P5P5P6P3P1Fjp=@f3R8P4P5P5P6P7P3P1GZp=1P2P3g00H[P1CIp=?%51#5p=PAl231p=3%03R9g00EaR:#5R;#;R<%6;R=#;R>':R?,23R@'8P21:<7RA,Y8RB%01RC121?RD'8XB2%0B12B?P8PA1H<>RE120<RF%0>120?[RG[RH%0<RIg00FFRJAF<>3UW8R>%0?\JRK^8IRLP3g00Fb1N0<'DPFeRMO1RNPGp-0ROg00GHRP#KRQ%qPRR1C23RS%n2RT%g2RU1A20RV1B2:RW'7,4URX1JU8RY5@U%X5RZPXC11WU6R[P1P7g00IBR\g00IbR]'D1V17=U\]dAS203CRR]b4b6b7X12W218C3P9[^12^2OP1f7R\/2?P\f5R^O3b3b0b5b0P<P7PEPHP>PLPNPGPQPR%Q2PT1A2<R_,?V,4UP[P]b4b6b7PFP1b3b0b5b0R`PEPHP>PLPNPGPQPRPSPTPUPXPZPXC1P[P]b4b6b7X12P9\C^12P1f6RCf4RaO2b3b0b5b0RbCMRcCOPBP8P?P8PAP8PcP<P0P7P`PbDL%;:R`/<APEPHP>PL1H<^%0C1:<\,20[\Ff8RF=F<3VJX8I1:<FRA#0\J^8IPN%0\RJ120A[PaPMO1PG%5=#P#6#6#6#6#6#6#;,E2RMP21G2`P:1G20CT,p2g00beRA#>Rc#>#>RB,=2Rd'3'3%>B,=2RB1=2cRc,3d=92cRc'31E2<1=2ARA,3B'313Ac,3M13AA,3M592592592592g00cD'o=mPQPRP21C27P31C28CkPTPUPU%h:,B2,7V,4UR:PZ1B2;R;,?V,4UC1PZPUPU17V_,4UPZPUPUP4P5P5P6DfPZ%e=9b2_R_,7V,4UC1C1PZPU1A2`/7;,4UPZPUP:PZPU1JU^9@UXPZA_2;W,7W,4UC1C1C1C1C1P[P]b4b6b7X12X:2X;2X2O%071207[PK\I1<`8%0^%0a/8\1`C^,<^[[[[[^12^:2^;2^2OP1f;RC/2?f:R?1:<?PCP7P^P\PFf9O9b3b9b0b5b0bAb9b>DaPEPHP>PLPNPGPQPRPSPTPU1?W_,4UR_9@UYPZP_C1P[P]b4b6b7X12X2O183DP@[^12^2OP1PJP\P^O3b3b0b5b0D^Cc1d87A]87bE\X?9W@X<2X=2P3P1O2X<2X=2o"). Qed.
Close Scope Z_scope.

Lemma word_of_unsigned (w : bv 64) (z : Z) : bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h01zh12b1h22b2h31nh41wh51Hh62H0p;1p;2p;3p;4p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej13Tg00;`j1=Tg00gPj12Tg00TEj21Tg00?Yj30Tg00h3j3;Tg00S_j2:Tg00P;j24Tg00hWj26Tg00iJj37Tg00j6j45Tg00SCj68Tg00Toj29Tg00O]j6<Tg00Ea#3#3#3#3#3#3#=R0#2R1g00DeR2f1R3,10f0R4502g00jRR5%24R6%23R7g004ff2R8#2?034f3R9/181193502R:[11831184502%29?083[R;f4R<#2?098\:A;834P4n2001000000120000000W2W1W3P;^27^16^35P4P0P91:08R5P21408110<R<=024X02P21109R61404902<X02P21406P616099706C5P8P3E811051908E<O4b6W5X02X41P3P4O2W0W4o"). Qed.

Lemma lxor_sign_lit x : (0 <= x < 2 ^ 63)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah16__sat1h24__x1h31xh41Hh57__arithh64__ffh76__sat0h88__varmaph95__with:1zp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij20Tg002Ej1RTg002jj18Tg003Hj11Tg003mj2QTg004Jj22Tg004fj29Tg00Paj24Tg00?Yj3:Tg006nj23Tg00k0j2>Tg005Aj2<Tg005ij3;Tg006Mj2PTg007Hj1OTg007hj1KTg008Hj2FTg008fj1ETg009Dj1DTg009oj27Tg00:Rj2CTg00;5j45Tg00;`j1BTg00<>j3ATg00<aj7@Tg00=Ej1GTg00=gj8HTg00>Kj2?Tg00>mj2ITg00@3j3JTg00@Rj4=Tg00kNj2LTg00O]j6MTg00BBj7NTf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEFNp=6g00DeR5g00ECR6/04g00EaR7#R#8R8%17#1#1#1#1R9#8R:'QR;,24'9R<P5140;f2R=g00lSR>'49:54X:5140>,351>0>1<8:1268R>106:126;[R?[1068R@g00FFRAA;8:0UW0106;\A^0@P0g00Fb1P68'3P>eO1P?g00GHR?#O%K?1F50%E5%D5R?P1P2P2P3P?P1P2P2P3P51756g00H41C57R7C5,6?P5P7g00H[1758%B95A5C5,6?F@R9%G2P9GH1??3P4P=g00IBR?g00IbR3'31I4==:?3dAJ560C=b6b8b9X251060120;'9\<^25P4f5f4O2b5b1b7b1,L0EMW4X35P4O1W3o"). Qed.
(* [comment removed for export] *)
Ltac dtests :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => first [ rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia ]
  | |- context [Z.leb ?a ?b] => first [ rewrite (proj2 (Z.leb_gt a b)) by lia | rewrite (proj2 (Z.leb_le a b)) by lia ]
  | |- context [Z.eqb ?a ?b] => first [ rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia ]
  end; cbn [Z.b2z negb].
(* [comment removed for export] *)
Ltac bsolve :=
  rewrite ?bv_eqb_Z, ?bv_ltu_Z, ?bv_lts_zero_r; cbn [negb];
  repeat (rewrite lxor_sign_lit by lia);
  try (progress dtests);
  repeat (rewrite unsigned_small64 by lia);
  repeat (rewrite inr64_unsigned_lit by zrange);
  rewrite ?Z.lor_0_l, ?Z.lor_0_r;
  repeat (rewrite zb_lor_eqb0 by (first [lia | zrange_nonneg]));
  try (progress dtests); cbn [andb orb negb]; rewrite ?Bool.andb_false_r, ?Bool.andb_true_r;
  repeat (rewrite unsigned_neg64 by lia);
  first [ reflexivity
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Bool.negb_true_iff; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply Z.leb_gt; lia]
        | apply Bool.negb_false_iff; first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.leb_le; lia] ].
Ltac dbr := first [ br_true bsolve | br_false bsolve ].
Ltac zrunb := repeat (first [ progress zrun | dbr ]).
Lemma land_abs63 x : (0 <= x < 2 ^ 63)%Z -> Z.land x 9223372036854775807 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h12Hah27__arithh34__ffh46__sat0h58__varmaph65__with74__x1h81xh91zp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij21Tg002Ej1UTg002jj17Tg003Hj10Tg003mj2TTg004Jj22Tg004fj26Tg00L]j2ATg00?Yj38Tg005Aj2>Tg005ij3=Tg006Mj2;Tg006nj29Tg007Hj1STg007hj1RTg008Hj2QTg008fj1FTg009Dj1ETg009oj24Tg00:Rj2BTg00;5j43Tg00;`j1@Tg00<>j3CTg00<aj7DTg00=Ej1?Tg00=gj8GTg00>Kj2HTg00>mj2ITg00@3j3JTg00@Rj4KTg00M=j3<Tg00M`j1LTg00N>j2MTg00N\j1NTg00O:j3OTg00O]j6PTg00BBj7:Tf1R0g00BfR1g00CER2P2g00CeR3f0R4g00DEF:p=5g00DeR5g00ECR6/14g00EaR7#U#7R8%07#0#0#0#0R9#7R:'TR;,24'6R<P51A0;f2R=9854X951>8:R>1268R?116:R@126;[RA[RB1168RCg00FFRDA=8:0UW1RE116;\D^1CRCP0g00Fb1;68'9P?eO1R?PAg00GHRD#SRF%RDRD1Q50%F5RG%E5RHP1P2P2P3PHP1P2P2P3P51456R1g00H4RI1B57R7C3,5HP5P7g00H[1458%@95C5C3,5HFDR9%?2P9GG1HH3R3P4P=g00IBR9g00IbR2'91I4==892dAJ560CKR2b3b5b6X751160120;'6\<^75P4f5f4O2b2b0b4b09<0;%L:,M0P>PBPEPCP?PAPFPD%N5PGP5P1PI145:C3,5HP3P2b3b5b6P@P4b2b0b4b09O0:EPUX85P4O1W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zrun_to stop := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_Zlit pc;
  lazymatch pc with stop => fail | _ => zstep end end).
(* [comment removed for export] *)
Ltac bsolve2 := unfold bv_lts; rewrite ?signed_of_Z by lia; cbn [negb];
  first [ reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Bool.negb_true_iff; apply Z.ltb_ge; lia | apply Bool.negb_false_iff; apply Z.ltb_lt; lia ].
Ltac dbr2 := first [ br_true bsolve2 | br_false bsolve2 ].
Ltac zrunb2 := repeat (first [ progress zrun | dbr | dbr2 ]).
Ltac show_hyps := try (match goal with H : ?T |- _ => idtac H ":" T; fail end).
Ltac show_all := show_pc; let v2 := getreg 2%Z in idtac "sp=" v2; show_regs;
  let v5 := getreg 5%Z in let v6 := getreg 6%Z in let v7 := getreg 7%Z in let v8 := getreg 8%Z in let v9 := getreg 9%Z in
  let v18 := getreg 18%Z in let v28 := getreg 28%Z in let v29 := getreg 29%Z in let v30 := getreg 30%Z in let v31 := getreg 31%Z in
  idtac "t0=" v5; idtac "t1=" v6; idtac "t2=" v7; idtac "s0=" v8; idtac "s1=" v9; idtac "s2=" v18; idtac "t3=" v28; idtac "t4=" v29; idtac "t5=" v30; idtac "t6=" v31.

Open Scope Z_scope.
Lemma shr_pre32 x : 0 <= x -> Z.shiftr (x * 4294967296) 32 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah17__arithh24__ffh36__sat1h48__varmaph55__with61xh76__sat0h81zp;2p;1p;3p;4p;6p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij22Tg002Ej10Tg002jj15Tg00Q>j2OTg003mj2DTg00Wij2ATg00?Yj34Tg005Aj2>Tg004Jj28Tg005ij3;Tg006Mj2:Tg006nj29Tg007Hj1QTg007hj1PTg00N\j1NTg008fj1KTg009Dj1ETg009oj23Tg00;`j1CTg00<>j3BTg00;5j47Tg00R>j6@Tg00>Kj2?Tg00>mj2FTg00@3j3GTg00@Rj4HTg00mPj3ITg00Vbj2JTg00`Vj3<Tg00O]j6LTg00BBj7MTf0R0#0#0#0#0p=1%00#0p==f1R1g00BfR2g00CER3P3g00CeR4P0g00DEFMp=6g00DeR5g00ECR6/20P5g00Ea#0R7#1R8#0#=#1#1#1#1#1#1#5,O1R9%57R7%58R:'DR;'Af2R<9450X851>7:1867R=126:R>186;[R?[1267R@g00FFRAA;7:1UW0126;\A^0@P1g00Fb1:67'9P=eO1P?g00GHR?#QR=%P?R?%N5R@%K5RA%E5RBP2P3P3P4P51357%C85B5g00U^1356R8C7,6BE@1?B4R4P0P<g00IBR7g00IbR3'91F0<=473dAG561CHR3b2b4b5A45;6g00VE[P0b1b3b7b39I1;1J9:P=P?P@PAP5P8g00H4135:C7,6BP4P3b2b4b5P>P0b19<9:ELUX65P0O1W6o"). Qed.
Lemma mulhu_pre32 x y : 0 <= x -> 0 <= y -> Z.shiftr (x * 4294967296 * (y * 4294967296)) 64 = x * y.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah17__arithh24__ffh36__sat2h48__varmaph55__with61xh71yh81zh92H1h:6__sat1h;7fv_listh<8hyp_listh=3lmpp;2p;1p;3p;4p;7p;6p;:p;<p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij27Tg002Ej11Tg002jj16Tg00Q>R0j20Tg003mj2UTg00Wij2=Tg00?Yj33Tg00n1j1HTg00n[j29Tg007Hj1:Tg007hj15Tg00]nj3CTg00o;j2BTg00oej34Tg010Oj2ATg0119j1WTg011Wj3VTg006nj2?Tg012Aj1QTg012ij4PTg013Oj7OTg005Aj2MTg004Jj2<Tg005ij3LTg006Mj2ITg00N\j1JTg008fj1KTg009Dj1FTg009oj28Tg00;`j1NTg00<>j3ETg00;5j4@Tg00R>j6DTg00>Kj2RTg00>mj2STg00@3j3aTg00@Rj4`Tg00mPj3_Tg00SCj6^Tg00Vbj2]Tg00`Vj3\Tg00O]j6YTg014>l:ZTg014ol<[Tg00BBj7XTf0R1#1#1#1#1p=2%11#1p=Gg00DeR2g00ECR3f1R4g00PaR5P0g015\R6g00JBR7g0169R8g016VR9P1M:Zp=TP2P3f2R:P5P0P6P7P8P9g0177R9P4P1M<[p=>P4g00BfR7g00CER6P6g00CeR0P1g00DEFXp=;1734R5P2f3R;g00EaR<#1R=#1#2R>#G#2#2#2#2#2#2#6R?'0R@10:?'0RA%6=RB%6>RC'URD'=f4RE/0;RF9321X82%H2RG/9GRG#:%5G%:29C2;9C2E%52P9P1P41B2<R91B2=R=5421A2B%WC5V2542RG1A2?RH9429A42=H542RHg017fg00IBR=g00IbR9'?RI%6<R</T4g018B,92%Q2'9#5P2P8A><1GA><1HCPb==3=9dFOb;b<10;:/0D=32AR;eP;P210FD1=1Df5/0E532X821MBC1<3BR;173CR<1<3D[RH[173BRGg00FFR8ALBC4UW0173D\8^0GP4g00Fb1I3B'?P;eO1PHg00GHRH#:R;%5HRH%J2RG%K2R8%F2RJP7P6P6P0P2182B%N>5E2g00U^1823R>C@,;JED1RJ0R0P1P:PI1S1:=3=9dAa234C`R9b2b4b5A32D3g00VE[P1b1b3b:b39_FD10E?/0@P1E^b91]ACP;PHPGP8P2P>g00H4182CC@,;JP0P9b2b4b5P<P1b19\ACEYV5UX72X62P4P1O2X72X62o"). Qed.
Lemma ltu_land_range (c : bool) : 0 <= Z.land (Z.b2z c) 18446744073709551615 <= 1.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41ci001bp;1p;2p;3p;4p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g018jj1JTg003Hj10Tg002jj17Tg00N>j2FTg001ij22Tg004fj23Tg007Hj1=Tg007hj1;Tg00N\j1:Tg008fj19Tg009Dj1ITg009oj28Tg00>Kj2HTg006nj2ETg00>mj2BTg00?Yj3ATg00@3j3?Tg00@Rj4CTg00;5j4DTg00BBj7>Tg00<aj7GTf0R0#0#0p=@%00#0#0#0p=<%00#0#0#0#0#0#0#0p=1g00DeR1f1R2g00H4P0CDp=5P2g00BfR3g00CER4P4g00CeR5P0g00DEF>p=4f2R6P3P4P4P5P2P0FGp=6g00IBR4P4g00ECR3%J0g00EaR7#0#@#<#1#1#1#1#1#1#1#7'FR8'2%77R7,28'3P0g00GHR8#=R9%;8R8%:1R:%91R;%I1R<1813R=1817R>'5,4<R?15>>,4<361H<5R5P0P6g00IbR>,E41B06=A4>dA?132CCR2b1b2b31237R11277'3P0b0P9P8P:P;15==,4<=6<?P5P2b1b2b31233/31P0b0n0110000020000X44P0O1W4o"). Qed.
Lemma land_W_range e : 0 <= Z.land e 18446744073709551615 <= 18446744073709551615.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h17__arithh24__ffh38__varmaph45__with52Hah66__sat0h74__x1h81eh91Hh:6__sat2h;1zp;1p;2p;3p;4p;8p;6p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej11Tg002jj1:Tg003mj2DTg00L]j28Tg00M`j1RTg001ij29Tg004fj25Tg005Aj2BTg004Jj23Tg005ij3@Tg006Mj2>Tg006nj2<Tg007Hj1ZTg007hj1VTg00N\j1UTg008fj1QTg009Dj1MTg009oj24Tg00;`j1LTg00<>j3KTg00;5j47Tg00>Kj2CTg00>mj2ETg00?Yj3FTg00@3j3GTg00@Rj4HTg019Gj3ATg019nj2ITg008Hj2JTg00:Rj2?Tg00=Ej1NTg01:_j3OTg00=gj8PTg015\j2=Tg00N>j2STg00O:j3TTg00O]j6YTg00BBj7XTg00<aj7WTg00ECR0f0R1'9p=0f1R2g00BfR3g00CER4P4g00CeR5P1g00DEFXp=2g00DeR6P2g00H4P1C7p=6f2R7P3P4P4P5P2P1FWp=;P6g00EaR8#1R9#:R:%19#1#1#1#1R9#:R;'DR<,81R=%01R>%R;R?,91'5X;61B:;R@130:RA%0;RB130<RC[RD[RE%0:RFg00FFRGA@:;2UW5RH%0<RI\G^5FRFP2g00Fb1>0:'<PAeO1RAPDg00GHRG#ZRJ%VGRG%U6RK%Q6RL%M6RMP61460RNg00H[RO146:%L95K6R9C7'21CM5R:P1P7g00IBRPg00IbRQ'<1E17=FPQdAG602CHR0b2b3b4PCP1b1b0b6b09A1<%0=13=<'51I2<%02R=f3/8<#0\I[P@PEPHPFPAPDPJPG1J62PLPMP3P4P4P51?68R5,6N,2MR3P6P5POP9C7,2M5;M%N4%:8R8,469O69,65,2M9;M3GPP:P0b2b3b4X76131<,5>1=<8,92,5=[^76P1f6/8<f5O2b1b0b6b0b:b91S1?PJPGPKPL146;,6N,2MP:P0b2b3b4PBP1b19T1;EYX86P1O1X86o"). Qed.
Lemma addc_land_l a b : 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  Z.land (a + b) 18446744073709551615 + 2 ^ 64 * Z.land (Z.b2z (Z.land (a + b) 18446744073709551615 <? a)) 18446744073709551615 = a + b.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h06__sat1h14__x1h24__x2h37__arithh44__ffh54__p1h68__varmaph75__with86__sat0h96__sat2h:1ah;1zh<2H0h=4__p2h>4__x3h?4__x4h@1bhA2HahB1HhC2H1hD2H2hE2H3hF2H4hG2H6hH2zhhI1EhJ3H10hK2H5hL2H7hM2H8hN2H9hO2HbhP2HghQ2HlhR6__sat3hS1op%0p&0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej15Tg002jj1RTg004Jj21Tg004fj24Tg00Paj20Tg003mj2nTg00L]j22Tg01;Bj2<Tg018jj1?Tg00M`k10>Tg00N>j2_Tg01;_k206Tg001ij27Tg01<DR0j2~Tg00Q>j2@Tg005Aj2{Tg005ij3uTg019nj2PTg01<^j2YTg01=?j1qTg00Wij2QTg00?Yj3=Tg019Gj2^Tg01=Xj2aTg01>?j2VTg01>ej2UTg01?Kj2TTg006Mj2cTg006nj2STg00[Gj2bTg00Zhj1DTg00Z?k20=Tg00\0k30<Tg01@Jk10;Tg00d0k208Tg01@hj3]Tg00]Bj2\Tg01AQj2:Tg007Hk107Tg00]nj3NTg007hk105Tg008Hj2ZTg00N\k104Tg00^Nj4ITg008fk102Tg009Dk101Tg009oj2MTg003Hj1gTg00:Rj2OTg00;`j1}Tg00<>j3|Tg00=Ej1zTg00R>j6yTg00^lj3WTg00Q[j3LTg00>Kj2tTg00>mj2sTg00@3j3rTg00@Rj4wTg01B=j2xTg01B]j4eTg00O]j6FTg00M=j3fTg015\j2HTg01:_j3oTg00Rbk400Tg00SCj6mTg01C8k203Tg00O:j3hTg00\Yj3lTg00;5j4[Tg00BBj7iTg00<aj7kTg00=gk809Tg00bAk60:Tg00ECR1f0R2'7p=3%52#5#5#5p=v%52#5p=j%52#5#5#5#5#5#5#5p=Cg00DeR3f3R4f2R5f1R6'@'0;=2p=;1056==32p=XA=321p=J1b32p=EAl362p=9P5g00BfR7g00CER8P8g00CeR9P3P6g00H4P2C[g00DER:Fip=>P3P6g00H[P2C[p=GP6P7P8P8P9P2P:Fip=8P5P7P8P8P9P6P2Fkp=AP3P6g00U^P2C[p=KP4P7P8P8P9P5P6P2L09p=6g00IBR:g00IbR;7=2p=`P6P7P8P8P9P2J0:p=d1@62,05p=pA=362p=B%36R<g00EaR=#5R>#5R?#vR@#j#C#C#C#C#C#C#C#RRA,16S00'4S01Q01P31045RB%R>RC%R@RD'nRE'2RFP2PEf4RG,<2#?&0>DRH'_10G4RIC;X;3P31<F4#?RF/2E12IEPEP2PIC;X;3206BE11BE17EB'~P011IE17EIf5RI/0GR0/2ERJPE1<JI#?/2EP0C;P2110EP3f6RJ/0IRKP2PEf7RL,<2#?/2E10LJRMC;X;3P:g01CXRN%?2/2E,@ES02=XMMX@:1{CDRO111CRP%3DS03111ERQ[RR[RS%3CRTg00FFRUAuCD6UWARV%3ERW\U^ATRX1P1E1711121ERY#3RZ\W[1Y1E%JER[#qR\1Q1ER],@E/0Y9=31[1^1E11YE,4ZRZ\Q1a1E11E1R^11EY17Y1'4[1V1E%J]\[1U1E%JY\[g017fS041T1ER_eP_PGg00FbR_1c1E'SPQeS05O1S06PZP6PUf:RZP2P6O2X:TPW^:TS07f;R`1c1C,S_PPeRPO1PRg00GHR_g00beRa,b3Rb%DaRa#DRc#ERd,9b20=3A>0<3b%DcRc#DRe#DS08#ES09&0;=Rf-083Rg%EcRc5]3S0:'9'9g00cDRh'\':':A]3gd,9b%EeRe/9c%Ea/9bRa/\hRi':':,:b&07_Rj5N_3N&05_RkP3P31Z3GS0;P5&043RlCIP61Z34CI&023Rm&013Rn1M31Ro%g=,O3Rp5>n1M3C%}@5|3R@,Gp,8n5AnS0<%z8RCPnPnPnP7P8P8P91K@o,8nEyS0=PC1O3?9W3@=L3p,Ko,8nC6PC1O3=R?1O3>R85L3R7AW3@pRq5L3/K7,8nC6C61tn9R9P2P51S:;1s25#`dAr316CwRrb4b6b7X13X23X>3X?3%35Rs115E'4Rtg00VE\[Ru1@EIRv/0GRw9=31[1054RxPEPGPxC;[[^13^23^>3^?3P2P]PYfCR]fDRyPGPZO6b3b9b0bHb<f?f>'0RzPEPYPzC;ebFbEbDbCb<bBb8b0b9PKPE%?N/2EPKC;e1<KJRzA=:zN17LM[17JK1<ML==:N[1xKJPOPSPVPXP6PPO1RJPRp-0RNPjPkP31Z35S0>P6PlCIRzPmPnA>no81dnGRY5AnR{PCA>n?7C6P9Prb4b6b7X13X23W514<51065R<,76[^13^23^5NP2f9R|/1AR}P|PZPLO4b3b0b8b0CeEF12KER~POPSPVPXPJPR19da/\h=N_jRhPkPzPmPn1G7@,8nRaPCPnP{PCPnA>no?1dnIR{5AnPCA>no7=AnaC6C6C6P9Prb4b6b7X13X23X5NX=N1026Ra/1E14s414sI104GRs#311sE'4[[[^13^23^5N^=NP211ZAP}P|PZPGPLf8R}O7b3b0b8b09fKEEFWQP2O117E0P3ApKfE/2E1HMER0,B2X;31HKERdPOPSPVPXPJPRPhPkPzPmPnA>n@7S0?PCPn1M3ARh,G8,8n9AnYRYPCPn1G?h,8n9An{PCAo37@R{9>no1G{@,8n5AnC6C6C6P9Prb4b6b7X13X23X5NX=N17Ea115ARA,4414IA1HsERA#311AE'4[[[^13^23^5N^=NP2%3Z%3|P|PZPGPLP}O7b3b0b8b07fEP~PKPfPEPOPSPVPXPJPRPjPkPlPmQ0=P9Prb4b6b7PuP2b3b0b8b0H00Em1B~dP3P0P2PE1<2}#?/2E10}LRdC;X;3P:P;1HdER~Q02;XdX@:%R=R=/PE%3=12=ER:#3Rd\W[POPSPVPX10Z|RJ/PE%3Jf<RJ/0`/2E#3\W[1Y=E1Q=ERf,@E/0:,B=\\1^=E11:E,4dRd\Q1a=E11E:17:1'4\^1V=E%Jf\[1U=E1B:=\[Q041T=ERKePKfARKf@'0/YEfBRI/0KRa1QaE,@E12aE'0'B\\1^aE10]IRa/2ER\#311\E'4\Q1aaE10y]R]/2ERa,1E17a1'4\^1V]EfER]/0yRy/QE#J\[1UyEfFRy/0]R]/2E/B]\[Q041T]ER]eP]Q06fGR]/0yRy/2ER[#311[E'4P`Q05O1PdP5PUPKP2P6O2X:TQ07PIPPO1PRQ0:,9bQ09/9e/:i':,:b19bcQ08#D#EA]3ge'9/:i':,:b=N_j5N_PkP3Q0>P6P3Q0;P4PlCICIPmPnQ0<PCPnPnQ0=PC1M3=%g>,O39W3@=L3p'K,8nC6PCPnQ0?PCAL3{q/K7,8nC6C6C6P9Prb4b6b7X13X23X>3X?31B=w\u17ExAXAvs[[\t^13^23^>3^?3P2PfP:fLfMPGPKP]O7b3b9b0bHb<bG1HyEPEP:PyC;ebJbNbMbLbGbKbFbEbDbCb<bBb8b0b9bRP0PE%?;/2EPMC;e1<0LR;%`;11~}[110L1<~}#`[2030LPOPSPVPX10|}R}/PE%3}10`Z/2E#3\W[P5PPO1PRPjPkPzPmPnPYPC1G{?,8nC6P9Prb4b6b7X13X23X5NQ00,451H<E/16[^13^23^5NP2%3`P`PJP|O4b3b9b8b0b9CeEF12MEP2EFbIWPP2O1n200100000021100011000bS1_FHPjPkPlPm1M3D9>noP9Prb4b6b7Q03P2b3Rr9hFDEF1_BHAhBDrEFWOWAX@3X:3P6P2O2X@3X:3o"). Qed.
Lemma addc_land_r a b : 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  Z.land (a + b) 18446744073709551615 + 2 ^ 64 * Z.land (Z.b2z (Z.land (a + b) 18446744073709551615 <? b)) 18446744073709551615 = a + b.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "p'0h01yi001yh17__arithh24__x1h31ah41bh51xi011xh64__ffh78__varmaph85__with97fv_listh:8hyp_listh;5lemmah<3lmph=1zi022x'i032y'p;2p;1p;3p;6p;4p;:p;;p;9p;7p;8p;@p;<p-1R0g01D8R1p4p710p9P0p1000SR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g01DdR0p4p710p9g001ij2KTg002Ej10Tg002jj16Tg004Jj2HTg004fj2FTg00PaR2j22Tg00?Yj37j1@Tg01E^j1NTg003Hj11Tg00N>j25Tg003mj2fTg01;BR3j2=Tg018jj1;Tg00Q>R4j2<Tg01FNj2_Tg01@Jj1]TP1j29Tg01Foj6CTg01GPj2YTg01H=j4>Tg01Hdj1WTg01ISj4ATg01JJj3UTg01K@l:TTg01Kmj3STg01LMl;OTP0l9QTg01MHj2MTg00n1j1RTg00n[j2:Tg007Hj1?Tg007hj18Tg00]nj3LTg00o;j2JTg01Mjj3BTg006nj2vTg012Aj1tTg012ij4jTg013Oj7iTg008Hj2hTg008fj1eTg009Dj1dTg009oj2DTg00:Rj2cTg00;5j4GTg00<aj7bTg00=Ej1aTg00=gj8gTg00>Kj2`Tg00>mj2kTg00@3j3lTg00@Rj4mTg01NTj4nTg00O]j6oTg01OTl9\Tg01P<l:pTg01Pgl@qTg014>l:[Tg014ol<rTg00BBj7sTf0R0#0#0#0#0p=^%00#0p=V%00#0#0#0#0#0#0#0p=4%10#1p=x%10#1#1#1p=w%10#1#1#1#1#1#1#1p=3g00DeR1g00ECR5f2R6P2f1R7g015\R8g00JBR9P0g01QRR:M9\p=ZP1P5P6P2P7P8P9P0P:g01R;R;M:pp=XP1P5P0P2P7P8P9P6P:P;f3R;f4R:f5f6f7f8M@qp=PP1P5P7P2P4P8P9g0169R<g016VR=P0M:[p=uP1P5P6P2P4P8P9P<P=g0177R=P7P0M<rp=IP7g00BfR9g00CER8P8g00CeR2P0g00DEFsp=E1K57g00EaR>#0R?#0#^R@#V#4#4#4#4#4#4#4#6RA,H7'FRB12;6RC126;RD571P1%@1RE%N112:;RF%1>#x#w#3#3#3#3#3#3#3#6RG'5RH%6?%6@'fR@1=H;RI#;RJ/5GRK'<RL'212;:RM/5GRN1=N;RO#;RP/5GRQ,<@RR'2%6>RSP1P1P7P5P1P1P7P51_70RT#6RU%]TRTn011000003001010310103P1P1P7P5PTPUn011000003001010310103n011010003001010210102X01X51RUPEPHPNPFPMP0PGPG191GRMECRTPLPRP1P1^01AZSUE,Y1RRP1P1PEPRC>P4AXSUEP@191@PKPQPJPPg00IBRP^01RJ^51RQP1PJPEP1PPPE%@PREC>RKC>RUP1PJPKP1PPPE%WPCACA9UQUP3PHPNPTP;P;191;M:T9SIOPGPGPMECM;OM9PPFPF191FM9QW;1M;6P1PDA710FX=1%R1RF/:FRF#?%8F%?19L1:9L1;%81P=P0P71J1>R=1J1?R?5B1RFAB1?=R?g017fg00IbR=,vPRM1uS7g018B,:1%t1':#8P1P<AIS0FAIS0?Cjb<=7P=dFib9b:A71DCe15DGRD1=D6#;/5G,<@'2P6P;g00GHR@#?%8@1h17%e1%d1R@P9P8P8P2P@P9P8P8P2P11D15g00H41c1>R>CG,E@P1P>g00H[1D1ACG,E@FbR>%a8P>Gg1`@2P0P6PM1k06=7P=dAl157Cmb6b7b8X21R=1K501H0A'FPB[^21RAP0P;P7O2b1P=PAP0P:P6O2b1CnEoO2VBUX41X31P7P0O2X41X31o"). Qed.
Lemma shr32_land t : 0 <= t < 18446744073709551616 -> Z.land (Z.shiftr t 32) 18446744073709551615 = t / 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah17__arithh24__ffh34__p1h46__sat1h58__varmaph65__with74__x1h86__sat0h96__sat3h:1th;6__sat2h<1zp;1p;2p;3p;4p;6p;5p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej10Tg002jj17Tg004Jj24Tg004fj2:Tg003mj2@Tg00Wij2?Tg003Hj11Tg00N>j2cTg00?Yj3ETg007Hj1XTg007hj1VTg008Hj2UTg008fj1TTg009Dj1STg009oj28Tg00:Rj2OTg00;5j49Tg00bAj6LTg00=Ej1KTg00>Kj2JTg006nj2<Tg00>mj2HTg00@3j3MTg00@Rj4NTg005Aj2DTg005ij3ATg006Mj2QTg00N\j1RTg00;`j1BTg00<>j3CTg00XFj4eTg00^lj3dTg00Q>j2bTg00_Oj5aTg00`;j4\Tg01Rbj2YTg00Vbj2ZTg00`Vj3[Tg00O]j6WTg001ij2]Tg00BBj7^Tg00<aj7_Tg00=gj8`Tg00ECR0f0R1']p=2%01#0#0#0p=P%01#0p=I%01#0#0#0#0#0#0#0p=5%11#1p=G%11#1#1#1p=F%11#1#1#1#1#1#1#1p=3f1R2g00BfR3g00CER4P4g00CeR5P1g00DEF^p=6f2R6P3P4P4P5P2P1F_p==f3R7P3P4P4P5P6P2P1G`p=>g00DeR8P2g00H[P1C9p=;%21R9g00EaR:#0R;#PR<#0R=#I#5#5#5#5#5#5#5#7R>,41R?':P8%7;R;%7<R@'@RA,?2RB%1:#G#F#3#3#3#3#3#3#3#7,c11?6A5E8X<8%2B%7=RC,@;RD,4BP2PAp-0REg00GHRF#XRG%VFRF1U82RH%T8RI%S8RJP81880RKg00H4RL1O8:R:C9,6JRMPJP3P4P4P5P7ELR75=J%K4R4PMC>1JJ5R5P1P6g00IBRMg00IbR3'<1H16=EM3dAM802CNR3b2b5b6X78W31:92%22[^78^3EP1146>P6P2O3b11D;@R6140;R9%2@RM140ARN[RO[RP%2;RQg00FFRRAA;@2UW0RS%2A\R^0QRTP2g00Fb1Q0;'<P9eRUO1RVPOPGPF%R8RWPI188;RX%B<5C8R<,;K,6JP5P3b2b5b6PNP1b1b4b8b4RNCeP2PAPDPNP6PPPSPT1D;C%2C140D[R0\9AA;C2VRX0Q%2D\R^0QPVP0f4PUO1POPGPFPHPIPJ188>,;:,6J9=J7P4%B=9C8X9d8<,;:,6JC>P5P3b2b5b6X78X3E1:2?1bAD,42[^78^3EP1f8RE#2PEf7O3b1b9b4b8b4b;b9DaC\,YB1Z2@PGPFPWPIP8PKPL188@C9,6JP5P3b2b5b6PMP1b19[2@EWUX:8P1O1X:8o"). Qed.
Lemma shl32_small t : 0 <= t < 4294967296 -> Z.land (Z.shiftl t 32) 18446744073709551615 = t * 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h02Hah17__arithh24__ffh36__sat1h46__sat3h58__varmaph65__with74__x1h81th96__sat0h:6__sat2h;1zp;1p;2p;3p;4p;8p;6p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej11Tg002jj17Tg004Jj26Tg004fj2ATg003mj2@Tg00Q>j2>Tg003Hj10Tg00N>j2fTg00?Yj3HTg005Aj2CTg005ij3FTg006Mj2WTg006nj2BTg00Z?j2VTg00Zhj1;Tg00[Gj2<Tg00\0j3UTg00\Yj3?Tg00]Bj2DTg01AQj2TTg007Hj1STg00]nj3=Tg007hj1RTg008Hj2QTg008fj1PTg009Dj1LTg009oj28Tg00:Rj2OTg00;5j4:Tg00=Ej1JTg00;`j1GTg00<>j3ITg00^lj3eTg00=gj8dTg00>Kj2cTg00>mj2bTg00@3j3]Tg00@Rj4ZTg01Rbj2[Tg01Scj2\Tg00N\j1YTg01TCj3XTg00O]j6^Tg001ij2_Tg00BBj7`Tg00<aj7aTg00ECR0f0R1'_p=2%11#1#1#1p=4%11#1p=N%01#0p=M%01#0#0#0p=K%01#0#0#0#0#0#0#0p=3g00DeR2f1R3g00H4P1C:p=9P3g00BfR4g00CER5P5g00CeR6P1g00DEF`p=5f2R7P4P5P5P6P3P1Fap=E%21g00EaR8#1R9#4R:#1R;#N#4#4#4#4#4#4#7R<,61'AR=P2%79R9%7:R>'@R?,>3R@%08#M#K#3#3#3#3#3#3#3#7,f11>7?5H2X;21C9>1609RA%2>RB160?[RC[%29RDg00FFREAF9>3UW0%2?\E^0D%7;R?,C9%2?1@9?RF,60[RG\AAF9?3VEX0D%2F\E^0DP3g00Fb1W09'BPAeRAO1PGf4PAO1PCg00GHRC1V2<g00beRA#;RG,<25U21<2ARA5?2g00cDRD'D%;G#;,<29?2A/DD,TA%SCRA5=C3=%RCRC1Q23%P2RD%L2RGP4P5P5P61820R41O28R8'9,5GP2P8g00H[RE182<C:,5G5EG%J51829R9%G:5I29e28R8,94,5GP2P8PE%G;9I29C:,5G5EGGd1cG6R6P1P7g00IBR9g00IbR;'B1b17=H9;dA]203CZR0b2b5b6X72%2@16@F'A\=^72P1f8f7O2b1b4b3b9b3b:b4,[@1\3>PAPC%Y2PD182>,94,5GP6P0b2b5b6PBP1b19X3>E^UX82P1O1X82o"). Qed.
Lemma shl32_land t : Z.land (Z.shiftl t 32) 18446744073709551615 = (t mod 2 ^ 32) * 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h07__arithh14__ffh28__varmaph35__with42Hah56__sat1h61th71zh86__sat0p;1p;2p;3p;4p;6p;5p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej12Tg002jj14Tg003mj2<Tg00Q>j2>Tg003Hj10Tg00N>j2;Tg00L]j2=Tg00?Yj35Tg005Aj2ATg004Jj2:Tg001ij26Tg005ij3VTg006Mj2UTg006nj2?Tg007Hj1STg007hj1QTg00N\j1LTg008fj1KTg009Dj1HTg009oj23Tg00;`j1GTg00<>j3FTg00;5j48Tg00R>j6ETg00>Kj2DTg00>mj2ITg00@3j3JTg00@Rj4CTg01Tlj5BTg00M`j1NTg00O:j3OTg00O]j69Tg01Scj2PTg01TCj3@Tg00BBj7RTf0R0#0#0p=T%00#0#0#0p=M%00#0#0#0#0#0#0#0p=1f1R1g00BfR2g00CER3P3g00CeR4P0g00DEFRp=7g00DeR5P5g00EaR6#2R7#4R8%27#2#2#2R7#4R9'<R:,>0R;%06#T#M#1#1#1#1#1#1#1#4,;01=1:/>:R6555X75P5%27#4R<,<8,=;A5506X75P0P:P:1A89g00ECR6/:8R=1669R>1:6:[R?[1668R@g00FFRAAV891UW4166:\A^4@P1g00Fb1U68'?P=eO1P?g00GHR?#SR=%Q?R?%L5R@%K5RA%H5RBP2P3P3P4P51358%G75F5g00U^1356R7C8,7BEE1DB4R4P0f2R8g00IBR3g00IbR2'?1I08=532dAJ561CCR1b1b2b3A55:6g00VE[P0b0b5b8b5R:P:DB%N<,;;P=P?P@PAP5P7g00H4R:135<C8,7BP4P1b1b2b3166<P0b09O;<E91P09P=P?P@PAP5P7P:1359C8,7BP4P1b1b2b3P>P0b09@09E9X65P0O1W6o"). Qed.
Lemma lor_lo_hi32 x t : 0 <= x < 4294967296 -> 0 <= t < 4294967296 ->
  Z.land (Z.lor x (t * 2 ^ 32)) 18446744073709551615 = x + t * 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h04__x1h12Hah27__arithh34__ffh46__sat2h58__varmaph65__with74__p1h86__sat1h96__sat4h:4__x2h;1th<1xh=6__sat3h>1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej12Tg002jj19Tg004Jj21Tg004fj2:Tg003mj2ETg00Q>j2DTg00Paj2ATg003Hj10Tg00N>j2kTg00?Yj3KTg005Aj2ITg005ij3MTg006Mj2]Tg006nj2GTg00Zhj18Tg00[Gj27Tg00\Yj3>Tg00]Bj2FTg01AQj2ZTg00Z?j2YTg00\0j3XTg007Hj1WTg00]nj3CTg007hj1VTg008Hj2JTg00N\j1TTg00^Nj4STg008fj1RTg009Dj1PTg009oj2=Tg00:Rj2BTg00=Ej1lTg00;`j1NTg00<>j3LTg00^lj3jTg00Q[j3iTg00>Kj2gTg00>mj2fTg00@3j3aTg00@Rj4`Tg01Rbj2_Tg01UUj2^Tg00bAj6bTg01V2j6cTg00O]j6dTg001ij2eTg00;5j4HTg00BBj7\Tg00<aj7[Tg00=gj8hTg00ECR0f0R1'ep=4%21#2#2#2p=6%21#2p=U%01#0p=Q%01#0#0#0p=O%01#0#0#0#0#0#0#0p=5g00DeR2f1R3g00H4P1CHp=<P3g00BfR4g00CER5P5g00CeR6P1g00DEF\p=3P2P3g00H[P1CHp=@f2R7P4P5P5P6P3P1F[p=;f3R8P4P5P5P6P7P3P1Ghp=?%43R9g00EaR:#2R;#6R<#2R=#U#6#6#6#6#6#6#9R>,13':R?P2%9;R@%9<RA'ERB,D7RC,A8RD%0:#Q#O#5#5#5#5#5#5#5#9,k1f4RE1D8BRF'A5K2X>21I@ARG110@RH%4ARI110B[RJ[RK%4@RLg00FFRMAM@A3UW1RN%4B\M^1LRO%9=RP,I@%4P1E@PRQ,10[RR\HAM@P3VMX1L%4Q\M^1LP3g00Fb1]0@'GPHeRHO1RLPRPEPHO1PJg00GHRHg00beRE#8RR#8RM,72172ERE5>2%8MRM#8#8,729>2Eg00cDRP'F'Z1Y2>172M5X2172R=>2E5>2/FP%WHRP5CH3C%VHRHP21J27P3%T2RECS%R2RR%P2RM1=20RS1B2;R;'<,3M1=2>RT,@;,3M5;M%l5RUPM1B2:R:,<S,3MRV1@:T,3M5;MRTPU1=2@R@%N<5L2R<9j2;9i2:R;,<S,3M%N=9L2@,@;,3M5;MC?C?1gM6R;P1P7g00IBR@g00IbR='G1f17=K@=dAa203C`R0b3b5b6X02X:21A7FRF#411FQ':\?\?^02^:2P1f9f:f7RFf8O4b2b9b4b8b4b=b9,_D1^8CP8P7PAPPPHPEPR1=2A,<S,3MP;P0b3b5b6PIP1b2PGPKPNPOPLPJPPPH1J23RJPRPMPTPU1@:<,3M9;MVC?P;P0b3b5b6X02%41R<111>':113B,:9[^02P1PFf5O2b2b4b8b4p-0RFPPPHPJPRPMPMP4P5P5P6P8Eb9;MVPUPVC?P;P0b3b5b6X02W71:<3P9[^02^7FP1118>P8P3O3b2EcEdV?UX;2X<2P3P1O2X;2X<2o"). Qed.
Lemma lor_hi_lo32 t y : 0 <= t < 4294967296 -> 0 <= y < 4294967296 ->
  Z.land (Z.lor (t * 2 ^ 32) y) 18446744073709551615 = t * 2 ^ 32 + y.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkKit ()) [] "h04__x1h12Hah27__arithh34__ffh46__sat2h58__varmaph65__with74__p1h86__sat1h96__sat4h:4__x2h;1th<1yh=1zh>6__sat3h?7fv_listh@8hyp_listhA3lmpp;1p;2p;3p;4p;7p;6p;:p;<p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g002Ej14Tg002jj18Tg004Jj21Tg004fj27Tg003mj2LTg00Q>R0j2NTg01UUj2JTg003Hj10Tg00N>j2TTg00PaR1j2DTg00?Yj39Tg00n1j1pTg00n[j2ETg007Hj1GTg007hj1>Tg00]nj3<Tg00o;j2VTg010Oj2dTg0119j1cTg011Wj3bTg00oej3`Tg01Mjj3MTg006nj2KTg012Aj1^Tg012ij4\Tg013Oj7[Tg005Aj2HTg005ij3OTg006Mj2YTg00Zhj1;Tg00[Gj2BTg00\Yj3CTg00]Bj2WTg01AQj2|Tg00Z?j2{Tg00\0j3zTg008Hj2PTg00N\j1yTg00^Nj4xTg008fj1wTg009Dj1tTg009oj2@Tg00:Rj2RTg00=Ej1oTg00;`j1QTg00<>j3UTg00^lj3mTg00Q[j3lTg00>Kj2iTg00>mj2jTg00@3j3kTg00@Rj4hTg01Rbj2nTg00O]j6FTg00bAj6gTg01V2j6fTg01W5j2eTg001ij2qTg014>l:rTg014ol<sTg00;5j4STg00BBj7uTg00<aj7vTg00=gj8aTg00ECR2f0R3'qp=2%43#4#4#4p=5%43#4p=]%03#0p=Z%03#0#0#0p=X%03#0#0#0#0#0#0#0p=6g00DeR4P2f1R5P1P0g015\R6g00JBR7g0169R8g016VR9P3M:rp=_P4P2f2R:P1P0P6P7P8P9g0177R9P5P3M<sp=IP4P5g00H4P3CSp==P5g00BfR7g00CER6P6g00CeR0P3g00DEFup=3P4P5g00H[P3CSp=?P:P7P6P6P0P5P3Fvp=:f3R1P7P6P6P0P:P5P3Gap=A%25R;g00EaR<#4R=#5R>#4R?#]#5#5#5#5#5#5#8R@,15'7RAP4%8=RB%8>RC'LRD,N1RE,J:RF%0<#Z#X#6#6#6#6#6#6#6#8RG,T3f4RH/ND/D1RI594X=4RJP41D:ERKPJP4PKA943IX=4%p4RI/EIRI#G%>I%G49<4H9<41%>4P9P3P51V4<R91V4=1d4B%cC5b45`4RI5M4RJAM4I9RIg017fg00IBR9g00IbRL'KRM%8<RN/_5g018B,E4%^4'E#>P4P8AIN3JAIN3IC\bA=99LdF[b?b@1DE:994Ke1TKG1HBCRG112BRN%2CRI112D[RJ[R8%2BROg00FFRPAOBC5UW1RQ%2D\P^1ORR%8?RS,HB%2S1LBSRT,12[RU\NAOBS5VPX1O%2T\P^1OP5g00Fb1Y2B'KPNeRNO1ROPUPHPNO1PJg00GHRNg00beRU#;RP#;#;RS#;,B41B4URU5C41B4SRS9C4Ug00cDRV'W'|1{4@1B4P5z4=C4U9C4S/WV%GNRV5<N3<%>NRNP41P4:P5%y4RSCx%w4RU%t4RP1@42RW1R4<R<'=,3PRX1@4@RY,?<,3P5:PRZ%o6R[PP1R4=R=,=W,3P1?=Y,3P5:PP[1@4BRB%Q>5U4R>9m4=9l4<R=,=W,3P%Q?9U4B,?=,3P5:PCACA1iP0R=P3P:PM1j3:=99LdAk425ChR2b3b5b6X04X:4%23RL113@'7R9%2:11:@'7%2K11KT'7[[^04^:4P3f:f9f7f8O4b2b9b4b8b4b>b9,nKEFPFP:P1PCPVPNPSPU1@4C,=W,3PP=P2b3b5b6PIP3b2PGP8PQPRPOPJPVPN1P45RJPUPPPZP[1?<>,3P9:PXCAP=P2b3b5b6X04115D,7;\9^04P3f6PHO2b2b4b8b4p-0R9PVPNPJPUPPPPP7P6P6P0P1Eg9:PXP[PXCAP=P2b3b5b6X04W717L5P;[^04^79P311H@PHP:O3b2EfEF1JE:1eE:EFVAUX<4X;4P5P3O2X<4X;4o"). Qed.
Close Scope Z_scope.

End WdWkKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module WdWkMem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fix_store_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?c)) _) => change (Z_to_le_bytes 8 c) with (le8 (Z_to_bv 64 c))
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?c)) _) => change (Z_to_le_bytes 4 c) with (le4 (Z_to_bv 64 c))
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?c)) _) => change (Z_to_le_bytes 2 c) with (le2 (Z_to_bv 64 c))
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with (le1 (Z_to_bv 64 c))
  end; mem_after_store.
Ltac fix_store0 := fix_store_lit.
Ltac zrun0 := repeat (first [ progress zrun
                            | lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => fix_store_lit end ]).
Ltac zrun0_to pc := repeat (first [ progress (zrun_to pc)
                            | lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => fix_store_lit end ]).

Lemma unsigned_lo64 x : bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. apply unsigned_small64. unfold lo64. apply wrap64_range. Qed.
Lemma unsigned_hi64 x : bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. apply unsigned_small64. unfold hi64. apply wrap64_range. Qed.
Lemma qok_1_1 : qok 1 1. Proof. split; [lia|]. unfold qB. cbn. lia. Qed.

Ltac show_goal := match goal with |- ?g => idtac "GOAL" g end.

(* [comment removed for export] *)
Tactic Notation "callx" uconstr(SPEC) constr(E) "by" tactic(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply SPEC; rewrite ?(unsigned_small64 E) by lia; side
                      | lazymatch goal with |- forall ms', ?P ms' -> _ => let h := get_head P in try unfold h end;
                        rewrite ?(unsigned_small64 E) by lia; post_call segs m ]
  end.
(* [comment removed for export] *)
Tactic Notation "leaf" uconstr(SPEC) "by" tactic(side) :=
  eapply evt_cut; [ eapply SPEC; side
                  | lazymatch goal with |- forall ms', ?P ms' -> _ => let h := get_head P in try unfold h end;
                    let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO;
                    (lazymatch type of PO with _ /\ _ => destruct PO as [?PC PO] | _ => idtac end);
                    subst ms';
                    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end) ].

Open Scope Z_scope.
(* [comment removed for export] *)
Lemma sx32_ztb x : -2 ^ 31 <= x < 2 ^ 31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 x) with (bv_wrap 32 x + 2 ^ 32 * ((bv_wrap 64 x) / 2 ^ 32)).
  2:{ unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32). change (2 ^ Z.of_N 32) with (2 ^ 32).
      rewrite Z.rem_mul_r by lia. pose proof (Z.div_mod (x mod (2 ^ 32 * 2 ^ 32)) (2 ^ 32) ltac:(lia)). lia. }
  unfold bv_swrap. rewrite Z.mul_comm. unfold bv_wrap at 2. rewrite <- Z.add_assoc, (Z.add_comm (_ * _)), Z.add_assoc.
  unfold bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite Z.mod_add by lia. rewrite Zplus_mod_idemp_l.
  replace ((x + 2 ^ 32 / 2) mod 2 ^ 32) with (x + 2 ^ 32 / 2) by (symmetry; apply Z.mod_small; change (2 ^ 32 / 2) with (2 ^ 31); lia).
  lia.
Qed.
Lemma ztb_uadd x c : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  apply Z_to_bv_eqm. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma ztb_landW_add x c : Z_to_bv 64 (Z.land x 18446744073709551615 + c) = Z_to_bv 64 (x + c).
Proof. rewrite land_W64. apply Z_to_bv_eqm. change (2 ^ 64) with 18446744073709551616. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma swrap32_landW_add x c : -2 ^ 31 <= x + c < 2 ^ 31 -> bv_swrap 32 (Z.land x 18446744073709551615 + c) = x + c.
Proof.
  intros. rewrite land_W64. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31).
  rewrite <- Z.add_assoc, <- (Zplus_mod_idemp_l (x mod 2 ^ 64)).
  rewrite (Z.mod_mod_divide x (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Close Scope Z_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma wr_at_app m A n1 n2 : (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros H1 H2. unfold wr_at. split.
  - intros (Ha & Hn & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i)%Z with (A + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hn & Hx) & (Ha2 & Hn2 & Hy)). repeat split; try lia.
    intros i Hi. destruct (Z_lt_ge_dec i n1); [apply Hx; lia|].
    replace (A + i)%Z with (A + n1 + (i - n1))%Z by lia. apply Hy. lia.
Qed.

Lemma rw_cells_app m A cs1 cs2 :
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite bytes_at_app. split.
  - intros (((W1 & W2) & (B1 & B2)) & WR). rewrite (cells_bytes_length cs1 W1) in B2.
    apply wr_at_app in WR; [|lia|lia]. destruct WR as [WR1 WR2].
    split; [split; [split; [exact W1 | exact B1] | exact WR1] | split; [split; [exact W2 | exact B2] | exact WR2]].
  - intros (((W1 & B1) & WR1) & ((W2 & B2) & WR2)). rewrite (cells_bytes_length cs1 W1).
    split; [split; [split; [exact W1 | exact W2] | split; [exact B1 | exact B2]]|].
    apply wr_at_app; [lia|lia|]. split; [exact WR1 | exact WR2].
Qed.

Lemma rw_cells_take3 m A pre mid post :
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre)) mid
  /\ rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post.
Proof.
  intros H. apply rw_cells_app in H. destruct H as [H1 H23]. apply rw_cells_app in H23. destruct H23 as [H2 H3].
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma rw_cells_join3 m A pre mid post :
  rw_cells segs m A pre -> rw_cells segs m (A + Z.of_nat (cells_size pre)) mid ->
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post ->
  rw_cells segs m A (pre ++ mid ++ post).
Proof. intros H1 H2 H3. apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. split; [exact H2 | exact H3]. Qed.

(* [comment removed for export] *)
Lemma stk_of_u32arr m A ws : u32arr segs m A ws -> stk segs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros [(Ha & Hl & Hb) Hw]. rewrite u32s_length, Nat2Z.inj_mul in Hl. change (Z.of_nat 4) with 4%Z in Hl.
  destruct Hw as (_ & _ & Hw).
  split; [lia|]. split; [lia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb.
    + destruct (nth_error (u32s ws) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
      apply nth_error_None in E. rewrite u32s_length in E. lia.
    + rewrite u32s_length. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_range (bs : list byte) : (0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length bs)))%Z with (8 * Z.of_nat (length bs) + 8)%Z by lia.
  rewrite Z.pow_add_r by lia. rewrite lor_shiftl8_add by lia. change (2 ^ 8)%Z with 256%Z. nia.
Qed.

Lemma Z_to_le_bytes_inv (bs : list byte) : Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as Hr.
  rewrite lor_shiftl8_add by lia.
  replace (bv_unsigned b + 256 * bytes_le_to_Z bs)%Z with (bv_unsigned b + bytes_le_to_Z bs * 256)%Z by ring. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

Fixpoint words_of_bytes (n : nat) (bs : list byte) : list word :=
  match n with
  | O => []
  | S n' => Z_to_bv 64 (bytes_le_to_Z (firstn 4 bs)) :: words_of_bytes n' (skipn 4 bs)
  end.

Lemma words_of_bytes_length n bs : length (words_of_bytes n bs) = n.
Proof. revert bs. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma u32s_words_of_bytes n bs : length bs = (4 * n)%nat -> u32s (words_of_bytes n bs) = bs.
Proof.
  revert bs. induction n as [|n IH]; intros bs Hl.
  - destruct bs; [reflexivity | cbn in Hl; lia].
  - cbn [words_of_bytes u32s]. rewrite IH by (rewrite skipn_length; lia).
    rewrite <- (firstn_skipn 4 bs) at 3. f_equal.
    unfold le4. rewrite Z_to_bv_unsigned.
    pose proof (bytes_le_to_Z_range (firstn 4 bs)) as Hr. rewrite (firstn_length_le bs (n:=4%nat)) in Hr by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Hr.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Z.mod_small by lia.
    rewrite <- (firstn_length_le bs (n:=4%nat)) at 1 by lia. apply Z_to_le_bytes_inv.
Qed.

Lemma u32arr_of_rw_cells m A n bs : rw_cells segs m A [CB (4 * n) bs] ->
  u32arr segs m A (words_of_bytes n bs).
Proof.
  intros H. pose proof (u8arr_of_rw_cells segs m A _ bs H) as [Hb Hw].
  destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hn _].
  split.
  - rewrite u32s_words_of_bytes by lia. exact Hb.
  - rewrite words_of_bytes_length. replace (4 * Z.of_nat n)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

End WithSegs.

End WdWkMem.
