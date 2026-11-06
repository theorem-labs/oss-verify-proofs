(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Reloc () := "C47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00c69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib6Common5Reloc5Reloc8rl_u_modC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List7existsbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib6Common5Reloc5Reloc@Z_to_bv64_mod_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib6Common5Reloc5Reloc7rl_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4btgtC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC59OSSVerify5KrLib6Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv9Zplus_modC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib6ZArith4Zdiv:Zminus_modC59OSSVerify5KrLib6Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9rem_mul_rI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib6Common5Reloc5Reloc9rl_even_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9code_readC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01c69OSSVerify5KrLib6Common5Reloc5Reloc:fetch_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib6Common5Hoare<land_m2_evenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203c69OSSVerify5KrLib6Common5Reloc5Reloc7rl_btgtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc8rl_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc5rl_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7eqb_neqc69OSSVerify5KrLib6Common5Reloc5Reloc4rl_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib6Common8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib6Common5Reloc5Reloc7dtab_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc7dlookupC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes9andb_propC56Stdlib6PArith6BinPos3Pos3eqbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes8list_indc69OSSVerify5KrLib6Common5Reloc5Reloc8DELTA_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc8DELTA_HIC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c69OSSVerify5KrLib6Common5Reloc5Reloc7rl_dtabC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc:rl_dtab_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc:dlookup_bdC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc;rl_delta_bdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rl (d c : Z) : word := Z_to_bv 64 (c + d).
Arguments rl : simpl never.

Lemma rl_unfold : forall d c, rl d c = Z_to_bv 64 (c + d).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01ch11dp;1p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8g000Mj10Tg0012j15Tg001Pj12Tg0023j21Tg002Pj24Tg0036j23Tg003PR1g003n#0#0#0#0#0#0#5R0#2f0f1'1,40'3X01W1o"). Qed.

Lemma Z_to_bv64_mod_eq : forall a b : Z, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02b1h12b2h21nh31zh41Hh52H0h61ah71bp;1p;2p;3p;6g000Mj12Tg004Sj19Tg0051j2<Tg005Nj25Tg005nj30Tg001Pj13Tg006Hj21Tg0072j3;Tg0012j1:Tg002Pj26Tg007Vj24Tg008<j27Tg008kj68Tg003PR0f1R1g003n#2R2#9%22#2#2#2#2R2#9'<R3'5f0R4/53500g009IR3%34R5%31R6g009gf2R7#3?014f3R8/171181500R9[11711174500%38?071[R:f4R;#3?087\9A;714P4n2001000000120000000W1W0W2P:^16^05^23P4%:2R21628R31627R5P014281123R39004X30P01427142;=004X30P111251727E8P31728E8O4b5W4X70W6o"). Qed.

Lemma rl_u_mod : forall d c, bv_unsigned (rl d c) = (c + d) mod 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01ch11dh21zp;1p;2p;3p;6g000Mj10Tg0012j1=Tg0023j21Tg007Vj26Tg004Sj15Tg0051j2;Tg005Nj23Tg005nj32Tg0036j28Tg002Pj27Tg006Hj24Tg008<j29Tg008kj6:Tg00:Bj2<Tg003PR0P0g003n#0R1#0#0#0#0#0R2#=R3f0R4f1R5'1R6'6f2,15%51%52';R2'39204X201362R2,801736,431936E:1<54,43=202eX00W1o"). Qed.

(* [comment removed for export] *)
Lemma rl_u : forall d c, 0 <= c + d < 2^64 -> bv_unsigned (rl d c) = c + d.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01Hh11ch21dh31zp;2p;1p;3p;6g0023j21Tg00;<j2>Tg000Mj10Tg004Sj12Tg0051j2=Tg00;Xj2:Tg009gj27Tg005Nj24Tg005nj35Tg00<4j36Tg0012j13Tg00:Bj28Tg006Hj29Tg00<Wj2<Tg008kj6;Tg003PR0g00=Wf0R1f1R2'1R3'>g003n#0R4#2%04#0#0#0#0R4#2'=R5,:3'7P0f2R3,12R6/45f3,139501X30A6651%341832'91<32E;W0X10W2o"). Qed.

(* [comment removed for export] *)
Lemma rl_addi : forall d c e, v_addi (rl d c) e = rl d (c + e).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h04__x1h14__x2h24__x3h31zh47__arithh54__ffh68__varmaph75__with81ch91dh:1ep;2p;1p;3p;4p;7p;8p;6p-1p100>5p4p710p8g0023j20Tg000Mj12Tg004Sj19Tg0051j2@Tg005NR0j24j1;Tg0012j1OTg001Pj1ITg002Pj2<Tg00:Bj25Tg005nj31Tg0036j27Tg00>Qj1>Tg00?1j1QTg00?Qj2=Tg00?oj4PTg00@Mj1NTg00@kj1KTg00AVj26Tg00B9j33Tg00B\j1HTg00CAj4GTg00Clj7DTg00DPj2CTg00E2j2ETg00E^j3BTg00F=j4FTg00Foj8:Tg00GLj3ATg008kj68Tg00H3j3JTg006Hj2?Tg00<Wj2LTg00I;j2MTg003PR1P1f1R2f2R3'0R4g003nR5#2R6#9%26#2#2#2#2R7#9'@R8'4R9%O7R7#IR:f0R;/02R<,<7f3R=1032R>'531X31109;R9102;R?/03R@P1104;RA/4810>=/48911;X31P1P1%;A%;@P8P8P1P1\1R>P0P0PAP@P>\1/70g00J6R0#>%Q0P11=13P21=1=CP%N1%K1R0g00Jbg00KAR>P>g00KaR>P11615R@1616R6531%H5,61R5531g00LAA31@5=316CGg00LhFD1C0>P;P3g00MHR>g00MhR0'71E;3=1>0dg00=W=B12CFb5b6b7X01X11X2110<310;3/02511^01^11^21P;P2P=P3O3b4G:1718G:1498AA4;8E83J1<79153?R?51:e1532R9,?71L32E81M9;=1:?eX:1X81W9o"). Qed.

Lemma rl_btgt : forall d c e, btgt (rl d c) e = rl d (c + e).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01ch11dh21ep;3p;1p;2g00NHj37Tg000Mj10Tg0012j13Tg001Pj12Tg00:Bj21Tg00OGj26Tg0023j25Tg005nj34Tg003PR0f2R1f1R2f0R337g003n#0#0#0#0#0#0#3#21112/631523,1134eX20X00W1o"). Qed.

Lemma rl_at : forall d c e, at_ (rl d c) e = rl d (c + e).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01ch11dh21ep;3g00NHj30Tg003PR0f2f1f030X20X00W1o"). Qed.

Lemma rl_auipc : forall d c e, v_auipc (rl d c) e = rl d (c + e).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h04__x1h14__x2h24__x3h31zh47__arithh54__ffh68__varmaph75__with81ch91dh:1ep;2p;1p;3p;4p;7p;8p;6g0023j20Tg000Mj12Tg004Sj19Tg0051j2@Tg005NR0j24j1;Tg0012j1OTg001Pj1ITg002Pj2<Tg00:Bj26Tg005nj31Tg0036j27Tg00>Qj1>Tg00?1j1QTg00?Qj2=Tg00?oj4PTg00@Mj1NTg00@kj1KTg00AVj25Tg00B\j1HTg00B9j33Tg00CAj4GTg00Clj7DTg00DPj2CTg00E2j2ETg00E^j3BTg00F=j4FTg00Foj8:Tg00P@j3ATg008kj68Tg00H3j3JTg006Hj2?Tg00<Wj2LTg00Pgj2MTg003PR1P1f1R2f2R3'0R4g003nR5#2R6#9%26#2#2#2#2R7#9'@R8'4R9%O7R7#IR:f0R;,02R<,<7f3R=1032R>'631X3110;9R910<3R?P110;4R@/4810>=/48911;X31P1P1%;@%;?P8P8P1P1\1R>P0P0P@P?P>\1/70g00J6R0#>%Q0P11=13P21=1=CP%N1%K1R0g00Jbg00KAR>P>g00KaR>P11515RA1516R6%H5,51R5531531g00LAA316A=315CGg00LhFD1C0>P;P3g00MHR>g00MhR0'71E;3=1>0dg00=W=B12CFb5b6b7X01X11X21A11@?^01^11^21P;P=P3P2O3b4G:1718G:1498AA4;8E83J1<79163<R<51:e1632R9,?71L32E81M9;=1:<eX:1X81W9o"). Qed.

Lemma rl_add_r : forall d c k, v_add (rl d c) (Z_to_bv 64 k) = rl d (c + k).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01zh14__x1h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with81ch91dh:1kp;2p;1p;3p;4p;7p;8p;6g0023j20Tg000Mj12Tg004Sj1;Tg0051j2ATg005NR0j23j1:Tg0012j1RTg001Pj1JTg002Pj24Tg006Hj27Tg00:Bj28Tg005nj31Tg007Vj2?Tg0036j29Tg00>Qj1TTg00?1j1STg00?Qj2>Tg00?oj4QTg00@Mj1NTg00@kj1ITg00AVj26Tg00B9j35Tg00B\j1ETg00CAj4DTg00Clj7FTg00DPj2CTg00E2j2GTg00E^j3HTg00F=j4BTg00Foj8=Tg00Qcj3KTg00RBj6@Tg00H3j3LTg008<j2MTg008kj6<Tg00<Wj2OTg00R^j2PTg003PR1P1f1R2f2R3'0R4g003nR5#2R6#;%26#2#2#2#2R7#;'AR8'3R9%R7R7#JR:f0R;1472,77'0,47f3R<1032R='8R>31X01P11?7;R?103</38/0;,47=1:>X01109?R?102;R>/03R@P1104;RA/3810=</38911;X01P1P1%:A%:@P8P8P1P1\1R=P0P0PAP@P=\1/90g00J6R0#T%S0P11>13P21>1<CQ%N1%I1R0g00Jbg00KAR=P=g00KaR=P11615R@1616R6551%E5,61R5551g00LAA51@5=516CDg00LhFF1C0=P;P3g00MHR=g00MhR0'91G;3=1=0dg00=W=H12CBb5b6b7X11X21X3110;2/0310;3/02511^11^21^31P;P2P<P3O3b4G=1918G=13;8,09/38AK4;8E@3L147?183>R>51:e147;R?,771M7;E<1832R;,771O32E<1P;?=1:>eX:1X81W9o"). Qed.

Lemma rl_add_l : forall d c k, v_add (Z_to_bv 64 k) (rl d c) = rl d (c + k).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01zh14__x1h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with81ch91dh:1kp;2p;1p;3p;4p;7p;8p;6g0023j20Tg000Mj13Tg004Sj1<Tg0051j2ATg005NR0j22j1:Tg0012j1RTg001Pj1JTg002Pj24Tg006Hj28Tg00:Bj27Tg005nj31Tg007Vj2?Tg0036j29Tg00>Qj1TTg00?1j1STg00?Qj2>Tg00?oj4QTg00@Mj1NTg00@kj1ITg00AVj26Tg00B\j1HTg00B9j35Tg00CAj4ETg00Clj7DTg00DPj2CTg00E2j2FTg00E^j3GTg00F=j4BTg00Foj8=Tg00Qcj3KTg00RBj6@Tg00H3j3LTg008<j2MTg008kj6;Tg00<Wj2OTg00R^j2PTg003PR1P1f1R2f2R3'0R4g003nR5#3R6#<%36#3#3#3#3R7#<'AR8'2R9%R7R7#JR:1472,87f0R;'0,47f3R<1032R='7R>31X01P11?7;R?103</28,0;,47=1:>X0110?9R?102;R>/03R@P110;4RA/2810=</28911;X01P1P1%:A%:@P8P8P1P1\1R=P0P0PAP@P=\1/90g00J6R0#T%S0P11>13P21>1<CQ%N1%I1R0g00Jbg00KAR=P=g00KaR=P11615RB1616R6%H5,61R5551551g00LAA516B=515CEg00LhFD1C0=P;P3g00MHR=g00MhR0'91F;3=1=0dg00=W=G12CBb5b6b7X11X21X31A11A@^11^21^31P;P<P3P2O3b4G=1918G=12;8/09/28AK;48E@3L147?173>R>51:e147;R?,871M7;E;1732R;,871O32E;1P?;=1:>eX:1X81W9o"). Qed.

(* [comment removed for export] *)
Lemma rl_sub_same : forall d c1 c2, v_sub (rl d c1) (rl d c2) = Z_to_bv 64 (c1 - c2).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01zh14__x1h24__x2h34__x3h47__arithh54__ffh68__varmaph75__with82c1h92c2h:1dp;2p;1p;3p;4p;7p;8p;6g0023j24Tg000Mj12Tg004Sj1<Tg0051j2DTg005NR0j21j1:Tg0012j1RTg001Pj1OTg00:Bj28Tg006Hj27Tg00SXj20Tg002Pj25Tg005nj33Tg0036j29Tg00>Qj1TTg00?1j1STg00?Qj2ATg00?oj4QTg00@Mj1PTg00@kj1NTg00AVj26Tg00B9j3>Tg00B\j1JTg00T5j3=Tg00CAj4ITg00Clj7FTg00DPj2GTg00E2j2HTg00E^j3ETg00F=j4KTg00Foj8;Tg00TXj3CTg00RBj6LTg00H3j3MTg00<Wj2@Tg008kj6?Tg00U8j2BTg003PR1P1f1R2f2R3'4R4g003nR5#2R6#<%26#2#2#2#2R7#<'DR8'1R9%R7R7#OR:f0R;f3R</82,77'0,571032R=,57R>33X01P114;3R?/18R@143</18/0;,57=3:>X01109@R@102;R9P1104?R>/1811=8931;X01P1P1%:>%:9P8P8P1P1\1R=P0P0P>P9P=\1/90g00J6R0#T%S0P11A13P21A1<CQ%P1%N1R0g00Jbg00KAR=P=g00KaR=P11615R>1616R65>1%J5,61R5=>165=1g00LAA=1>5CIg00LhFF1G0=P;P3g00MHR=g00MhR0'91H;3=3=0dg00=W=E12CKb5b6b7X11X21X3114;21432'010;3531^11^21^31P;P2P<P3O3b4G;1918G;11@8AC4?8EL3M183;R?,771@3;E?1832R;,771@32E?1B;?157953:eX91X81W:o"). Qed.

(* [comment removed for export] *)
Lemma rl_even_u : forall d c, (c + d) mod 2 = 0 -> bv_unsigned (rl d c) mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01zh12H0h22H1h32H2h42H3h52H4h62Hah77__arithh84__ffh96__sat0h:8__varmaph;5__with<1qh=1rh>1Hh?6__sat1h@6__sat2hA1chB1dp;2p;1p;3p;4p;6p;5p;7g0023j21Tg000Mj19Tg004Sj1<Tg005Nj20Tg0051j2GTg00V2j23Tg00B\j1:Tg00VOj27Tg0036j2?Tg00Vlj2BTg00W]j2CTg00X>j1_Tg005nj36Tg00XWj2HTg00;Xj25Tg009gj2;Tg00Y>j2FTg00;<j2=Tg00Yej2ETg00ZKj2DTg00>Qj1WTg00?1j1VTg00[1j1UTg00@Mj1RTg00@kj1QTg00[Oj2ATg00CAj4@Tg00\2j6OTg00DPj2MTg00E2j2LTg00E^j3NTg00F=j4KTg00\Vj3PTg008kj68Tg00]7j2JTg00]Yj1STg00^:j2TTg00^bj3^Tg0012j1ITg00_Fj3]Tg00_ij5\Tg00:Bj2[Tg006Hj2YTg00<Wj2XTg00Clj7ZTg003PR0f0R1g00=WR236p=41=21p=2f1R3g00JbR4g00KAR5P5g00KaR6P1g00LhFZp=>1113g003nR7#9R8#<R9'0#4P0f2R:,13R;%98#9#9#9#9R8#<,G9'01019#4X00R<P010;9R=13;9%:7#:#:#:#:R7#<R>,G9R?'0R@,79RA'1P<P0P2f3RB,1:RC/39/0?,79,11/09#4X00P0PAP<P017@9RDP<P0P2%41X001?0210D91B;9%2;%29RDf4R<,1BRB/09RE#2[[1CC9%49RC#_RF13B9,79/1E960B[1HB91529REf5RG,1<R</09RH#215H9';[1F<91592RHf6RI,1GRG/09RJ,591=J2';[1EG9f7RK,1IRI/39#4\C1DI9f8RL,1KRK/09RM=60K\C13K9P0f9RN,1LRL/09P0g00J6RO#WRP%VORO%U0RQ%R0RR%Q0RSP4P5P5P6P01A09R5g00LA1A02R4C@,>SEO1MS6R6P1P:g00MHRTg00MhRU'?1L1:=6TUdAN023CKRUb8b:b;g00`L\CP1b7b=b<b5b4b3b2b1b9RT9P@9E8PA1J9@E8112A%SAE8P=P1E8179?,0;P;P9P?PT1T9>%2>152?RT[\Eg00`iR;A^9>3UX6D%2?\;^6D1BB9%2B%2J\D[1C<913G9,79/1J960G\F1HG910I9RG#215G9';\E1FI9159M1=M2';\H1EK913L9#4\C1DL9f:RL,1NRN/09=60N\C13N9P0f;,1L/09P0PPPOPQPRP0P4g00aE%I79]05C@,>SP6PUb8b:b;PTP1b7b=b<b5b4b3b2b1b9b?b@D\E8%I81[:3'Y1X:3E8W>XA0XB0o"). Qed.

Lemma rl_ret_ok : forall d c, (c + d) mod 2 = 0 -> ret_ok (rl d c).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01Hh11ch21dp;2p;1p;3g0023j27Tg000Mj16Tg004Sj10Tg005Nj21Tg005nj35Tg00:Bj22Tg00alj33Tg00bmj24Tg003PR0f0R1f1R2'7g003n#6#0'1g00=W550f2R3/22A3321'4W0X10W2o"). Qed.

(* [comment removed for export] *)
Lemma fetch_even : forall segs (a : word) w, fetch_word segs a = Some w -> bv_unsigned a mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "p'0h01Eh11Hh22H0h31mh41nh51ah61bi001bh71eh84segsh91wi012b0i022b1i032b2i042b3i051li062l0i072l1i082l2i092l3i0:2l4i0;1oi0<1xp;1p;2p;3p;4p;6g00?1R0j1;Tg000Mj11Tg0012j15Tg001Pj17Tg00cjR1j1DTg00dLj2BTg00eNj26Tg005nj30Tg006Hj23Tg004Sj1=Tg005Nj24Tg00f0j22Tg0036j2<Tg00fMj19Tg00fkj1CTg00gMj3:Tg00hNj4ATg00iAj2?Tg00RBj6>Tg00iaj2@Tg00MHR2f0R3g00MhR430p=8g00j@#;g003n#1R5#1R6#1R7#1#1R8#1#5R9#7%58#7R8%D8R:f2R;f1R<'B168330139;%=5R5'4g00=WR='2P21<23f3R>,39/45/2==023P2f5R?,39/45/2==023P2P:%9<%C8R@P1%57#7R7#;RAP:f7RBf6RC%56R63:P0P7P:P3P@P0P7P:P3P@P0P7P:P3P@P0P7P:P3P@P0P7P:P3P<P>P?PBCA,68P@n1011090002002010010:n10110800020020104109n10110700020020103108n10110600020020102107n10110500020020101106R7P@n10110<00021010500n0100000020001168?R050:g003PRD139B/45RB;0=RE]1]0P<f4RF,39/45/2=R5#8P2P:%94P@P1PAP:A:C?6P7P@n10110<00021010500R7n0100000020001168FRF50:g009g12<3#8A0D;<[R6A0D<312;<#8RC[A0D>;\C1?<3P<n2001000000120000000X3DX4DP6^3D^4DP3PBP=P;O3PEP3b0b2W1W0g00k?R=9025P2P:%9=P@P7n0100000020001=0:FP:P@P1P8p-0P3g00`LR8g00`in10110;00021000000X7:g00k_P0P3E>P81@E3b2W1W0n0110001020101P3P;O2b0b6W1W9W5W8o"). Qed.

Lemma fetch_ret_ok : forall segs (a : word) w, fetch_word segs a = Some w -> ret_ok a.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01Hh11ah24segsh31wp;1p;2p;3p;4g00?1j19Tg000Mj10Tg0012j12Tg001Pj11Tg00cjj18Tg00dLj27Tg00eNj24Tg005nj33Tg00l;j45Tg00bmj26Tg00j@#9g003n#0#0#0#0#0R0#0#2#1%20#1R0%80f2R1f1R2'7f0R3,4033f3P1P2P3C5,61W0W3W1W2o"). Qed.

Lemma rl_jalr0 : forall d c, ret_ok (rl d c) -> v_jalr (rl d c) 0 = rl d c.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01Hh11ch21dp;2p;1g00:Bj21Tg00m=j10Tg003PR0f1f0R1'1#0P1W0X10W2o"). Qed.

(* [comment removed for export] *)
Lemma rl_jalr_fetch : forall segs d c e c' w, c + e = c' ->
  fetch_word segs (rl d c') = Some w -> v_jalr (rl d c) e = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h04__x1h14__x2h24__x3h31zh41Hh52H0h62H1h73H10h83H11h93H12h:3H13h;3H14h<3H15h=3H16h>3H17h?3H18h@2H2hA2H3hB2H4hC2H5hD2H6hE2H7hF2H8hG2H9hH2HahI3HevhJ7__arithhK4__ffhL8__varmaphM5__withN5__x10hO5__x11hP4__x4hQ4__x5hR4__x6hS4__x7hT4__x8hU4__x9hV2c'hW1qhX2q0hY2q1hZ2q2h[1rh\2r0h]2r1h^2r2h_1Eh`2Hfha6__sat0hb6__sat1hc6__sat2hd6__sat3he6__sat4hf6__sat5hg1chh1dhi1ehj4segshk1wp&0p;1p;2p;3p;4p;6p;7p;8g00?1j1vTg000Mj12Tg0012j1pTg001Pj1uTg0023j20Tg00cjk106Tg00:Bj2:Tg00dLj2tTg00eNj2oTg005nj34Tg00n5j2cTg00l;k40ATg006Hj2aTg004Sj1_Tg005NR0j21j1eTg0051k20;Tg00<Wj2kTg00RBj6jTg00noj1iTg00oMj2gTg002Pj2YTg00W]j2KTg00X>j1bTg00XWj2ETg00;Xj2CTg00Y>j2FTg00Yej2ITg00ZKj2?Tg00V2j29Tg00okk20@Tg010Lj1ATg010kj3WTg011Tj2rTg012=k20?Tg012ij2qTg00>Qk10>Tg013Uk30=Tg00[1k10<Tg00@Mk10:Tg00@kk109Tg00[Oj2]Tg00fkk107Tg00B\j1RTg0145j3TTg00CAj4UTg00AVj2hTg014Xk705Tg00DPk204Tg0036j2XTg00E2k203Tg00E^k302Tg00F=k401Tg00VOj2QTg00^:k200Tg00^bj3~Tg00Vlj2VTg00Foj8fTg00GLj3}Tg008kj6ZTg00H3j3|Tg015<j2{Tg00;<j2\Tg009gj2dTg016:j3^Tg00?Qj2zTg00?ok408Tg00Clj7nTg00\2j6yTg00B9j3xTg016cj8wTf0R1#2#2p=sg003PR2f1R3;41p=lg00=WR49421p=Bf2R5/03/11p=<%21#2#2#2#2#2#2#2p=L1153/01p=Mf4R6f3R71953'Q/01542p=H1\451C31'dp=>1C531\14'dp=@1931=424p=G1153=421p=J1075/03/11p=;1053/01p=31r21p=NA^231p=`A^2319^25p=S1z21p=OP2P5P3P1H08p=DP5g00JbR8g00KAR9P9g00KaR:P2P3g00LAP1CUg00LhR;Fnp==P3P8P9P9P:P1Eyp=m1h21p=8Ax231p=5P7P8P9P9P:P5P3P1Gwp=6P3P8P9P9P:P1P;Fnp=[10319425p=P1\41p=7g00j@#vg003nR;#2R<#2R=#2R>#sR?#p#uR@1075/l3P21067RA&06@RBf7RCf6RD/:1't1o@534%2?R?#pRE#uRF1:CDf5RG'c1:C334[XV21:GA,tD1o@354BPC10G6,:DRBP5P1H0A1aEB%_<RB'1#BP210DGR@,:C,aE111B#BX32P1%_?RA-0;BRH9<@CRI1kC@Ej11IB#BP2f8RI,0CR@/1HRJ101C%i<RK'g,YEf9RL10ICRM':RN54FX32%s?#L#L#L#L#L#L#L#_R?=M@D/KB%BBRO#bRP10ILRQ?M?CRRPBPRPB11RBDH[1ERB1C4BRRf:RS,0L?M?IRT/1BRU?>UB[1FTB1CB4RTf;RU,0SRV?M?LRW/1BRX=@BX[1IWBf<RW,0U?M?SRX/GB\O1?XBf=RX,0WRY?M?URZ?JBZ\O19ZBP2f>RZ=<X??<WBP2f?R[,0ZR\/K?%B?R]#bR^f@R_,0[R`P?P`P?11`?DH[1E`?1C4?R`fARa,0_Rb/1?Rc?>c?[1Fb?1C?4RbfBRc,0aRd/1?Re=@?e[1Id?fCRd,0cRe/G?\]1?e?fDRe,0dRf?J?f\]19f?P2fERf=<e?P2PfPefFRgP?C;/KBPgPffGRhP?C;RiPBPiPB11iBDH\P1EiBPhPgfHRiP?C;Rj/1BRk?>kB\R1FjBPiPhfIRjP?C;Rk/1BRl=@Bl\T1IkBPjPifJRiP?C;Rk/GB\O1?kBPiPjfKRjP?C;Rk?JBk\O19kBP2PjPifLRiP?C;/1BP2fMRk93ij/K?fNRl93kiRmP?PmP?11m?DH\^1Em?fORm93lkR^/1?Rn?>n?\`1F^?fPR^93mlR`/1?Rn=@?n\b1I`?fQR`93^mRb/G?\]1?b?fRRb93`^Rn?J?n\]19n?P2PbP`fSRnP?C;P2g00J6Ro%i;-0@2Rpg017GRq#ARr#ARs#ARt#A#ARu#ARv#ARw#NRx5W2%Nv9W2pRv%Nu%NtRt%NsRs%NrRr9W2p'`3S3S%Aw#NAW2pt1`sr5Sv7Sx1r2q,`rg017f+0?'q'q&0>oRr40=%voRo%OI&0<2Rq7D6%OS?DDq7D5%OL?DGq%OU?DCq7D77D3&0:2Rq&092RxPx1]2?Rv1]24Rs5=x,mxRt&079Rp%R;Rw#2#8Ru%8=Ry'5%Rw#8Rz'5%R<R{#R#89T2v%R=#8R='55=xC6PpPxPx1]2BR|==xs,mxR}Pp%2{#89T2|%8<R<'59=x=C6PpPxPxPtPp15uz%8>9T2v%8wRw'55=xC6PpPxPxP2Psg00aERvP|CU,[xPpPxP8P9P9P:P2Psg018R1h2;R;CU,[xP2P;PvP|CU,[xK05C6PpPxPxP}Pp15wy%8{9T2|/5;5=xC6PpPxA=x<sPpA=x;sC6C6C6C6C6C6204x:R:P1P5g00MHRsg00MhRp'X20315=4spdB02243H01RpbKbLbMX02X12X22XP2XQ2XR2XS2XT2XU2XN2XO2g00`LRs\]R]A3D6C1Q?U;PL[Ps\ORs1QBU=PS7[1Q?S=PQG\]A>66B\R1QBL=P@G\s%BDRsPs[[[[[[^02^12^22^P2^Q2^R2^S2^T2^U2^N2^O2P1P5PLP3P_fURsfTR@PhPnP[PIPgPCPZPfPjPiPkOAbJb^bZb?b>b=b<b;b]bYb:b9b8b7bGb\bXbFbEbDbCbBb[bWbAb@b6b5b4A<JDB#BP2AMQHCRJ1YE110LIRj,:S54FX3210MLRMP210QCRL/1HA<jSH,l1X32P2P2%eL%eMPHPHP2P2\2RjP0P0PLPMPj\2/X0200BA%7A1C4HR0[\R%7BRjg00`iRMA~BA3UWH%7HRA\M^Hj1VVH%7V11YHRY#7\A[A3USWRS/VH%7SPXPWPZPHC;RW#7RS\A[10YURY/VB%7Y11\H?<XB#7\j[1VWBA3[Z_RW/1HR\/1B#7\j\SA3ZX[/KH%BHRZ#bRXPWPHPWPHP\DH[1EWHA3_[aR[/1HRW?>WH\01F[H1CH4R4A3a_cR_/1HR[=@H[[1I_HA3cadRa/GH\Z1?aHA3dceRc?JHc\Z19cHP2PePdPfPHC;P21K1BP3PBP3PB113BDH\P1E3B115BRf?>fB\R1F5B117BRf=@Bf\T1I7B1G6B\O1?6BAJGBG\O19GBP211DBP210ik/KH10klRkPHPkPH11kHDH\X1EkH10lmRl/1HRk?>kH\01FlH10m^Rm/1HRl=@Hl\41ImH10^`R^/GH\Z1?^H10`bR`?JH`\Z19`HP2A<bnHP2101b/KB103nRnPBPnPB11nBDH\P1EnB105@R@/1BRn?>nB\R1F@B107sRs/1BR@=@B@\T1IsBfV,06R6/GB\O1?6BfW,0GRG?JBG\O19GBP2fX=<DBP2PrPo%O5%O77D3Pq15;</5w15;w/5<5=xP:PpbKbLbMX02X12X22A31351015;P3^02^12^22P1fZf\f[O3bJb^bZb?b>b=b<b;b]bYb:b9b8b7bGb\bXbFbEbDbCbBb[bWbAb@b6b5b4babbbcbdbebfGf1X2HGf11JHA}QCHEZ5|J1YEJ=4FNe1gJK1{J1EZb_1:ICRJ,aE1kICEZ1cJD10CD,:I54FebIbIW`P5P1EjW4WkXV2Xi2Xg2Xh2Wjo"). Qed.

(* [comment removed for export] *)
Lemma rl_addi_lit : forall d c e c', c + e = c' -> v_addi (rl d c) e = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02c'h11Hh21ch31dh41ep;2p;3p;1p;6g0023j22Tg005nj33Tg000Mj10Tg0012j14Tg001Pj18Tg00:Bj21Tg00I;j27Tg00NHj35Tg00RBj66Tg003PR0f2R1f1R2'2f0R3530P0f3R4/21g003n#0#0#0#0#0#0#4#8f5R5f4R6'1/74115333X00A5641P2P3E6W1X00X40X20W3o"). Qed.
Lemma rl_btgt_lit : forall d c e c', c + e = c' -> btgt (rl d c) e = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02c'h11Hh21ch31dh41ep;2p;3p;1p;6g0023j22Tg005nj33Tg000Mj10Tg0012j14Tg001Pj18Tg00:Bj21Tg00OGj27Tg0199j35Tg00RBj66Tg003PR0f2R1f1R2'2f0R3530P0f3R4/21g003n#0#0#0#0#0#0#4#8f5R5f4R6'1/74115333X00A5641P2P3E6W1X00X40X20W3o"). Qed.
Lemma rl_auipc_lit : forall d c e c', c + e = c' -> v_auipc (rl d c) e = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02c'h11Hh21ch31dh41ep;2p;3p;1p;6g0023j22Tg005nj33Tg000Mj10Tg0012j14Tg001Pj18Tg00:Bj21Tg00Pgj27Tg01:8j35Tg00RBj66Tg003PR0f2R1f1R2'2f0R3530P0f3R4/21g003n#0#0#0#0#0#0#4#8f5R5f4R6'1/74115333X00A5641P2P3E6W1X00X40X20W3o"). Qed.
Lemma rl_at_lit : forall d c e c', c + e = c' -> at_ (rl d c) e = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02c'h11Hh21ch31dh41ep;2p;3p;1p;6g0023j22Tg005nj33Tg000Mj10Tg0012j14Tg001Pj18Tg00:Bj21Tg01;8j27Tg01;mj35Tg00RBj66Tg003PR0f2R1f1R2'2f0R3530P0f3R4/21g003n#0#0#0#0#0#0#4#8f5R5f4R6'1/74115333X00A5641P2P3E6W1X00X40X20W3o"). Qed.
Lemma rl_num_lit : forall d c c', c = c' -> rl d c = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02c'h11Hh21ch31dp;3p;1p;2p;6g005nj32Tg000Mj10Tg0012j14Tg001Pj13Tg00:Bj21Tg0036j26Tg00RBj65Tg003PR0f1R1f0R2520P0f2R3g003n#0#0#0#0#0#0#4#3R4f4R5f3R6'1115232X001163,64P1P2E5W1X00X20W3o"). Qed.

(* [comment removed for export] *)
Lemma rl_eqb_same : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 ->
  c_eq (rl d c1) (rl d c2) = (c1 =? c2).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "p'0h02H1h11Hh22H2h32Hah44__x1h54__x2h64__x3h72c1h81xh91yh:1zh;2H0h<1Nh=7__arithh>4__ffh?6__sat3h@6__sat4hA8__varmaphB5__withC1bi001bhD2c2hE1dhF1ei011ehG1ri021ri031np;2p;1p;3p;7p;4p;8p;6g0023j20Tg000Mj16Tg004Sj1=Tg0051j2fTg00;Xj22Tg009gR0j28Tg0012j1TTg00:Bj29Tg006Hj2;Tg00f0j24Tg005nj35Tg01<jj2FTg01=LR1j2dTg01=oj1^Tg008kj7Zj6BTg00X>j17Tg01>Qj2WTg00^:j2VTg00^bj3UTg010Lj1STg011Tj2?Tg00noj1RTg00okj2OTg010kj3NTg016:j3MTg012=j2LTg00>Qj1KTg013Uj3JTg00?1j1ITg00?Qj2>Tg00?oj4HTg00@Mj1GTg00@kj1PTg00AVj2:Tg00B\j1QTg00CAj4CTg00fkj1eTg00B9j3DTg016cj8cTg00DPj2bTg0036j2_Tg00E2j2]Tg00E^j3\Tg00F=j4[Tg01?2j3ATg01?nj2YTg00;<j2XTg00Clj7`Tg00\2j6aTg00=WR2f0R3'Xp=1g003PR4f1R5;53p=3g00MHR6g00k?753p=<P5g00JbR7g00KAR8P8g00KaR9P3g00LhF`p=@P5P7P8P8P9P3Eap=Ef2R:,05R;#1g003nR<#6R=#=R>%6=#6#6#6#6R?#=R@'fRA,2;'8f3RB,05RC#112CA'8P4f4RC,0B%T?R?f5RD/9B';,4314CBRE556X:4P410:C10CD/43=56EX:41FB:13B:14B:RF'dPEP6P113DCf7R1f8RE'0f6RG/0ERH'4=565P513GDRIP4PGf9RG,03RJ#112JA'8f:RJ,0510EJ'4g00MhRK556]0X74%1H12HA'8101GRH#^W0P1P3PDFZWFP3O1%7IP01453#<13:5#7RI[1353#714:5#<[RD%<F\I1W53P3n2001000000120000000X94X84PD^94^84P310EGPH1V>@122>%1@122A[[%1>RHg00`iREAU>@5UW3%1A\E^3HP0f;RH,0GRG#112GAf<RG,0H10JG'3#7P1f=,0H#1f>RH,0G/2AP0f?R0,0HR1#1121Af@R1,0010H1'3#7PGfARH,01#1fBR1,0H/2Ag00J6RAg017GRH#S,?4%R<,O41?4H5N45M4g017f'L%KA3J%IAP41>4:P51>4BCH%G4%P4RAP7P8P8P9P41:4<R7g00LARH%Q<,:4R<CC,@A,EA%e8P41:4=R=9D47PHAD4<=CC,@A,EAGc1bA9P3P:1_6K1]3:=56KdA\425C[b>bAbBX44X54X64133:g00`LR2[10B:,3;P2[[^44^54^64P3P1fDfCPGO4b=W2W0P5P3O2n2001000000120000000W;W1P5P3O2n2001000000121000000b?b@O3b1W<P3O1n10210010200021010111103bCbG19C:RG,;?AAC:3EB19CBR:,;?AACB5EB1Y:G=56FeW2W0XD4X74XE4o"). Qed.

Lemma rl_ltu_same : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 ->
  c_ltu (rl d c1) (rl d c2) = (c1 <? c2).
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "p'0h01Hh14__x1h24__x2h34__x3h42H1h52H2h62H0h72Hah81Lh97__arithh:4__ffh;6__sat3h<6__sat4h=8__varmaph>5__with?1mh@1nhA1xhB1yhC1zhD1bi001bhE2b0hF2c1hG2c2hH1dp;2p;1p;3p;4p;6p;7p;8g0023j20Tg000Mj15Tg004Sj1@Tg0051j2[Tg00;Xj21Tg009gR0j2ATg0012j1NTg00:Bj2;Tg006Hj2:Tg01@gj24Tg005nj36Tg01ADj2ETg00;<j22Tg01AfR1j3XTg01BJj2VTg00^:j2UTg00^bj3TTg00>Qj1RTg00?1j1QTg00?Qj2BTg00?oj4MTg00@Mj1LTg00@kj1KTg00AVj2<Tg00B\j1JTg00CAj48Tg00fkj1ITg00B9j3>Tg00DPj2HTg0036j2GTg00E2j2FTg00E^j3OTg00F=j4PTg01Bjj2STg01?2j3CTg008kj6DTg01CJj2ZTg00Clj7YTg016cj8WTg00=WR2f0R3'2p=3g00MHR4g00MhR5763p=9f1R6g00JbR7g00KAR8P8g00KaR9P3g00LhFYp=7f3R:P7P8P8P9f2R7P6P3GWp=?g00k?9643p==g003PR;1067R<#3g003nR=#5R>#@R?%5>#5#5#5#5R@#@RA'[RB,1<'A106:RC#311CB'AP;f4RC,0:%N@R@f5RD/;:':,4314C:RE564XC;P;107C10CD/43=64EXC;1E:711:7127:14:7RF3XPEP4P111DC12CDf7R1f8RE'0f6RG/0E'4=646P611GDP01463RH#91176RI[11631476RJ#9[RK%9F\I1V63P3n2001000000120000000X?;X@;PK^?;^@;P3f9RK,0ERE101KRI1U?ARL112?%3A112B[[RM%3?RNg00`iROAT?A6UW7RA%3B\O^7NRNP0f;RO,0KRK#3R?11KBRKf<RP,0ORQf:/0PRR'1P1f=,0O#3ROf>RS,0P/1BRTP0f?RU,0SRV#3RW11VBRVf@RX,0URU10SXRS'1PPfARY,0X#3RXfBRZ,0Y/1BRBg00J6RY#RR[%QYRYP;1B;7P61B;:CMR\%L;R]%K;R^P;1<;=R_g00aER`%J=,<;R=C8,7^%I8R8P;1<;>R>9>;_RaP`A>;=>R>C8,7^C?1H^9R9P3P71G451F37#9dAO;26CPR2b:b=b>X1;X2;X3;113710:7R5,1<[^1;^2;^3;P3PZfDR`fCRbPPO4b9W5W4P6P3O2n2001000000120000000W6W0P6P3O2n2001000000120000000b;b<O3b0W8P3O112DGP0%=H1267RH[1236%=J[RJ%=F\H1S63P3n2001000000120000000XB;XA;PJ^B;^A;P3PEPIPLPMPAPNP0P?PK12RQP1P0PWPV12SUPPP[PYP\P]P^P;P_g018RR_P=C8,7^P8P;PaP_P>C8,7^C?P9P2b:b=b>X1;X2;X3;123712<5[^1;^2;^3;P3PbP`PZPPO4b9X5BX4XP6P3O2n2001000000120000000X6TX0OP6P3O2n2001000000120000000b;b<O3b0W8P3O1n200210000000021100011000bEbD1;C7RO,:@ACC73ED1;C:R7,:@ACC:6ED1Z7O=64FeW5W4XG;XF;WHo"). Qed.

Lemma rl_inj : forall d c1 c2, 0 <= c1 + d < 2^64 -> 0 <= c2 + d < 2^64 -> rl d c1 = rl d c2 -> c1 = c2.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h01Eh12H1h22H2h32Hah44__x1h54__x2h64__x3h71zh81Hh92H0h:7__arithh;4__ffh<6__sat3h=6__sat4h>8__varmaph?5__with@2c1hA2c2hB1dp;2p;1p;3p;6p;4p;8p;7g0023j20Tg000Mj15Tg004Sj1@Tg0051j2^Tg00;Xj23Tg009gR0j2=Tg0012j1NTg001Pj1JTg00:Bj24Tg005nj38Tg006Hj1Cj26Tg01DDj6BTg01?2j3ATg00RBj6?Tg00^:j2VTg00^bj3UTg00noj1RTg00okj2QTg010Lj1PTg011Tj2<Tg010kj3MTg016:j3LTg012=j2ITg00>Qj1HTg013Uj3GTg00?1j1FTg00?Qj2;Tg00?oj4KTg00@Mj1ETg00@kj1DTg00AVj27Tg00B\j1OTg00B9j39Tg00CAj4:Tg00fkj1STg016cj8TTg00DPj2]Tg0036j2\Tg00E2j2[Tg00E^j3ZTg00F=j4YTg00;<j2XTg00Clj7WTg00=WR1f0R2'Xp=2g003PR3f1R4;82p=1P4g00JbR5g00KAR6P6g00KaR7P2g00LhFWp=>f2R8,04R9#2g003nR:#5R;#@R<%5;#5#5#5#5R=#@R>'^R?,39'=f3R@,04RA#213A?'=%N=R=#JRAf4RB/4@14B838PAP3%C=f5RA/4BRC14A@RDP2EB16=C16=D'1P3f6RD/4A,6=f7RC/4A,6=RE,12X73P210ADRFAADA@E?14DB,6=,1FP3PEf8RE,0C/12X73P210ACRFAACA@E?10DC/1F1V<>131<%2>131?[[%2<RFg00`iRCAU<>4UW3%2?\C^3FP0f:RF,0ERE#213E?f9,1FPDf<,0F#2f;RFf=RD'0/3?P0f>R0,0DRE#213E?110DPFf?f@R0'0#2fARD,00/3?g00J6R?%R:,Q3g017GR0#P,<35M31<305L3g017f'I%H?3G%F?P31;38P41;3@CK%E3%D3R@P5P6P6P7P3173:R5%O:,73R:593g00LAR?173;R;=93:C:,>@%S6P3P5P?P;C:,>@GT1]@7P2P8g00MHR@g00MhR7'\1[28=8@7dAZ314CYb;b>b?X43X53X631028/191148[^43^53^63P2fCPDfBPFO4b:W2W1P4P2O2n2001000000120000000W9W8P4P2O2n2001000000121000000b<b=b0b0b0W0W2W1XA3X@3XB3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint dlookup (t : list (positive * Z)) (b : positive) : Z :=
  match t with
  | [] => 0
  | (b', d) :: t' => if Pos.eqb b b' then d else dlookup t' b
  end.

(* [comment removed for export] *)
Fixpoint slookup (t : list (Z * Z)) (c : Z) : Z :=
  match t with
  | [] => 0
  | (c', w) :: t' => if Z.eqb c c' then w else slookup t' c
  end.

(* [comment removed for export] *)
Definition DELTA_LO : Z := - 2^16.
Definition DELTA_HI : Z := 2^32.
Definition dtab_ok (t : list (positive * Z)) : bool :=
  forallb (fun bd => (DELTA_LO <=? snd bd) && (snd bd <=? DELTA_HI)) t.

Class Reloc := {
  rl_segs : list Segment;              (* [comment removed for export] *)
  rl_dtab : list (positive * Z);       (* [comment removed for export] *)
  rl_stab : list (Z * Z);              (* [comment removed for export] *)
  rl_img_lo : Z;                       (* [comment removed for export] *)
  rl_rw_lo : Z;                        (* [comment removed for export] *)
  rl_img_hi : Z;
  rl_dtab_ok : dtab_ok rl_dtab = true
}.

Definition rl_delta {RL : Reloc} (b : positive) : Z := dlookup rl_dtab b.
Arguments rl_delta : simpl never.

Lemma dlookup_bd : forall t b, dtab_ok t = true -> DELTA_LO <= dlookup t b <= DELTA_HI.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "p'0h02Hah11Hh21bi001bh31th42H1h52Hbh67__arithh74__ffh88__varmaph95__with:4__x1h;4__x2h<4__x3h=1mh>1nh?2H2h@2IHhA6__sat0hB6__sat1hC6__sat2hD6__sat3hE1ahF2b'hG2b0hH2bdhI1dhJ1li011pi021zp;2p;1p;3p;4p;5p;7p;8g01DaR0j2fTg00?1j1OTg01EAj1;Tg01F@j27Tg009gR1j22Tg00>Qj1FTg000Mj18Tg004Sj1?Tg00^:j2CTg00;Xj2ATg00;<j21Tg0051j2KTg00^bj3NTg00[1j1\Tg00@Mj1ZTg00@kj1YTg00[Oj2JTg0012j1ITg00_Fj3HTg01G?j2XTg00DPj2WTg0036j2VTg00E2j2UTg00E^j3TTg00F=j4STg01Gbj1RTg013Uj3=Tg01H?j4DTg01H_j2<Tg01I=j3QTg01IZj3@Tg01J6j3ETg01JYj2PTg01K8j2>Tg01KUj2eTg00?Qj2LTg00?oj4dTg00AVj2BTg00B\j1cTg00fkj1bTg01L5j5[Tg005nj3]Tg00CAj4^Tg00Clj7_Tg014Xj7`Tg016cj8aTg00MHR2f0R3g00MhR43]p=0g01LWR5/13p=3g01MWR6,13p=4g003PR7f1R8g018RP3C^p=9P8g00JbR9g00KAR:P:g00KaR;P3g00LhF_p=:f2R<P9P:P:P;P8P3F`p=G1>53p=61>36p=5f3R=P9P:P:P;P<P8P3Gap=Mg01NWR9/f7R>#OR?P>%;8#017<8R@#3%4@'2[^29R@X3?%F>RA#;#0g003nRB#8RC#?RD%8C#8#8RE#8RF#?RG'Cg00=WRH/ADRI11HG1KDGRJ,AH[[11HDRKg00`iRLANDG8UW011HJRJ\L^0K%?ERG,CD11HG1KDGRM,AH[\IANDG8VLX0K11HM\L^0Kg00J6RK#FRL%OKRK%\7%Z7RG%Y7RI1J7DRD%IE5H7,X71J7HRE'9,:I%IF9H7D,9E,:I3G1WI;R;P3P<1V241U3<#0dAT7H8CSR4b7b8b9%RM/1H/2JP3b6bAbBbCbD115H11H6'2e17A8RA#3%4A'2eW1X29P0P9P7A=>=<#;#0f4R0==>=/78RA#3%4A'2[^29\@^J?P3P9P7P0P=CD==><#;#0%60%50'<RAAQ973RH#6%5H'<XH>RH=@>=RJ;E3%0A%0J'2P1f5RJ#6%5J'<#0A@>H0#0P2P7f7RA,P=f6RM17J=n0100000020000RE#3%4E'2P3%6A%5A'<#0A@>HA#0f:RH,PMP2P2P2P7P3f;R2f8RM,7Hn0100000020000RE#3%4E'2P3%6HRE%5HRH;E<%0E%0H'2P1%62#0%52#0f<R2#3%42'2P3f=#6#0f>#5#0P11>83#011<8[R111831><8#0R2[11=<\21e83P8n2001000000120000000X=7X>7R2P1^=7^>7R1P3P5f@RHP<O3%3HP2P1P3fBR1P6P=O3%41PLPKP71L7<P81L7=CdPGPI1B7CRC%cB,B7'9,:IRG%b:R:PI1B7B/9C,:IRCP:AGICGCMCMP;P4b7b8b9X:7X;7X<7118<R411<=11=0'2\4[^:7^;7^<7P3P6fDP5P8P=O5b6b5b1b0b1W5W0P8P3O2n2001000000121000000b4PMPAP8O2n0110000020100bGW?W4P8P3O2n2001000000121000000b1P9P7PJP0CD==>=/78R=#3%4='2eW1X29X@@X3?XI7XF9P8P3O2n2001101000121101102XE>P3D[W3o"). Qed.

Lemma rl_delta_bd : forall {RL : Reloc} b, - 2^16 <= rl_delta b <= 2^32.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02RLh11bp;1p;3g01O<j12Tg01P;j11Tg01Q=j30Tg01R?g01NWf1R0#2f0%1030W1W0o"). Qed.

(* [comment removed for export] *)
Lemma rl_delta_u : forall {RL : Reloc} b c, 2^16 <= c < 2^63 -> bv_unsigned (rl (rl_delta b) c) = c + rl_delta b.
Proof.
ltac2:(KReplay.run1 (kr_t_Reloc ()) [] "h02Hah14__x1h24__x2h31Hh42Hch52RLh67__arithh74__ffh86__sat0h96__sat1h:6__sat2h;6__sat3h<6__sat4h=6__sat5h>6__sat6h?6__sat7h@8__varmaphA5__withB1bhC1cp;1p;2p;3p;4p;7p;8g000Mj13Tg004Sj16Tg0051j2;Tg00;<j22Tg00B\j18Tg00;Xj21Tg009gj25Tg01S>j2QTg01Gbj1MTg01TAj2ATg00^:j2=Tg00^bj3>Tg010Lj1@Tg011Tj27Tg016:j3?Tg012=j2HTg00>Qj1WTg013Uj3GTg00?1j1VTg00?Qj2UTg00[1j1TTg00?oj4PTg00@Mj1OTg00@kj1NTg00[Oj2ETg0012j1<Tg00_Fj3:Tg01G?j2LTg00AVj2DTg00fkj1KTg00CAj4CTg00B9j3JTg00DPj2ITg0036j2RTg00E2j2STg005nj3_Tg00E^j3^Tg00F=j4]Tg0023j2\Tg01?2j3[Tg00Clj7YTg014Xj7XTg016cj8ZTg00=WR0f0R1'2p=0g003PR2f1R3g018RP1CCp=9P3g00JbR4g00KAR5P5g00KaR6P1g00LhFYp=4f2R7P4P5P5P6P3P1FXp=Bf3R8P4P5P5P6P7P3P1GZp=Fg01R?g01NWg003nR4#3R9#6R:%39#3#3R;#6R<';R=/21%84#8#8#8#8R>#6R?,;:R@,11'51Q87%M=RA1A87RB'2%3;RC#6RD,;:RE,2B'5f4/A81=:?110:RB%0?110@[[%0:RFg00`iRGA>:?3UW0%0@\G^0F1=:D%0D110E[\BA>:D3VGX0F%0E\G^0F%3CRD#6R?,=:%0?1;:?RH,10[\BA>:?3VGX0F%0H\G^0F1=:<%0<110=[\BA>:<3VGX0F%0=\G^0Fg00J6RFg017GRG#@R<#@RB#@R?#@,72172B172GRG5?25?2g017fRB'H172?172<=?2G5?2/HB%WF5GF3G%VFP21U27P3%T2CP%O2%N2RF1E2:R:%<;5:2R;,L21D29R9'9,4F%<C9:2:,99,4F5BF%K5R5PF1D24R4,9;,4FP2P4g00aER;%<>9:2:CC,4F5BFP51E20AJ249R4'9,4FP2P4P;%<D9:2:CC,4F5BFCFCF1IF6P1P7g00MHRFg00MhR6'R1S17=_F6dA^203C]b7b@bAX12X2212A3123E'512=3113@'51\78R8#0118H'5[[^12^22P1f=f<'Af;f9f:O4b6b8b9b:b;b<b=b>b?7[7b3W4XC2WBW5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rl_fold_by p d c e L :=
  let c' := vm_eval (c + e)%Z in
  replace p with (rl d c') by (first [ exact (L d c e c' eq_refl) | symmetry; exact (L d c e c' eq_refl) ]).

Ltac rl_pc p :=
  lazymatch p with
  | rl ?d ?c => tryif is_Z_lit c then idtac
                else (let c' := vm_eval c in
                      replace p with (rl d c') by (first [ reflexivity | symmetry; reflexivity ]))
  | v_addi (rl ?d ?c) ?e => rl_fold_by p d c e rl_addi_lit
  | btgt (rl ?d ?c) ?e => rl_fold_by p d c e rl_btgt_lit
  | v_auipc (rl ?d ?c) ?e => rl_fold_by p d c e rl_auipc_lit
  | at_ (rl ?d ?c) ?e => rl_fold_by p d c e rl_at_lit
  | v_jalr (rl ?d ?c) ?e =>
      let c' := vm_eval (c + e)%Z in
      first [ match goal with
              | H : fetch_word _ (rl d c') = Some _ |- _ => rewrite (rl_jalr_fetch _ d c e c' _ eq_refl H)
              | H : ret_ok (rl d c) |- _ =>
                  lazymatch e with 0%Z => rewrite (H : v_jalr (rl d c) 0 = rl d c) end
              end
            | idtac ]
  end.

#[export] Ltac norm_pc_state st ::=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => first [ rl_pc p | wlit p ]
       | _ => idtac
       end.

(* [comment removed for export] *)
Ltac rl_val v :=
  lazymatch v with
  | v_addi (rl ?d ?c) ?e => rl_fold_by v d c e rl_addi_lit
  | v_auipc (rl ?d ?c) ?e => rl_fold_by v d c e rl_auipc_lit
  | at_ (rl ?d ?c) ?e => rl_fold_by v d c e rl_at_lit
  | btgt (rl ?d ?c) ?e => rl_fold_by v d c e rl_btgt_lit
  end.

#[export] Ltac vals_lit ::=
  repeat match goal with
         | |- context [regupd _ _ ?v] => first [ val_lit v | rl_val v ]
         end.

(* [comment removed for export] *)
Ltac rl_norm :=
  repeat match goal with
         | |- context [v_addi (rl ?d ?c) ?e] => rl_val (v_addi (rl d c) e)
         | |- context [v_auipc (rl ?d ?c) ?e] => rl_val (v_auipc (rl d c) e)
         | |- context [at_ (rl ?d ?c) ?e] => rl_val (at_ (rl d c) e)
         | |- context [btgt (rl ?d ?c) ?e] => rl_val (btgt (rl d c) e)
         end.

(* [comment removed for export] *)
Ltac rl_bounds :=
  repeat match goal with
         | |- context [@rl_delta ?RL ?b] =>
             lazymatch goal with
             | _ : - 2^16 <= @rl_delta RL b <= 2^32 |- _ => fail
             | _ => pose proof (@rl_delta_bd RL b)
             end
         end.
Ltac rl_unorm :=
  repeat match goal with
         | |- context [bv_unsigned (rl (@rl_delta ?RL ?b) ?c)] =>
             rewrite (@rl_delta_u RL b c) by lia
         end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rl_to_Z_in H :=
  repeat match type of H with
         | context [rl ?d ?c] =>
             let z := vm_eval (c + d)%Z in
             change (rl d c) with (Z_to_bv 64 z) in H
         end.

Ltac bvlit64_to_Z_in H :=
  repeat match type of H with
         | context [@BV 64 ?z ?p] =>
             replace (@BV 64 z p) with (Z_to_bv 64 z) in H by (apply bv_eq; vm_compute; reflexivity)
         end.
Ltac bvlit64_to_Z :=
  repeat match goal with
         | |- context [@BV 64 ?z ?p] =>
             replace (@BV 64 z p) with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity)
         end.

Ltac rl_tail t :=
  let H := fresh "RLT" in
  pose proof t as H;
  rl_to_Z_in H; bvlit64_to_Z_in H; bvlit64_to_Z;
  exact H.
