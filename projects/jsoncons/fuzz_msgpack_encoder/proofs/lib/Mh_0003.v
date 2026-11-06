(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From Stdlib Require ZArith Lia. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
Module L5FastLiaT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac plia2 := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_st ] ].
Ltac plia1 := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ] ].
(* [comment removed for export] *)
Ltac plia_log := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ]
                       | idtac "PLIA-T2-TRY"; solve [ L5FastLia.prune_arith; L5FastLia.lia_st ]
                       | idtac "PLIA-T3-TRY"; tryif assert_succeeds L5FastLia.plia_last then (idtac "PLIA-T3-OK"; L5FastLia.plia_last) else fail ].
Goal forall x y : Z, (0 <= x)%Z -> (x <= 2 * x)%Z /\ (y = y)%Z.
Proof. intros. split. plia2. plia1. Qed.

End L5FastLiaT.
From Stdlib Require ZArith List Lia Bool. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module As0Tables.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_As0Tables () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib9micromega5Tauto5eKindI46Stdlib9micromega5Tauto8GFormula00c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab4shadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab;kHighMemEndC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab7app_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6in_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01C46Stdlib4Bool4Bool=andb_true_iffK46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6BIG_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6BIG_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6rz_logC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6of_natc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab5ziotaC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6zrangeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab:class_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab:max_cachedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab>chunks_per_mapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab8class_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab8in_ziotaC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab8class_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab?class_id_ok_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab<from_primaryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab<sec_map_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6neededC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7mod_mulc69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab8round_upC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AsanTab.

(* [comment removed for export] *)
Definition SB : Z := 0x7fff8000.
Definition shad (a : Z) : Z := a / 8 + SB.
(* [comment removed for export] *)
Definition BIG_LO : Z := 0x7fff7000.
Definition BIG_HI : Z := 0x10007fff8000.
Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighMemBeg : Z := 0x10007fff8000.   (* [comment removed for export] *)
Definition kHighMemEnd : Z := 2 ^ 47 - 1.
(* [comment removed for export] *)
Definition in_mem (a : Z) : bool := (a <=? kLowMemEnd) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).
(* [comment removed for export] *)
Definition app_mem (a n : Z) : Prop := a + n <= BIG_LO \/ BIG_HI <= a.

Lemma kHighMemBeg_eq : kHighMemBeg = shad kHighMemEnd + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g003Xj13Tg004[j12Tg0059j20Tg005Vj21Tg0060g006N#3g007X#2'0'1o"). Qed.
Lemma in_mem_app : forall a n i, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 -> app_mem a n -> 0 <= i < n -> in_mem (a + i) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h02H0h14__p1h24__x1h34__x2h44__x3h52b1h62b2h72Hah87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>1nh?1Hh@2HihA1mhB2HnhC4HtophD1ahE1ip;2p;1p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002UR0p4p711g008=R1p4p73101p8g008aj2:Tg0059j23Tg009=j14Tg004[j1?Tg009bj2ZTg00:?j21Tg00:[j2TTg00;aR2j2<Tg00<<j1FTg00=Aj2BTg00=^R3j2LTg00>8j2nTg00>Xj15Tg00?=j29Tg00?Zj2XTg00@7j2@Tg00@Uj2WTg00A5j2VTg00A]j3UTg00BAj1JTg00B`j2ATg00CIj3ITg00D2j2STg00D^j1RTg00E>j3QTg00E^j1OTg00F>j2ETg00F\j4HTg00G:j1NTg00GXj1PTg00HCj2CTg00Hfj4DTg00IQj1oTg00J3j3KTg00JVj2>Tg00K9j2mTg005Vj2lTg00K[j2kTg00LGj3]Tg00Lfj4_Tg00MXj3`Tg00N2j2\Tg00NSj1aTg00O1j1bTg00OOj3[Tg00P2j3cTg00PUj4dTg00Q0j3eTg00QJj3fTg00Qdj6gTg00RHj7hTg00Rlj7iTP1j8jTg00SPR1f0R4'1p=6%54#5#5#5p=2g00SnR5g00TNR67f4p=0%54#5p=^%44#4#4#4p=7%44#4p=Yf1R7P0g00TnR8P8g00UNR9P4Egp=GP7P0P8P8P9P4g00UnFhp=8f2R:P0P8P8P9P7P4Fip=Mg0060R;P7g00VNP4CDp=;f3R<P0P8P8P9P:P7P4Gjp==%6:1:1:f4R0/3<g007XR=#4R>#?R?%2>R@#?RA'ZRB'1f5RC/T0P3f6R3/3Cg00W5RD'1g00X:RE/13%6C1:C3'<f8RF/33#F#0[P4f7RG/33/1D%631:3G'<RDP21B74#0%0:RH%07RI'LRJ[%04RK,LI1B:7#0[RL1B<:#0\J1n74P4n2001000000120000000X65X55RJPL^65^55RLP4f:RM/3FRF%5=RN#5#2#2#2#4#5#^RO#2#2#2#?RP'9RQ%7>#7#7#2#2#2#2#4#Y#7#7#7#?RR/9F%?=RS,XBRT,9F'@RF%0QRU%0FRVP21974#011:7RW[117419:7#0[RX19<:#0\W1W74P4n2001000000120000000XA;X>;RWPX^A;^>;RXP4f;f9RY'3RZPP1V?AR[1:1?%6A1:1B[[R\%6?R]g00Y?R^AU?A7UW7RA%6B\^^7]R]p-0R^g00Y[R_g00ZGR`#JRa#J,A;1A;a1A;`5I;5I;g00Zf'S%R_3QR`%O_R_P;1E;:RaP71E;<CHRb%N;Rc%P;Rd1GdCP;1C;>R>g00[R1C;NRNCD,8d5MdRe%o8R8Pd1C;=R==K;NRN%7O#7#7#?RO,>;';,8dP8AK;=>Rf1>;P';,8dC=C=1md9R9P4P:1l561k4:#0dA];17C_R6b9b<b=X2;X3;X4;W11:7:,<<Rg137<Rh/1O13:<RO/1P[[^2;^3;^4;^1^P4f<RP#6f=RiPPf>RjPCP3O6b8b:b;O3b03`O3b013YG#F#0RYeW@W?P4O111EGPJPLP4PQPFP21@74#01<HIRH[1<IK1@:7#0[RK1@<:#0\H1\74P4n2001000000120000000X65X55PK^65^55P419RZR519ZTRZ%05%0ZPWPXP4PR13PMRPP[P\PAP]P`P_P;PaP7%a;CHPcPd1>;1/;>,8d1Gd05MdP8Pd1>;RR0/;=,8dP81;0f,8dC=C=P9P6b9b<b=X2;X3;X1^%67/<:11R711RO[[^2;^3;^1^P41:ijPif?RRP3PGO5b8b:b;O3b0PWPXP4PPPTP[P\PAP]P`P_PbPcPdPeP8Pd1>;?%b@5[;R@,;N,8dP81>;S9c;@,;f,8dC=C=P9P6b9b<b=X2;X3;X4;X1^11hB11OT[\g^2;^3;^4;^1^P4%6iPjPiPRP3PMO6b8b:b;O3b0CdO3b09eUVO3b0PYeX@DW?P4O1n200100000021100011000W0WCWBW7XE;X>;XD;o"). Qed.

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2 ^ rz_log n.
Definition round_up (x m : Z) : Z := (x + m - 1) / m * m.
(* [comment removed for export] *)
Definition needed0 (n : Z) (al16 : bool) : Z := round_up (Z.max n 8) 8 + rz_size n + (if al16 then 16 else 0).   (* [comment removed for export] *)
Definition kMaxSize : Z := 0x10000.
Definition from_primary (n : Z) (al16 : bool) : bool := needed0 n al16 <=? kMaxSize.
(* [comment removed for export] *)
Definition needed (n : Z) (al16 : bool) : Z := if from_primary n al16 then needed0 n al16 else needed0 n al16 + rz_size n.
(* [comment removed for export] *)
Definition user_off (n : Z) : Z := rz_size n.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41bi001bh51np;1p;2p;3p;4p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002UR0p4p711g00RlR1p4p73101p8g00>Xj18Tg009=j15Tg004[j13Tg00?=j20Tg00D^j1CTg00E^j1@Tg00NSj1>Tg00G:j1=Tg00GXj1<Tg00JVj2;Tg00K9j2LTg005Vj2KTg00K[j2JTg00QJj3ITg00LGj3BTg00Lfj4ATg00:?j29Tg00;aj2:Tg00\9j1ETg00Hfj4FTg00RHj7GTP1j7HTf0R1#5#5p=4g00SPR2f2R3'9f1R4/91':p=2P3P0g00TnR5P5g00UNR6g0060R7P4g00VNP1CFg00UnFGp=11;71p=7P3P0P5P5P6P4P1FHp=61921p=?1941,:3p=Dg007XR5#8R0#5R8#5#4R9#3,01g00SnR:P:P:P7P1P2P:P7%59#3R9,03%35R;P:P7%80R<#4#4#4#3R=,03R>%55R5#3R?P:P7%8<#8R@#5#4#4#4#3RA,03%30R0P:P7%8@#4#4#4#4R@#3RB,03%55#3RCP:P7%5@R@#3RD,03%85#3R5P:P7%5@#3R@,03%38R8%3<R<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000RE?2E<P1g00Y[RE#CRF%@ERE%>7RG%=7RH%<7RI1;72RJ=1IJ%7<RK91IJRL361LI6R6P1P3g00TNRM,K:1J13=I:MdAB724CARMb1b2b31922%?<R2':P1b01049P:P:P:P7P1P;P:P7f3R9/0=P?P:P7109AR=P0P:P7109BPCP:P7109DP5P:P7109@P8P<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000R9?29<P1PFPEPGPH%7;R991IJA1I9K56IP6PMb1b2b3A2;;<P1b0P>P:P:P:P7P1P?P:P7f4R>/0AP0P:P710>BRAPCP:P710>DP5P:P710>@P8P<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000R>?2><P1PFPEPGPH%7?R>91IJA1I>K56IP6PMb1b2b3A2??<P1b0P=P:P:P:P7P1P0P:P7f5R=/0BPCP:P710=DRBP5P:P710=@P8P<n0100000020000n0100000020000n0100000020000n0100000020000R=?2=<P1PFPEPGPH%70R=91IJA1I=K56IP6PMb1b2b3A200<P1b0PAP:P:P:P7P1PCP:P7f6RA/0DP5P:P710A@RAP8P<n0100000020000n0100000020000n0100000020000RD?2D<P1PFPEPGPH%7CRD91IJA1IDK56IP6PMb1b2b3A2CC<P1b0PBP:P:P:P7P1P5P:P7f7/0@P8P<n0100000020000n0100000020000R@?2@<P1PFPEPGPH%75R@91IJA1I@K56IP6PMb1b2b3A255<P1b0PAP:P:P:P7P1P8P<n0100000020000R:?2:<P1PFPEPGPH%78R:91IJA1I:K56IP6PMb1b2b3A288<P1b0PFPEPGPHA1IKK96ILP6PMb1b2b3AD2<<P1b0n0110000020000b4n0110000020001b4n0110000020001b4n0110001020001b4n0110001020001b4n0110001020001b4n0110001020001b4%E1R1?21<eX57o"). Qed.
Lemma rz_size_values : forall n, In (rz_size n) [16; 32; 64; 128; 256; 512; 1024; 2048].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h01bi001bh11np;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g00>Xj1<Tg009=j14Tg004[j13Tg00?=j22Tg00D^j1HTg00=^j21Tg00Q0j3=Tg00]>j1GTg00E>j3ETg009bj2DTg00^Dj2CTg00^aj3@Tg00QJj3>Tg005Vj2BTg00MXj3ATf0R0#4#4p=6g0060R1f1R2;E0p=;f3R3f2R4/D2'C=@10p=5A>120p=0g00_8R5,10p=:f4R6=>13A>142/10'1p=81B109A42p=9A>142/10p=?A=4209=63p=7A@120p=Fg007XR7#<R8#4R9#4#6R:#3,20g00SnR;P;%47R<#4R=#6R>#3R?%3<R@P;P1P0g00SPRAP;P1%4:#3R:,24%37R7P;P1%<8RB#6#6#6#3RC,24RDP@P;P1%<B#<RE#4#6#6#6#3RF,24%38R8P;P1%<E#6#6#6#6RE#3RG,24%3=R=P;P1%4ERE#3RH,24%<<#3R<P;P1%4E#3RE,24%39R9%3BRBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000%4>R>#3R4%4>R>#3RI%4>R>#3RJ%4>R>#3RK%4>R>#3RL%4>R>#3RM%4>#3R>%H1';';';';';';';,;?RNC5P010??P4P?PIP?PJP?PKP?PLP?PMP?10>?#:D8D8D8;9?P?P@PAPNC5e122:P;P;P?P@P;P1P0P7P;P1123CP@P;P1123FRCP8P;P1123GP=P;P1123HP<P;P1123EP9PBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?41044R3PIP4PJP4PKP4PLP410>4#:9?M4D8D8R:'1A93:43=P?P@P7PNC5ePDP;P;P?P@P;P1P0P@P;P1126FP8P;P1126GRFP=P;P1126HP<P;P1126EP9PBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?I104IR610IIRDPJPIPKPIPLPIPMPI10>I#:D8D8R7'1R:'1P6P:A9D7ID7P?P@P@PNC5ePCP;P;P?P@P;P1P0P8P;P1f5RC/2GP=P;P112CHRGP<P;P112CEP9PBn0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?J104JRC10IJR710JJRDPKPJPLPJ10>J#:9?MJD8R:'1R6'1R3'1PCP3A9D:J9=76D7P?P@P8PNC5ePFP;P;P?P@P;P1P0P=P;P1f6RF/2HP<P;P112FERFP9PBn0100000020000n0100000020000n0100000020000PNC5P010?K104KRH10IKR810JKR610KKR7PLPKPMPK10>K#:D8R:'1RD'1R3'1RC'1PHPCP8P3P6PDA97:KD7D7P?P@P=PNC5ePGP;P;P?P@P;P1P0P<P;P1f7/2EP9PBn0100000020000n0100000020000PNC5P010?L104LRE10ILRG10JLR=10KLR:10LLR710>L#:9?MLRD'1R6'1R3'1R8'1RC'1PEPCPGP8P=P3A97DL9=:6D7D7P?P@P<PNC5ePFP;P;P?P@P;P1P0P9PBn0100000020000PNC5P010?M104MR;10IMRF10JMR<10KMR610LMR:10MMRD10>M#:R7'1R3'1R='1R8'1RG'1RC'1P;PCPFPGP<P8P6P=P:P3A9D7MD7D7D7P?P@P9PNC5e10?>104>R410I>RI10J>RJ10K>RK10L>RL10M>RM10>>R9#:R7'1RD'1R3'1R:'1R='1R6'1P4P6PIP=PJP:PKP3PLPDA995>9=M7D7D7D7P?P@PBPNC5en0110000020101b0n0110000020101b0n0110000020101b0n0110001020101b0n0110001020101b0n0110001020101b0n0110001020101b0%G0/FNeX11o"). Qed.

(* [comment removed for export] *)
Definition kNumClasses : Z := 32.
Definition class_size (c : Z) : Z :=
  if c <=? 16 then 32 * c
  else let t := Z.shiftl 512 ((c - 16) / 2) in t + (if Z.odd (c - 16) then t / 2 else 0).
(* [comment removed for export] *)
Definition class_id (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := Z.log2 s in
       let hbit := (Z.shiftr s (l - 1)) mod 2 in
       let lbits := s mod 2 ^ (l - 1) in
       2 * l - 2 + hbit + (if lbits =? 0 then 0 else 1).
(* [comment removed for export] *)
Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / class_size c)).
(* [comment removed for export] *)
Definition kRegionSize : Z := 2 ^ 32.
Definition kFreeArrayOffset : Z := 0xE0000000.      (* [comment removed for export] *)
Definition kFreeArraySize : Z := 2 ^ 29.
Definition kUserMapSize : Z := 2 ^ 18.             (* [comment removed for export] *)
Definition kSpaceSize : Z := 2 ^ 37.               (* [comment removed for export] *)
Definition kSpaceReserve : Z := 0x2000011000.      (* [comment removed for export] *)
Definition region_beg (space_beg c : Z) : Z := space_beg + c * kRegionSize.
Definition chunk_addr (space_beg c i : Z) : Z := region_beg space_beg c + i * class_size c.
Definition compact (space_beg c p : Z) : Z := (p - region_beg space_beg c) / 16.
Definition rinfo (space_beg c : Z) : Z := space_beg + kSpaceSize + 128 * c.
(* [comment removed for export] *)
Definition chunks_per_map (c : Z) : Z := kUserMapSize / class_size c.

(* [comment removed for export] *)
Definition sec_map_size (needed_sz : Z) : Z := round_up needed_sz 4096 + 4096.
Definition sec_user (map_beg n : Z) : Z := map_beg + 4096 + rz_size n.

(* [comment removed for export] *)
Definition kQuarantineMax : Z := 2 ^ 28.           (* [comment removed for export] *)
Definition kQuarantineMin : Z := 0xE666661.        (* [comment removed for export] *)
Definition kLocalQuarantineMax : Z := 2 ^ 20.      (* [comment removed for export] *)
Definition kBatchSlots : Z := 1021.
Definition kBatchBytes : Z := 8192.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs_log : Z := 20.
Definition fs_frame_bytes (k : Z) : Z := 64 * 2 ^ k.
Definition fs_nframes (k : Z) : Z := 2 ^ (fs_log - 6 - k).              (* [comment removed for export] *)
Definition fs_flags_off (k : Z) : Z := 4096 + (2 ^ (fs_log - 5) - 2 ^ (fs_log - 5 - k)).   (* [comment removed for export] *)
Definition fs_frame (fs k i : Z) : Z := fs + 4096 + 2 ^ (fs_log - 5) + k * 2 ^ fs_log + i * fs_frame_bytes k.
Definition fs_size : Z := 0xb09000.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kDepotL2Nodes : Z := 2 ^ 16.   (* [comment removed for export] *)
Definition kStoreBlockFrames : Z := 2 ^ 20. (* [comment removed for export] *)
Definition kMaxTraceDepth : Z := 30.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ziota (lo : Z) (k : nat) : list Z := match k with O => [] | S k' => lo :: ziota (lo + 1) k' end.
Definition zrange (lo n : Z) : list Z := ziota lo (Z.to_nat n).
Lemma in_ziota : forall k lo x, lo <= x < lo + Z.of_nat k -> In x (ziota lo k).
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h01xh14__x1h24__x2h31kh42loh51Hh62H0h77__arithh84__ffh94__p1h:8__varmaph;5__with<4__x3h=1ni001nh>2IHh?4cstrh@1ei011ehA1mhB1si021shC1yp;2p;1p;3p;4p;6p;<p;Bp;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002UR0p4p711g008=R1p4p73101p8g00:?j24Tg00_UR2j11Tg00`5j28Tg00^aj39Tg0059R3j20Tg008aR4j25Tg00;aj2ATg00a9j1@Tg00aWj4QTg005Vj2=Tg00b:j6ITg00bcj4KTg00D^j1\Tg00E^j1[Tg00F>j2HTg00NSj1XTg00F\j4GTg00G:j1WTg00GXj1VTg00HCj2DTg009=j1UTg00Hfj4;Tg00JVj2FTg00J3j3:Tg00IQj1PTg00Qdj6OTg00K9j2NTg00K[j2RTg00QJj37Tg00LGj3STg00Lfj4TTg00BAR5j1ETg00cJj2kTg00cjj1BTg00dCR6j2jTg004[j1iTg00=^j2hTg00MXj3gTg00dcj1^Tg00>Xj1]Tg00eHj6_Tg00Q0j3`Tg00elj4aTg00fMl<CTg00g2lBbTg00gXl<cTg00RHj7dTg00Rlj7ZTP1j8YTf3R1f2R7f1R8f0R9'0'5'Ap=2g0060R:/=9p=3g00h=R;P:P:P:P2P2P1P7P8g00ZGR<g00SPR=P9M<Cp=MP:P:P:P:P:P:P3P9P8P7P3P1f4R3f5R>f6R?f7R@f8RAf9MBbp=LP:P:P4P@P4P?P>P3P1P7P8P9M<cp=JP8P0g00TnR4P4g00UNRBP9g00UnFdp=6P:P8g00[RP9C;p=?P7P0P4P4PBP8P9FZp=>P1P0P4P4PBP7P8P9GYp=<P;P;P:P:P5P2P2P1g00h\P7P8P9M<Cp=fP;P:P:P:P2P2P>P3P1P7P8P9M<Cp=e1489R2P9P8%17C2187199:8[^0:^4:R5X3;P2P9P8%1<RCC21478RD107CRE,58RF'APDP8P7P=C2RGPDPFPDP9X0:RFP=O1RH,07RI,58%@DPF1589#@XC:X0:RDP8P8%38PEPIPFPFPFP:P:g00i@1089CQ#3XA:X=:RIP7P7%37PCPHPFPF%19#3X0;RH1=:=CMM:LGJEIP9CKPGp-0RGg00Y[RC#\RE%[CRCP:1H:7RJP8%X:CG%W:RK%V:RLP:g007XRM,D:RNg00VNRO%UM,D:RPC;,6LRQ1F:=9::N,?P,6L5>L%P4RRPLP0P4P4PBP3EOC<1NLBRSP9P7g00SnRTg00TNRU'=1R97=7TUdAS:=8CTRUb8b:b;X1:X2:W91498RTP8P9P=C2P1[^1:^2:^9GP9183<99:1P1P3P8O4b7b6W5X0:X4:P2P9P8%E1#1C21k78A7:78R2%B2'jP6A7:17R6%B6A7:31R6%iMR2,03/8?99:1'hP9A7:>3R<10>2RG/8@99:3RV;g9X@6P9O1%B6P?PGP314>3RG%E@R?#1R6,0>RW,53RX'APGP3P>%1@RY/02C2RZPGPXPGPF1092X0:RXPYO1R[O1R\,0>R],53%@GPFPDP3P3%33PWP]PFPFPFPIP>P>%3>P6P\PFPFPHP?P[PXP@PY%3YCfEeM:LGJEIP1CKPZ%^A%1A,4=PEPCP:PJP81H:1CGPKPL%]M,D:RM1F:2RK5::9::N,?P,6L9>LQPRPLPLP0P4P4PBP:PNg00idPPC;,6LE_PRP:A::NKRKPOPPC;,6LA::KM,?P,6L5>LC<C<PSPUb8b:b;X1:X2:X<:PTP8P91072R2C2A7:87g00_8[1421P1P2P3C2[[^1:^2:^<:P9f:#1P@PAP7P1O5b7b?b6O39`<VW=P9O1n200110200021010111100bB%E3,8799:8eW5X0:X4:X>5X3;P9CaX3;o"). Qed.

Lemma class_size_table :
  map class_size (zrange 1 30)
  = [32; 64; 96; 128; 160; 192; 224; 256; 288; 320; 352; 384; 416; 448; 480; 512;
     768; 1024; 1536; 2048; 3072; 4096; 6144; 8192; 12288; 16384; 24576; 32768; 49152; 65536].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g00E^j1<Tg009=j10Tg00>Xj14Tg00D^j1;Tg005Vj28Tg004[j12Tg00jKj27Tg00kPj46Tg00QJj39Tg00E>j35Tf0R0#0#0p=1g0060R1f2R2#2f1R3#2=51035p=:f4#2f3#2%22%23=510551551551p=3%<1R0g007XR3#0R2#0R4#0#1R5%05R5%43R6#0R7#1#1R8%05R5%42R2#0#1#1R9%08R8%46R6#0#1#1R:%05R5%44#0#1#1%09%42#0#1#1%08R8%47#0#1#1%0:%46#0R6#1#1%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08%05%;13:D3D3D3D3D3D3D3R5'8P1P1g00kl%23%26'7C6=905do"). Qed.

Lemma max_cached_table :
  map max_cached (zrange 1 30) = [16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g00E^j1;Tg009=j11Tg004[j10Tg00>Xj14Tg00D^j1:Tg005Vj28Tg00jKj27Tg00kPj46Tg00QJj35Tg00E>j33Tg0060R0f2R1f1R2f0R353033p=9f4f3A30239301530530p=2%;0R1g007XR3#1R2#1R4#1R5#1#0R6P6P6P6%43R6#1R7#1#0%42#1#0%05R5P5%07R7P7%04R4P4P4P4P4P4%02R2P2P2P2P2P2P2P2P2P2P2P2%:09922D2D2D2D2D2D2D2R2'8P0P0g00m5%03%46#4#1#0'7C6=512do"). Qed.

Lemma chunks_per_map_table :
  map chunks_per_map [1; 2; 3; 6; 7; 8; 16; 19; 21; 23; 24; 30] = [8192; 4096; 2730; 1365; 1170; 1024; 512; 170; 85; 42; 32; 4].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g00E^j19Tg009=j10Tg00>Xj11Tg00D^j15Tg005Vj28Tg00kPj47Tg00QJj36Tg004[j13Tg00E>j34Tg0060R0f4#3f3#3f2#3f1#3f054054054034p=2%90R1g007XR2#0R3#0R4#0R5#0R6#0R7#0#0#0#0R8#0R9#0#0R:#0P:%13R:#0#1R;#0R<#1R=#0R>#1#0#1R?#0P?%14R?#0#0#1#0#0#1#0P9P8P>P=P<P7P4%50R4D2D2D2R7'8P0P0g00n>P2P3%12R2%02R3%12R2P5P6%1?P;%1:#1%03#0%12#0P4D2D2D2C7=617do"). Qed.

(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && ((c =? 1) || (class_size (c - 1) <? s)).
Lemma class_id_ok_all : forallb class_ok (zrange 1 65536) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g005Vj26Tg004[j12Tg00jKj23Tg00oKj35Tg00QJj34Tg009=j11Tf0#1#1p=0g00SnR0g00TNR1'6g0060g00ogg007XR2#2%02#0#0#0#0#0#0#0#2'335=401do"). Qed.

Lemma class_id_ok : forall s, 1 <= s <= 65536 ->
  1 <= class_id s <= 30 /\ s <= class_size (class_id s) /\ (class_id s = 1 \/ class_size (class_id s - 1) < s).
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h01Hh11mh21nh32H4h44__x1h54__x2h61xh74__p1h84__x3h97__arithh:4__ffh;8__varmaph<5__with=2H1h>2H2h?2H3h@4__p2hA4__x4hB2H0hC3HinhD2HshE5lemmahF1shG1yhH2z0p&0p;1p;2p;3p;4p;<p;6p;Bp;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002UR0p4p711g008=R1p4p73101p8g004[j1LTg009=j1GTg00:?j22Tg010nR2j1}Tg00_UR3j1WTg0059R4j2ITg008aR5j24Tg00;aR6j23Tg011Nj2UTg005Vj2BTg011kj3]Tg00a9k108Tg00aWk407Tg00gXl<tTg00b:j6pTg012Qj2nTg00QJj3ETg00=^R7j2>Tg0133j1jTg013Qj2hTg00BAj1MTg00B`j2RTg0142j3dTg00CIj3VTg00D2j2bTg00D^j1aTg00E>j3`Tg00E^j1_Tg00F>j2NTg00NSj1^Tg00F\j4JTg00G:j1\Tg00GXj1[Tg00HCj2KTg00JVj2HTg00Hfj4FTg00IQk105Tg00J3k304Tg00K9j2{Tg00K[j2zTg00LGj3vTg00Lfj4uTg014[j4sTg015Fj4rTg00jKj2qTg00^aj3XTg00oKj3oTg00ogR8j1YTg016Mj2mTg016fj3lTg017Wj3kTg018:j11Tg00?=j28Tg00>Xj1QTg00klj15Tg019Aj2@Tg019^j2ATg00=Aj2PTg01:;j3OTg00@Uj2iTg01:^j3gTg01;:j2xTg01;Zj2yTg00fMl<ZTg00g2lBfTg00Qdj6~Tg00RHj7eTg00Rlk700Tg01<:k701TP1j8cTg00@7k202Tg00?Zk203Tf0R1#G#Gp=Cf2R9f1R:'2/31p=9g0060R;g00h=R<P;P;P2f4R2P3f3R=g01<^P9P:P1M<Zp>06P<P;P;P;P3P3f5R3P2P=P9P:P1M<Zp=|P;P;P;P;P;P;P4P1P:P9P4P=P2P3f6R4f7R>f8R?f9R@MBfp=wAE;:1p=6P:P0g00TnRAPAg00UNRBP1E~p=TP:P0PAPAPBP1g00UnFep==P9P0PAPAPBP:P1K00p=<P;P:g00VNP1CFp=DP9P0PAPAPBP:P1K01p=SP=P0PAPAPBP9P:P1Gcp=:g00SnR0g00TNRC7E1p=018:1-029p=;203:1#5p=718:1=E0Cp=?g007XRD#LRE%GDRF#GRG#C#C#C#C#C#C#C#LRH,21791%}HRIPEP:12E:RJ%WIRK,IERL,4:RM'3g00SPRN/UHRO,IERP,4:RQ,3JPJPMPJPQp-0RQ/BJ9]JJP;P;P5P1X6;RMP514:1R5$08XG;X6;P:P:1B;:PLPPPMPMPMP;P;g00i@1I:1H07,B;X1;X2;PEPE1B;EPKPOPMPM%W1,B;X6<PIPOPM1UN1X6;PHPH1B;HI06E|M:wM<tEp1nNH14NHRM16OH'312HNRIAE;ON'3'>POP;g00Y[RO%jD,h;g00ZGR<#MRK#M#M,R;5d;1R;K1R;<5V;5V;g00Zf'b%aOR<3`%_OROP;1N;9RKP:%^;RPCJ%\;RL%[;RR1TR2P;1K;FRFg00idRS1H;HRTCF,=R5<R1H;N,DT,=R1TR3RU5<R5SR&05ARAPR1H;ERV1K;DRW'D,=RRX1DWT,=R5<RPAP;PWg00[RRTB04;VFCF,=R9<RXC:C:1{RBRBP1P91B0C1z19#0dAv;N:CuRCb:b;b<X4;X5;X7QX@Q16:H,3913I='>12:H,3J1IE=,4999E9[[^4;^5;^7Q^@QP1AE;:NPMP:P2P9P=O6b9bHbBCsCr1qEHRH9X;:RMePMg01=KAo;8H#0RMAX;1H%Y:#0[^6;RN,mMAlMN1WEAk;8HP1O2PNP1P2P9O2%Y2#0%13RN,8E%QDRD#Q#Q#G#LRH7;N%5N7;3R81@NE17NE/A3'PRN;O1%08%0N'3P6%14RN,8E?;NH%5N7;4#01@NE17NE/A4'P#0%1>RN12NH59E%5N16NE17NE/4>'>59>'3P1%1?RN,8E?;NH%5N7;?#0%1@RN/@E17NE/A@'P#0f:R@#1RN,8E?;NHR8%5N,8@RN;O:%08%0N'3P6f;RN#1R8,8E?;8H#0%58,?Nf<RN#1R8128H59E%58168E178E/4N'>59N'3P1f=#1RN,8E?;NH#0f>RN%1N#5'?f?#1RN,8ER818NHRN;O:%08%0N'3P6f@RN#1R8,?E1?8HfAR8#1RM12MH59E%5M16ME17ME/48'>598'3P1fB#1,?EfC#1/?HP61?:1129:[R812:11?9:RM[12=9\M1i:1P:n2001000000120000000X1;X2;RMP8^1;^2;R8P1PEfE#1RJP9O312EJPMP8P1fG#1RJPHP=O312JHPMP8P1fIR8%18#5RMP@O3128MfJRM#1R8/@ERJ178E/AMRM;gN%0J%0M'>P7fKR7#1RM/@E#017ME/A7#0fLR7#1RM12MH59E%5M16ME17MERJ/47'>597'3P11@ME#0P61@:1#0169:[RM16:11@9:#0RN[16=9\N1x:1P:n2001000000120000000X1;X2;PM^1;^2;P1fNRM#1RNPEP:O316NEP<POP;PKP:1N;=RKCJPLPRP;PWPSPVCF,=RRVPAPR1K;D,DF,=RRDPAPR1H;H,DW,=RRWPAPRPXPAA<RXWRSASRVU9<RD5<RC:C:C:C:PBPCb:b;b<X4;X5;X8;X7Q161E129=RU129HR812E=RI122H99E2RH1234R0162ERY/>>'3'3[[[[^4;^5;^8;^7QP1fPRQ#1RZ/7ER[/4Q%5ZR\PQPZP:P4P?P@O8b9b3b0W3P1O11AJ7#0P61A:1#0149:[R61A9:#0RJ\514=9\J1y:1P:n2001000000120000000X1;X2;P6^1;^2;P117NERNPMP:O314NMP<POP;P;1N;2P9PPCJP:PKCJPLPRP;1K;GPTPFCF,=RRFPAPRPDPAPRPWPAPRPXPAASRVF9<RD9<RSC:C:C:C:PBPCb:b;b<X4;X5;X8;XA;14=:14>3,>Y,30,3H\I\8\U[^4;^5;^8;^A;P1P[P\PQPZP:P4P?P@O8b9b3b0W3P1O1n200100000021100011000b3b?b0b>b0b=b0W>W=P:P1O2n2001000000121000000b0W?W0P:P1O2n2001000000121000000b0W3W0P:P1O2n2001000000121000000b0b0b0b0bCWDXF;o"). Qed.

(* [comment removed for export] *)
Lemma examples :
  from_primary 65536 false = false /\ sec_map_size (needed 65536 false) = 73728
  /\ class_id (needed 3 false) = 1 /\ class_id (needed 64 false) = 3 /\ class_id (needed 144 true) = 7
  /\ class_id (needed 100 false) = 6 /\ class_id (needed 1000 false) = 19 /\ class_id (needed 4999 false) = 23
  /\ class_id 8192 = 24 /\ needed 65536 false = 69632.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;3p;1p;2p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p711p10034p4p73101p8g00QJj3;Tg009=j10Tg00>Xj11Tg004[j12Tg00;aj23Tg005Vj2<Tg01>Yj2@Tg01?dj1CTg018:j18Tg01@oj2?Tg00PUj4=Tf0R0#0#0#0#0p=5g0060R1f1R2;;0p=41<10p=>f3R3f2R41<12P0C=p=7f6f5f4P3P4P2P0C=C=p=A%00#0p=:g01B4R3,?0p=9A;142/30p=61320,34p=Bg00SnR4?;33g007XR2#0R0#0R1#1R5#5R6#0#5#5#2R7/47R8%22R9/49R:%12R2#2R;/4;R<%12R=#2R>/4>R?%02R2#2R@/4@RA%15R5#2RB/4BRC%10#1#1#2R0/40RD%02R2#0#2RE/4ERF%01R1#1#5#5#5#2RG/4GRH'3RI'3RJ'3RK'3RL'3RM'3RN'3RO'31<43P8PO%>7P:PNP9P<PMP;P?PLP>PAPKP@PCPJPBPDPIP0PFPHPE%>GC7C7C7C7C7C7C7FA%01#:R1#0#:#5RH#0#:#2RF/@3=;43%9FRF#C/47%9;#8%21#9#8%26g00TN'?#8%12#:#2#9#8%1=#1#0#1#0#:#2#9#8%15#5#1#1#1#2#9#8%2H#814FG76E76076B76@76>76;7693Bdo"). Qed.

(* [comment removed for export] *)
Lemma round_up_8_spec : forall x, 0 <= x -> x <= round_up x 8 < x + 8 /\ round_up x 8 mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71Hh82H0h92Hxh:1xp;2p;1p;4p;6p;3p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g002UR0p4p711g00eHR1p4p73101p8g00:?j21Tg009=j1ATg004[j1DTg0059j24Tg00?Zj28Tg00D^j1ZTg00E^j1VTg00NSj1RTg00G:j1QTg00GXj1NTg00JVj2BTg00Hfj46TP1j6dTg00K9j2bTg005Vj2`Tg00K[j2YTg00QJj39Tg00LGj3WTg00Lfj4UTg01BTj3TTg01C5j2?Tg00^Dj2:Tg01CRj25Tg008aj23Tg01D2j3PTg00;aj22Tg00BAj1=Tg00B`j27Tg00CIj3;Tg00D2j2CTg0133j1MTg013Qj2LTg0142j3OTg00E>j3HTg00F>j2ETg00F\j4KTg00>Xj1STg00HCj2@Tg00IQj1cTg00J3j3GTg00P2j3aTg01DYj3ITg01E<j3_Tg00PUj4[Tg01E]j2\Tg00RHj7]Tg00Rlj7^Tg008=j8XTf1R1P0g00TnR2P2g00UNR3f0R4g00UnF]p=0g0060R5g00SPR6794p=<P5P1g00[RP4C6p=>f2R7P0P2P2P3P1P4F^p=Jf3R8P0P2P2P3P7P1P4GXp=F1164g007XR9#AR:#A#A#DR;,41R<%D9R='8R>g00Y[R?#ZR@%V?RA%R5RB%Q5RC%N5RDP0P2P2P3P51B5;R0g00idRE1B56RFC6,0DEd1bD3R3P4P7g00SnRGg00TNRH'`1Y47=9GHdAW561CURHb1b2b3%<;g00_8[P4b0RG7T;1?>;,:;15>;'4995>147;RI/8=RJP@PAPBPC1>F0,0DP3PHb1b2b3136;P4b07P;15J;RJ,1613J;'2148;RJ/8=/?;RB/:;RK,1813KJ'215K;#<g00ZGRK#=RJ#=RL,75175JRJ175KRK5;55;5g00ZfRM'C%=L,75%M9,L5=O5J=;5K5;5/CM=H?@5H?PAP51E57P11E58CKPCPDP5PFg00VNRF%S9,@5RCC6,0D1>C0,0D5JD%c2R2PDP51@59R9=G50RA1B5=5a5PE1@5:R:9I50=G5CC6,0DP2P5P9PFAI5:0R:C6,0D1>:A,0D5JDCFCFP3PHb1b2b3X45X55X651167137;'21:;7/48995>1:8;R8,17138I'2[[^45^55^65P4f4R4/4;/8=R=/5;1?=;P4P1P7O5b0A_B;GC[b8b71\1;RB,1113B<'215B;#<'2eW9X:5o"). Qed.

End AsanTab.

End As0Tables.
Module ArtSizeLog.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.As0Tables.
Import ListNotations.
Import AsanTab. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
  assert (Hl : Z.log2 (Z.lor a b) < 64).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lor_nonneg a b). lia.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha. pose proof (Z.lor_ldiff_and a b) as E. pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as E2.
  rewrite E in E2.
  replace (Z.land (Z.ldiff a b) (Z.land a b)) with 0 in E2
    by (rewrite (Z.land_comm a b), Z.land_assoc, Z.land_ldiff, Z.land_0_l; reflexivity).
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.

Lemma land_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 64.
Proof. intros a b Ha Hb. pose proof (land_le_l a b ltac:(lia)). assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smear1 (x : Z) : Z := Z.lor x (x / 2 ^ 1).
Definition smear2 (x : Z) : Z := let s := smear1 x in Z.lor s (s / 2 ^ 2).
Definition smear3 (x : Z) : Z := let s := smear2 x in Z.lor s (s / 2 ^ 4).
Definition smear4 (x : Z) : Z := let s := smear3 x in Z.lor s (s / 2 ^ 8).
Definition smear5 (x : Z) : Z := let s := smear4 x in Z.lor s (s / 2 ^ 16).
Definition smear (x : Z) : Z := let s := smear5 x in Z.lor s (s / 2 ^ 32).

(* [comment removed for export] *)
Definition sm_spec (x w s : Z) : Prop := forall i, 0 <= i -> (Z.testbit s i = true <-> exists j, i <= j <= i + w - 1 /\ Z.testbit x j = true).

Lemma sm_spec_0 : forall x, sm_spec x 1 x.
Proof. intros x i Hi. split; [intros H; exists i; split; [lia|exact H] | intros (j & Hj & H); replace i with j by lia; exact H]. Qed.

Lemma sm_spec_step : forall x w s, 0 < w -> sm_spec x w s -> sm_spec x (2 * w) (Z.lor s (s / 2 ^ w)).
Proof.
  intros x w s Hw P i Hi. rewrite Z.lor_spec, Z.div_pow2_bits by lia. rewrite Bool.orb_true_iff.
  rewrite (P i Hi), (P (i + w)%Z ltac:(lia)).
  split.
  - intros [(j & Hj & H)|(j & Hj & H)]; exists j; (split; [lia|exact H]).
  - intros (j & Hj & H). destruct (Z.lt_ge_cases j (i + w)) as [L|R].
    + left. exists j. split; [lia|exact H].
    + right. exists j. split; [lia|exact H].
Qed.

Lemma smear_spec : forall x, sm_spec x 64 (smear x).
Proof.
  intros x. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
  change 64 with (2 * 32). apply sm_spec_step; [lia|].
  change 32 with (2 * 16). apply sm_spec_step; [lia|].
  change 16 with (2 * 8). apply sm_spec_step; [lia|].
  change 8 with (2 * 4). apply sm_spec_step; [lia|].
  change 4 with (2 * 2) at 1. apply sm_spec_step; [lia|].
  change 2 with (2 * 1) at 1. apply sm_spec_step; [lia|]. apply sm_spec_0.
Qed.

Lemma smear_nonneg_aux : forall a k, 0 <= a -> 0 <= Z.lor a (a / 2 ^ k).
Proof. intros a k Ha. apply Z.lor_nonneg. split; [lia|]. destruct (Z.le_gt_cases 0 k). apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]. rewrite Z.pow_neg_r by lia. rewrite Z.div_0_r. lia. Qed.

Lemma smear_nonneg : forall x, 0 <= x -> 0 <= smear x.
Proof.
  intros x Hx. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
  repeat (apply smear_nonneg_aux). lia.
Qed.

Theorem smear_eq : forall x, 0 < x < 2 ^ 64 -> smear x = 2 ^ (Z.log2 x + 1) - 1.
Proof.
  intros x Hx. pose proof (smear_spec x) as P. pose proof (smear_nonneg x ltac:(lia)) as NN.
  assert (HL : 0 <= Z.log2 x) by (apply Z.log2_nonneg).
  assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Z.log2 x + 1) - 1) with (Z.ones (Z.log2 x + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l, <- Z.sub_1_r; reflexivity).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.lt_ge_cases i (Z.log2 x + 1)) as [Lo|Hi'].
  - replace (i <? Z.log2 x + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    apply (proj2 (P i Hi)). exists (Z.log2 x). split; [lia|]. apply Z.bit_log2. lia.
  - replace (i <? Z.log2 x + 1) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.testbit (smear x) i) eqn:E; [|reflexivity]. exfalso.
    apply (proj1 (P i Hi)) in E. destruct E as (j & Hj & Hb). rewrite Z.bits_above_log2 in Hb by lia. discriminate.
Qed.

Lemma smear_range64 : forall x, 0 < x < 2 ^ 64 -> 0 <= smear x < 2 ^ 64.
Proof.
  intros x Hx. rewrite smear_eq by lia. assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). pose proof (Z.log2_nonneg x).
  split. assert (0 < 2 ^ (Z.log2 x + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
  assert (2 ^ (Z.log2 x + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition C55 : Z := 6148914691236517205.   (* [comment removed for export] *)
Definition C33 : Z := 3689348814741910323.   (* [comment removed for export] *)
Definition C0F : Z := 1085102592571150095.   (* [comment removed for export] *)
Definition C01 : Z := 72340172838076673.     (* [comment removed for export] *)
Definition slpop (y : Z) : Z :=
  let t2 := Z.land (y / 2 ^ 1) C55 in
  let t3 := y - t2 in
  let t7 := Z.land t3 C33 + Z.land (t3 / 2 ^ 2) C33 in
  let t9 := t7 + t7 / 2 ^ 4 in
  let t10 := Z.land t9 C0F in
  (t10 * C01) mod 2 ^ 64 / 2 ^ 56.

Definition slpop_ok (L : Z) : bool := slpop (2 ^ 64 - 1 - (2 ^ (L + 1) - 1)) =? 63 - L.
Lemma slpop_ok_all : forallb slpop_ok (zrange 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem slpop_tab : forall L, 0 <= L <= 63 -> slpop (2 ^ 64 - 1 - (2 ^ (L + 1) - 1)) = 63 - L.
Proof.
  intros L HL. assert (Hin : In L (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
  pose proof slpop_ok_all as H. rewrite forallb_forall in H. specialize (H L Hin). unfold slpop_ok in H. apply Z.eqb_eq in H. exact H.
Qed.

Definition lxor63_ok (a : Z) : bool := Z.lxor a 63 =? 63 - a.
Lemma lxor63_all : forallb lxor63_ok (zrange 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem lxor_63 : forall a, 0 <= a <= 63 -> Z.lxor a 63 = 63 - a.
Proof.
  intros a Ha. assert (Hin : In a (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
  pose proof lxor63_all as H. rewrite forallb_forall in H. specialize (H a Hin). unfold lxor63_ok in H. apply Z.eqb_eq in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma slpop_ranges : forall y, 0 <= y < 2 ^ 64 ->
  let t2 := Z.land (y / 2 ^ 1) C55 in
  let t3 := y - t2 in
  let t7 := Z.land t3 C33 + Z.land (t3 / 2 ^ 2) C33 in
  let t9 := t7 + t7 / 2 ^ 4 in
  let t10 := Z.land t9 C0F in
  0 <= t2 <= y / 2 ^ 1 /\ 0 <= y / 2 ^ 1 < 2 ^ 64 /\ 0 <= t3 < 2 ^ 64 /\ 0 <= t3 / 2 ^ 2 < 2 ^ 64 /\ 0 <= Z.land t3 C33 <= C33 /\ 0 <= Z.land (t3 / 2 ^ 2) C33 <= C33
  /\ 0 <= t7 < 2 ^ 63 /\ 0 <= t7 / 2 ^ 4 <= t7 /\ 0 <= t9 < 2 ^ 64 /\ 0 <= t10 < 2 ^ 64.
Proof.
  intros y Hy. cbv zeta. unfold C33, C55, C0F. change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 4) with 16.
  pose proof (Z.div_mod y 2 ltac:(lia)). pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
  set (y2 := y / 2) in *.
  assert (A : 0 <= Z.land y2 6148914691236517205 <= y2).
  { split. apply Z.land_nonneg; lia. apply land_le_l. lia. }
  set (t2 := Z.land y2 6148914691236517205) in *.
  pose proof (Z.div_mod (y - t2) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (y - t2) 4 ltac:(lia)).
  set (t34 := (y - t2) / 4) in *.
  assert (B1 : 0 <= Z.land (y - t2) 3689348814741910323 <= 3689348814741910323).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  assert (B2 : 0 <= Z.land t34 3689348814741910323 <= 3689348814741910323).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  set (t5 := Z.land (y - t2) 3689348814741910323) in *. set (t6 := Z.land t34 3689348814741910323) in *.
  pose proof (Z.div_mod (t5 + t6) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (t5 + t6) 16 ltac:(lia)).
  set (t8 := (t5 + t6) / 16) in *.
  assert (Cc : 0 <= Z.land (t5 + t6 + t8) 1085102592571150095 <= 1085102592571150095).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  lia.
Qed.

End ArtSizeLog.
