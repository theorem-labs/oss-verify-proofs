(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_As0Tables () := "C47Corelib7Classes?RelationClasses9Reflexivec89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab4shadC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab;kHighMemEndC13~~~K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab7app_memC13~~~I47Corelib4Init5Logic3and00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6in_memC13~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01C46Stdlib4Bool4Bool=andb_true_iffK46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6BIG_LOC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6BIG_HIC13~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6rz_logC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab7rz_sizeC13~~~C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6of_natc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab5ziotaC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6zrangeC13~~~C47Corelib5Lists7ListDef3mapc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab:class_sizeC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab:max_cachedC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab>chunks_per_mapC13~~~C46Stdlib5Lists4List7forallbc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab8class_okC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab8in_ziotaC13~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab8class_idC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab?class_id_ok_allC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab<from_primaryC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab<sec_map_sizeC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab6neededC13~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7mod_mulc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab8round_upC13~~~".
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
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg001mj12Tg002Kj20Tg002hj21Tg003Bg003`#3g0058#2'0'1o"). Qed.
Lemma in_mem_app : forall a n i, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 -> app_mem a n -> 0 <= i < n -> in_mem (a + i) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h02H0h14__p1h24__x1h34__x2h44__x3h52b1h62b2h72Hah87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>1nh?1Hh@2HihA1mhB2HnhC4HtophD1ahE1ip;2p;1p;3p;4p;6p;7p;8g005]j2:Tg002Kj23Tg0069j14Tg001mj1?Tg006^j2ZTg007;j21Tg007Wj2TTg008kR0j2<Tg009Fj1FTg00:Yj2BTg00;6R1j2LTg00;Pj2nTg00<0j15Tg00<Uj29Tg00=2j2XTg00=Oj2@Tg00=mj2WTg00>Mj2VTg00?5j3UTg00?Yj1JTg00@8j2ATg00@aj3ITg00AJj2STg00B6j1RTg00BVj3QTg00C6j1OTg00CVj2ETg00D4j4HTg00DRj1NTg00E0j1PTg00E[j2CTg00F>j4DTg00Fij1oTg00GKj3KTg00Gnj2>Tg00HQj2mTg002hj2lTg00I3j2kTg00I_j3]Tg00J>j4_Tg00K0j3`Tg00KJj2\Tg00Kkj1aTg00LIj1bTg00Lgj3[Tg00MJj3cTg00Mmj4dTg00NHj3eTg00Nbj3fTg00O<j6gTg00O`j7hTg00PDj7iTg00Phj8jTg00QLR2f0R3'1p=6%53#5#5#5p=2g00QjR4g00RJR57f3p=0%53#5p=^%43#4#4#4p=7%43#4p=Yf1R6g00RjR7g00SIR8P8g00SiR9P3Egp=GP6P7P8P8P9P3g00TIFhp=8f2R:P7P8P8P9P6P3Fip=Mg003BR;P6g00TiP3CDp=;f3R<P7P8P8P9P:P6P3Gjp==%6:1:2:f4R7/3<g0058R=#4R>#?R?%2>R@#?RA'ZRB'1f5RC/T7P1f6R1/3Cg00UPRD'1g00VcRE/11%6C1:C1'<f8RF/31#F#0[P3f7RG/31/1D%611:1G'<RDP01B63#0%0:RH%06RI'LRJ[%03RK,LI1B:6#0[RL1B<:#0\J1n63P3n2001000000120000000X64X54RJPL^64^54RLP3f:RM/3FRF%5=RN#5#2#2#2#4#5#^RO#2#2#2#?RP'9RQ%7>#7#7#2#2#2#2#4#Y#7#7#7#?RR/9F%?=RS,XBRT,9F'@RF%0QRU%0FRVP01963#011:6RW[116319:6#0[RX19<:#0\W1W63P3n2001000000120000000XA;X>;RWPX^A;^>;RXP3f;f9RY'3RZPP1V?AR[1:2?%6A1:2B[[R\%6?R]g00X6R^AU?A6UW7RA%6B\^^7]R]p-0R^g00XRR_g00Y>R`#JRa#J,A;1A;a1A;`5I;5I;g00Y]'S%R_3QR`%O_R_P;1E;:RaP61E;<CHRb%N;Rc%P;Rd1GdCP;1C;>R>g00ZI1C;NRNCD,8d5MdRe%o8R8Pd1C;=R==K;NRN%7O#7#7#?RO,>;';,8dP8AK;=>Rf1>;P';,8dC=C=1md9R9P3P:1l451k3:#0dA];26C_R5b9b<b=X2;X3;X4;W11:6:,<<Rg136<Rh/1O13:<RO/1P[[^2;^3;^4;^1^P3f<RP#6f=RiPPf>RjPCP1O6b8b:b;O3b03`O3b013YG#F#0RYeW@W?P3O111EGPJPLP3PQPFP01@63#01<HIRH[1<IK1@:6#0[RK1@<:#0\H1\63P3n2001000000120000000X64X54PK^64^54P319RZR419ZTRZ%04%0ZPWPXP3PR13PMRPP[P\PAP]P`P_P;PaP6%a;CHPcPd1>;2/;>,8d1Gd75MdP8Pd1>;RR7/;=,8dP81;7f,8dC=C=P9P5b9b<b=X2;X3;X1^%66/<:11R611RO[[^2;^3;^1^P31:ijPif?RRP1PGO5b8b:b;O3b0PWPXP3PPPTP[P\PAP]P`P_PbPcPdPeP8Pd1>;?%b@5[;R@,;N,8dP81>;S9c;@,;f,8dC=C=P9P5b9b<b=X2;X3;X4;X1^11hB11OT[\g^2;^3;^4;^1^P3%6iPjPiPRP1PMO6b8b:b;O3b0CdO3b09eUVO3b0PYeX@DW?P3O1n200100000021100011000W0WCWBW7XE;X>;XD;o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41bi001bh51np;1p;2p;3p;4p;7g00<0j18Tg0069j15Tg001mj13Tg00<Uj20Tg00B6j1CTg00C6j1@Tg00Kkj1>Tg00DRj1=Tg00E0j1<Tg00Gnj2;Tg00HQj2LTg002hj2KTg00I3j2JTg00Nbj3ITg00I_j3BTg00J>j4ATg007;j29Tg008kj2:Tg00[0j1ETg00F>j4FTg00O`j7GTg00PDj7HTf0R0#5#5p=4g00QLR1f2R2'9f1R3/90':p=2P2g00RjR4g00SIR5P5g00SiR6g003BR7P3g00TiP0CFg00TIFGp=11;70p=7P2P4P5P5P6P3P0FHp=61910p=?1930,:2p=Dg0058R5#8R4#5R8#5#4R9#3,00g00QjR:P:P:P7P0P1P:P7%59#3R9,02%35R;P:P7%84R<#4#4#4#3R=,02R>%55R5#3R?P:P7%8<#8R@#5#4#4#4#3RA,02%34R4P:P7%8@#4#4#4#4R@#3RB,02%55#3RCP:P7%5@R@#3RD,02%85#3R5P:P7%5@#3R@,02%38R8%3<R<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000RE?2E<P0g00XRRE#CRF%@ERE%>7RG%=7RH%<7RI1;71RJ=1IJ%7<RK91IJRL361LI6R6P0P2g00RJRM,K:1J02=I:MdAB713CARMb1b2b31911%?<R1':P0b01039P:P:P:P7P0P;P:P7f3R9/0=P?P:P7109AR=P4P:P7109BPCP:P7109DP5P:P7109@P8P<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000R9?29<P0PFPEPGPH%7;R991IJA1I9K56IP6PMb1b2b3A2;;<P0b0P>P:P:P:P7P0P?P:P7f4R>/0AP4P:P710>BRAPCP:P710>DP5P:P710>@P8P<n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000R>?2><P0PFPEPGPH%7?R>91IJA1I>K56IP6PMb1b2b3A2??<P0b0P=P:P:P:P7P0P4P:P7f5R=/0BPCP:P710=DRBP5P:P710=@P8P<n0100000020000n0100000020000n0100000020000n0100000020000R=?2=<P0PFPEPGPH%74R=91IJA1I=K56IP6PMb1b2b3A244<P0b0PAP:P:P:P7P0PCP:P7f6RA/0DP5P:P710A@RAP8P<n0100000020000n0100000020000n0100000020000RD?2D<P0PFPEPGPH%7CRD91IJA1IDK56IP6PMb1b2b3A2CC<P0b0PBP:P:P:P7P0P5P:P7f7/0@P8P<n0100000020000n0100000020000R@?2@<P0PFPEPGPH%75R@91IJA1I@K56IP6PMb1b2b3A255<P0b0PAP:P:P:P7P0P8P<n0100000020000R:?2:<P0PFPEPGPH%78R:91IJA1I:K56IP6PMb1b2b3A288<P0b0PFPEPGPHA1IKK96ILP6PMb1b2b3AD1<<P0b0n0110000020000b4n0110000020001b4n0110000020001b4n0110001020001b4n0110001020001b4n0110001020001b4n0110001020001b4%E0R0?20<eX57o"). Qed.
Lemma rz_size_values : forall n, In (rz_size n) [16; 32; 64; 128; 256; 512; 1024; 2048].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h01bi001bh11np;1p;2p;3g00<0j1<Tg0069j14Tg001mj13Tg00<Uj22Tg00B6j1HTg00;6j21Tg00NHj3=Tg00\Cj1GTg00BVj3ETg006^j2DTg00]Wj2CTg00^4j3@Tg00Nbj3>Tg002hj2BTg00K0j3ATf0R0#4#4p=6g003BR1f1R2;E0p=;f3R3f2R4/D2'C=@10p=5A>120p=0g00^KR5,10p=:f4R6=>13A>142/10'1p=81B109A42p=9A>142/10p=?A=4209=63p=7A@120p=Fg0058R7#<R8#4R9#4#6R:#3,20g00QjR;P;%47R<#4R=#6R>#3R?%3<R@P;P1P0g00QLRAP;P1%4:#3R:,24%37R7P;P1%<8RB#6#6#6#3RC,24RDP@P;P1%<B#<RE#4#6#6#6#3RF,24%38R8P;P1%<E#6#6#6#6RE#3RG,24%3=R=P;P1%4ERE#3RH,24%<<#3R<P;P1%4E#3RE,24%39R9%3BRBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000%4>R>#3R4%4>R>#3RI%4>R>#3RJ%4>R>#3RK%4>R>#3RL%4>R>#3RM%4>#3R>%H1';';';';';';';,;?RNC5P010??P4P?PIP?PJP?PKP?PLP?PMP?10>?#:D8D8D8;9?P?P@PAPNC5e122:P;P;P?P@P;P1P0P7P;P1123CP@P;P1123FRCP8P;P1123GP=P;P1123HP<P;P1123EP9PBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?41044R3PIP4PJP4PKP4PLP410>4#:9?M4D8D8R:'1A93:43=P?P@P7PNC5ePDP;P;P?P@P;P1P0P@P;P1126FP8P;P1126GRFP=P;P1126HP<P;P1126EP9PBn0100000020000n0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?I104IR610IIRDPJPIPKPIPLPIPMPI10>I#:D8D8R7'1R:'1P6P:A9D7ID7P?P@P@PNC5ePCP;P;P?P@P;P1P0P8P;P1f5RC/2GP=P;P112CHRGP<P;P112CEP9PBn0100000020000n0100000020000n0100000020000n0100000020000PNC5P010?J104JRC10IJR710JJRDPKPJPLPJ10>J#:9?MJD8R:'1R6'1R3'1PCP3A9D:J9=76D7P?P@P8PNC5ePFP;P;P?P@P;P1P0P=P;P1f6RF/2HP<P;P112FERFP9PBn0100000020000n0100000020000n0100000020000PNC5P010?K104KRH10IKR810JKR610KKR7PLPKPMPK10>K#:D8R:'1RD'1R3'1RC'1PHPCP8P3P6PDA97:KD7D7P?P@P=PNC5ePGP;P;P?P@P;P1P0P<P;P1f7/2EP9PBn0100000020000n0100000020000PNC5P010?L104LRE10ILRG10JLR=10KLR:10LLR710>L#:9?MLRD'1R6'1R3'1R8'1RC'1PEPCPGP8P=P3A97DL9=:6D7D7P?P@P<PNC5ePFP;P;P?P@P;P1P0P9PBn0100000020000PNC5P010?M104MR;10IMRF10JMR<10KMR610LMR:10MMRD10>M#:R7'1R3'1R='1R8'1RG'1RC'1P;PCPFPGP<P8P6P=P:P3A9D7MD7D7D7P?P@P9PNC5e10?>104>R410I>RI10J>RJ10K>RK10L>RL10M>RM10>>R9#:R7'1RD'1R3'1R:'1R='1R6'1P4P6PIP=PJP:PKP3PLPDA995>9=M7D7D7D7P?P@PBPNC5en0110000020101b0n0110000020101b0n0110000020101b0n0110001020101b0n0110001020101b0n0110001020101b0n0110001020101b0%G0/FNeX11o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p'0h01xh14__x1h24__x2h31kh42loh51Hh62H0h77__arithh84__ffh94__p1h:8__varmaph;5__with<4__x3h=1ni001nh>2IHh?4cstrh@1ei011ehA1mhB1si021shC1yp;2p;1p;3p;4p;6p;<p;Bp;7p;8g007;j24Tg00^hR0j11Tg00_Hj28Tg00^4j39Tg002KR1j20Tg005]R2j25Tg008kj2ATg00`Zj1@Tg00a8j4QTg002hj2=Tg00a[j6ITg00bDj4KTg00B6j1\Tg00C6j1[Tg00CVj2HTg00Kkj1XTg00D4j4GTg00DRj1WTg00E0j1VTg00E[j2DTg0069j1UTg00F>j4;Tg00Gnj2FTg00GKj3:Tg00Fij1PTg00O<j6OTg00HQj2NTg00I3j2RTg00Nbj37Tg00I_j3STg00J>j4TTg00?YR3j1ETg00bkj2kTg00cKj1BTg00cdR4j2jTg001mj1iTg00;6j2hTg00K0j3gTg00dDj1^Tg00<0j1]Tg00dij6_Tg00NHj3`Tg00eMj4aTg00enl<CTg00fSlBbTg00g9l<cTg00O`j7dTg00PDj7ZTg00Phj8YTf3R5f2R6f1R7f0R8'0'5'Ap=2g003BR9/=8p=3g00g^R:P9P9P9P0P0P5P6P7g00Y>R;g00QLR<P8M<Cp=MP9P9P9P9P9P9P1P8P7P6P1P5f4R1f5R=f6R>f7R?f8R@f9MBbp=LP9P9P2P?P2P>P=P1P5P6P7P8M<cp=JP7g00RjR2g00SIRAPAg00SiRBP8g00TIFdp=6P9P7g00ZIP8C;p=?P6P2PAPAPBP7P8FZp=>P5P2PAPAPBP6P7P8GYp=<P:P:P9P9P3P0P0P5g00h=P6P7P8M<Cp=fP:P9P9P9P0P0P=P1P5P6P7P8M<Cp=e1478R0P8P7%16C218659997[^09^49R3X3:P0P8P7%1;RCC21467RD106CRE,57RF'APDP7P6P<C2RGPDPFPDP8X09RFP<O1RH,06RI,57%@DPF1578#@XC9X09RDP7P7%37PEPIPFPFPFP9P9g00ha1078CQ#3XA9X=9RIP6P6%36PCPHPFPF%18#3X0:RH1=9<CMM:LGJEIP8CKPGp-0RGg00XRRC#\RE%[CRCP91H96RJP7%X9CG%W9RK%V9RLP9g0058RM,D9RNg00TiRO%UM,D9RPC;,6LRQ1F9<9:9N,?P,6L5>L%PARRPLP2PAPAPBP1EOC<1NLBRSP8P6g00QjRTg00RJRU'=1R86=7TUdAS9<7CTRUb8b:b;X19X29W91487RTP7P8P<C2P5[^19^29^9GP8181;9995P5P1P7O4b7b6W5X09X49P0P8P7%E5#1C21k67A7967R0%B0'jP4A7956R4%B4A7915R4%iMR0,01/8>9995'hP8A79=1R;10=0RG/8?9991RV;g8X@4P8O1%B4P>PGP114=1RG%E?R>#1R4,0=RW,51RX'APGP1P=%1?RY/00C2RZPGPXPGPF1080X09RXPYO1R[O1R\,0=R],51%@GPFPDP1P1%31PWP]PFPFPFPIP=P=%3=P4P\PFPFPHP>P[PXP?PY%3YCfEeM:LGJEIP5CKPZ%^@%1@,4<PEPCP9PJP71H95CGPKPL%]M,D9RM1F90RK5:99:9N,?P,6L9>LQPRPLPLP2PAPAPBP9PNg00iEPPC;,6LE_PRP9A:9NKRKPOPPC;,6LA:9KM,?P,6L5>LC<C<PSPUb8b:b;X19X29X<9PTP7P81060R0C2A7976g00^K[1405P5P0P1C2[[^19^29^<9P8f:#1P?P@P6P5O5b7b?b6O39`;VW=P8O1n200110200021010111100bB%E1,869997eW5X09X49X>3X3:P8CaX3:o"). Qed.

Lemma class_size_table :
  map class_size (zrange 1 30)
  = [32; 64; 96; 128; 160; 192; 224; 256; 288; 320; 352; 384; 416; 448; 480; 512;
     768; 1024; 1536; 2048; 3072; 4096; 6144; 8192; 12288; 16384; 24576; 32768; 49152; 65536].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3g00C6j1<Tg0069j10Tg00<0j14Tg00B6j1;Tg002hj28Tg001mj12Tg00ilj27Tg00k?j46Tg00Nbj39Tg00BVj35Tf0R0#0#0p=1g003BR1f2R2#2f1R3#2=51035p=:f4#2f3#2%22%23=510551551551p=3%<1R0g0058R3#0R2#0R4#0#1R5%05R5%43R6#0R7#1#1R8%05R5%42R2#0#1#1R9%08R8%46R6#0#1#1R:%05R5%44#0#1#1%09%42#0#1#1%08R8%47#0#1#1%0:%46#0R6#1#1%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08R8%05R5%08%05%;13:D3D3D3D3D3D3D3R5'8P1P1g00k[%23%26'7C6=905do"). Qed.

Lemma max_cached_table :
  map max_cached (zrange 1 30) = [16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3g00C6j1;Tg0069j11Tg001mj10Tg00<0j14Tg00B6j1:Tg002hj28Tg00ilj27Tg00k?j46Tg00Nbj35Tg00BVj33Tg003BR0f2R1f1R2f0R353033p=9f4f3A30239301530530p=2%;0R1g0058R3#1R2#1R4#1R5#1#0R6P6P6P6%43R6#1R7#1#0%42#1#0%05R5P5%07R7P7%04R4P4P4P4P4P4%02R2P2P2P2P2P2P2P2P2P2P2P2%:09922D2D2D2D2D2D2D2R2'8P0P0g00m2%03%46#4#1#0'7C6=512do"). Qed.

Lemma chunks_per_map_table :
  map chunks_per_map [1; 2; 3; 6; 7; 8; 16; 19; 21; 23; 24; 30] = [8192; 4096; 2730; 1365; 1170; 1024; 512; 170; 85; 42; 32; 4].
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;1p;2p;4p;3g00C6j19Tg0069j10Tg00<0j11Tg00B6j15Tg002hj28Tg00k?j47Tg00Nbj36Tg001mj13Tg00BVj34Tg003BR0f4#3f3#3f2#3f1#3f054054054034p=2%90R1g0058R2#0R3#0R4#0R5#0R6#0R7#0#0#0#0R8#0R9#0#0R:#0P:%13R:#0#1R;#0R<#1R=#0R>#1#0#1R?#0P?%14R?#0#0#1#0#0#1#0P9P8P>P=P<P7P4%50R4D2D2D2R7'8P0P0g00nIP2P3%12R2%02R3%12R2P5P6%1?P;%1:#1%03#0%12#0P4D2D2D2C7=617do"). Qed.

(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && ((c =? 1) || (class_size (c - 1) <? s)).
Lemma class_id_ok_all : forallb class_ok (zrange 1 65536) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;2p;1p;3g002hj26Tg001mj12Tg00ilj23Tg00odj35Tg00Nbj34Tg0069j11Tf0#1#1p=0g00QjR0g00RJR1'6g003Bg010@g0058R2#2%02#0#0#0#0#0#0#0#2'335=401do"). Qed.

Lemma class_id_ok : forall s, 1 <= s <= 65536 ->
  1 <= class_id s <= 30 /\ s <= class_size (class_id s) /\ (class_id s = 1 \/ class_size (class_id s - 1) < s).
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h01Hh11mh21nh32H4h44__x1h54__x2h61xh74__p1h84__x3h97__arithh:4__ffh;8__varmaph<5__with=2H1h>2H2h?2H3h@4__p2hA4__x4hB2H0hC3HinhD2HshE5lemmahF1shG1yhH2z0p&0p;1p;2p;3p;4p;<p;6p;Bp;7p;8g001mj1LTg0069j1GTg007;j22Tg011UR0j1}Tg00^hR1j1WTg002KR2j2ITg005]R3j24Tg008kR4j23Tg0125j2UTg002hj2BTg012Rj3]Tg00`Zk108Tg00a8k407Tg00g9l<tTg00a[j6pTg0138j2nTg00Nbj3ETg00;6R5j2>Tg013Zj1jTg0148j2hTg00?Yj1MTg00@8j2RTg014Yj3dTg00@aj3VTg00AJj2bTg00B6j1aTg00BVj3`Tg00C6j1_Tg00CVj2NTg00Kkj1^Tg00D4j4JTg00DRj1\Tg00E0j1[Tg00E[j2KTg00Gnj2HTg00F>j4FTg00Fik105Tg00GKk304Tg00HQj2{Tg00I3j2zTg00I_j3vTg00J>j4uTg015Bj4sTg015mj4rTg00ilj2qTg00^4j3XTg00odj3oTg010@R6j1YTg017Bj2mTg017[j3lTg018Lj3kTg018oj11Tg00<Uj28Tg00<0j1QTg00k[j15Tg01:Dj2@Tg01:aj2ATg00:Yj2PTg01;>j3OTg00=mj2iTg01;aj3gTg01<=j2xTg01<]j2yTg00enl<ZTg00fSlBfTg00O<j6~Tg00O`j7eTg00PDk700Tg01==k701Tg00Phj8cTg00=Ok202Tg00=2k203Tf0R7#G#Gp=Cf2R8f1R9'2/37p=9g003BR:g00g^R;P:P:P0f4R0P1f3R<g01=aP8P9P7M<Zp>06P;P:P:P:P1P1f5R1P0P<P8P9P7M<Zp=|P:P:P:P:P:P:P2P7P9P8P2P<P0P1f6R2f7R=f8R>f9R?MBfp=wAE:97p=6P9g00RjR@g00SIRAPAg00SiRBP7E~p=TP9P@PAPAPBP7g00TIFep==P8P@PAPAPBP9P7K00p=<P:P9g00TiP7CFp=DP8P@PAPAPBP9P7K01p=SP<P@PAPAPBP8P9P7Gcp=:g00QjR@g00RJRC7E7p=01897-028p=;20397#5p=71897=E@Cp=?g0058RD#LRE%GDRF#GRG#C#C#C#C#C#C#C#LRH,27797%}HRIPEP912E9RJ%WIRK,IERL,49RM'3g00QLRN/UHRO,IERP,49RQ,3JPJPMPJPQp-0RQ/BJ9]JJP:P:P3P7X6:RMP31497R3$08XG:X6:P9P91B:9PLPPPMPMPMP:P:g00ha1I97H07,B:X1:X2:PEPE1B:EPKPOPMPM%W7,B:X6;PIPOPM1UN7X6:PHPH1B:HI06E|M:wM<tEp1nNH14NHRM16OH'312HNRIAE:ON'3'>POP:g00XRRO%jD,h:g00Y>R;#MRK#M#M,R:5d:1R:K1R:;5V:5V:g00Y]'b%aOR;3`%_OROP:1N:8RKP9%^:RPCJ%\:RL%[:RR1TR0P:1K:FRFg00iERS1H:HRTCF,=R5<R1H:N,DT,=R1TR1RU5<R5SR&05ARAPR1H:ERV1K:DRW'D,=RRX1DWT,=R5<RPAP:PWg00ZIRTB04:VFCF,=R9<RXC:C:1{RBRBP7P81B@C1z78#0dAv:N9CuRCb:b;b<X4:X5:X7QX@Q169H,3813I<'>129H,3J1IE<,4899E8[[^4:^5:^7Q^@QP7AE:9NPMP9P0P8P<O6b9bHbBCsCr1qEHRH9X:9RMePMg01>NAo:6H#0RMAX:7H%Y9#0[^6:RN,mMAlMN7WEAk:6HP7O2PNP7P0P8O2%Y0#0%11RN,8E%QDRD#Q#Q#G#LRH7;N%5N7;1R61@NE17NE/A1'PRN;O7%06%0N'3P4%12RN,8E?;NH%5N7;2#01@NE17NE/A2'P#0%1=RN12NH59E%5N16NE17NE/4='>59='3P7%1>RN,8E?;NH%5N7;>#0%1?RN/@E17NE/A?'P#0f:R?#1RN,8E?;NHR6%5N,8?RN;O9%06%0N'3P4f;RN#1R6,8E?;6H#0%56,?Nf<RN#1R6126H59E%56166E176E/4N'>59N'3P7f=#1RN,8E?;NH#0f>RN%1N#5'?f?#1RN,8ER618NHRN;O9%06%0N'3P4f@RN#1R6,?E1?6HfAR6#1RM12MH59E%5M16ME17ME/46'>596'3P7fB#1,?EfC#1/?HP41?971289[R612971?89RM[12<8\M1i97P9n2001000000120000000X1:X2:RMP6^1:^2:R6P7PEfE#1RJP8O312EJPMP6P7fG#1RJPHP<O312JHPMP6P7fIR6%16#5RMP?O3126MfJRM#1R6/@ERJ176E/AMRM;gN%0J%0M'>P5fKR5#1RM/@E#017ME/A5#0fLR5#1RM12MH59E%5M16ME17MERJ/45'>595'3P71@ME#0P41@97#01689[RM16971@89#0RN[16<8\N1x97P9n2001000000120000000X1:X2:PM^1:^2:P7fNRM#1RNPEP9O316NEP;POP:PKP91N:<RKCJPLPRP:PWPSPVCF,=RRVPAPR1K:D,DF,=RRDPAPR1H:H,DW,=RRWPAPRPXPAA<RXWRSASRVU9<RD5<RC:C:C:C:PBPCb:b;b<X4:X5:X8:X7Q167E128<RU128HR612E<RI120H99E0RH1212R@160ERY/>='3'3[[[[^4:^5:^8:^7QP7fPRQ#1RZ/7ER[/4Q%5ZR\PQPZP9P2P>P?O8b9b3b0W3P7O11AJ5#0P41A97#01489[R41A89#0RJ\314<8\J1y97P9n2001000000120000000X1:X2:P4^1:^2:P717NERNPMP9O314NMP;POP:P:1N:0P8PPCJP9PKCJPLPRP:1K:GPTPFCF,=RRFPAPRPDPAPRPWPAPRPXPAASRVF9<RD9<RSC:C:C:C:PBPCb:b;b<X4:X5:X8:XA:14<914=1,>Y,3@,3H\I\6\U[^4:^5:^8:^A:P7P[P\PQPZP9P2P>P?O8b9b3b0W3P7O1n200100000021100011000b3b?b0b>b0b=b0W>W=P9P7O2n2001000000121000000b0W?W0P9P7O2n2001000000121000000b0W3W0P9P7O2n2001000000121000000b0b0b0b0bCWDXF:o"). Qed.

(* [comment removed for export] *)
Lemma examples :
  from_primary 65536 false = false /\ sec_map_size (needed 65536 false) = 73728
  /\ class_id (needed 3 false) = 1 /\ class_id (needed 64 false) = 3 /\ class_id (needed 144 true) = 7
  /\ class_id (needed 100 false) = 6 /\ class_id (needed 1000 false) = 19 /\ class_id (needed 4999 false) = 23
  /\ class_id 8192 = 24 /\ needed 65536 false = 69632.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "p;3p;1p;2p;4g00Nbj3;Tg0069j10Tg00<0j11Tg001mj12Tg008kj23Tg002hj2<Tg01?jj2@Tg01ACj1CTg018oj18Tg01B\j2?Tg00Mmj4=Tf0R0#0#0#0#0p=5g003BR1f1R2;;0p=41<10p=>f3R3f2R41<12P0C=p=7f6f5f4P3P4P2P0C=C=p=A%00#0p=:g01CoR3,?0p=9A;142/30p=61320,34p=Bg00QjR4?;33g0058R2#0R0#0R1#1R5#5R6#0#5#5#2R7/47R8%22R9/49R:%12R2#2R;/4;R<%12R=#2R>/4>R?%02R2#2R@/4@RA%15R5#2RB/4BRC%10#1#1#2R0/40RD%02R2#0#2RE/4ERF%01R1#1#5#5#5#2RG/4GRH'3RI'3RJ'3RK'3RL'3RM'3RN'3RO'31<43P8PO%>7P:PNP9P<PMP;P?PLP>PAPKP@PCPJPBPDPIP0PFPHPE%>GC7C7C7C7C7C7C7FA%01#:R1#0#:#5RH#0#:#2RF/@3=;43%9FRF#C/47%9;#8%21#9#8%26g00RJ'?#8%12#:#2#9#8%1=#1#0#1#0#:#2#9#8%15#5#1#1#1#2#9#8%2H#814FG76E76076B76@76>76;7693Bdo"). Qed.

(* [comment removed for export] *)
Lemma round_up_8_spec : forall x, 0 <= x -> x <= round_up x 8 < x + 8 /\ round_up x 8 mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_As0Tables ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71Hh82H0h92Hxh:1xp;2p;1p;4p;6p;3p;7p;8g007;j21Tg0069j1ATg001mj1DTg002Kj24Tg00=2j28Tg00B6j1ZTg00C6j1VTg00Kkj1RTg00DRj1QTg00E0j1NTg00Gnj2BTg00F>j46Tg00dij6dTg00HQj2bTg002hj2`Tg00I3j2YTg00Nbj39Tg00I_j3WTg00J>j4UTg01DOj3TTg01E0j2?Tg00]Wj2:Tg01EMj25Tg005]j23Tg01Emj3PTg008kj22Tg00?Yj1=Tg00@8j27Tg00@aj3;Tg00AJj2CTg013Zj1MTg0148j2LTg014Yj3OTg00BVj3HTg00CVj2ETg00D4j4KTg00<0j1STg00E[j2@Tg00Fij1cTg00GKj3GTg00MJj3aTg01FTj3ITg01G7j3_Tg00Mmj4[Tg01GXj2\Tg00O`j7]Tg00PDj7^Tg00Phj8XTf1R0g00RjR1g00SIR2P2g00SiR3f0R4g00TIF]p=0g003BR5g00QLR6794p=<P5P0g00ZIP4C6p=>f2R7P1P2P2P3P0P4F^p=Jf3R8P1P2P2P3P7P0P4GXp=F1164g0058R9#AR:#A#A#DR;,40R<%D9R='8R>g00XRR?#ZR@%V?RA%R5RB%Q5RC%N5RDP1P2P2P3P51B5;R1g00iERE1B56RFC6,0DEd1bD3R3P4P7g00QjRGg00RJRH'`1Y47=9GHdAW560CURHb1b2b3%<;g00^K[P4b0RG7T;1?>;,:;15>;'4995>147;RI/8=RJP@PAPBPC1>F1,0DP3PHb1b2b3136;P4b07P;15J;RJ,1613J;'2148;RJ/8=/?;RB/:;RK,1813KJ'215K;#<g00Y>RK#=RJ#=RL,75175JRJ175KRK5;55;5g00Y]RM'C%=L,75%M9,L5=O5J=;5K5;5/CM=H?@5H?PAP51E57P01E58CKPCPDP5PFg00TiRF%S9,@5RCC6,0D1>C1,0D5JD%c2R2PDP51@59R9=G51RA1B5=5a5PE1@5:R:9I51=G5CC6,0DP2P5P9PFAI5:1R:C6,0D1>:A,0D5JDCFCFP3PHb1b2b3X45X55X651167137;'21:;7/48995>1:8;R8,17138I'2[[^45^55^65P4f4R4/4;/8=R=/5;1?=;P4P0P7O5b0A_B;GC[b8b71\0;RB,1013B<'215B;#<'2eW9X:5o"). Qed.

End AsanTab.
