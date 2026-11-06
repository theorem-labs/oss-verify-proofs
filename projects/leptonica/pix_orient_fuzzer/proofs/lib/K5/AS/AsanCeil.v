(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PlacementSearch.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanCeil () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K52AS?PlacementSearch<higher_fit_bC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib2K52AS?PlacementSearch=no_higher_fitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC46Stdlib4Bool4Bool=negb_true_iffC69OSSVerify5KrLib2K52AS?PlacementSearchAno_higher_fit_iffC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS8AsanCeil>placement_ok_bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS8AsanCeil<placement_okC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec69OSSVerify5KrLib2K52AS8AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_ind_rC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0c69OSSVerify5KrLib2K52AS8AsanCeilGplacement_ok_b_of_floorC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS8AsanCeilChint_placement_ok_bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203c69OSSVerify5KrLib2K52AS8AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS8AsanCeilJalloc_ceiling_le_alloc_topC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7Z_to_bvC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib4Init5Logic9False_indC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib2K52AS?PlacementSearchBpage_round_up_Z_geC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef6repeatC47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succ".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;1p;2g0000j10Tg000Uj16Tg0013j25Tg001Mj11Tf0R0#1#1p=7%10#1#1#1p=2%00#0p=4%00#0#0#0p=3g0022g002P#7#2#2#2#0#2#2#0#4#3#3#3#3#3#6'5o"). Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;1p;2g001Mj13Tg000Uj14Tg0013j25Tg0000j12Tf0R0#2#3#2#3p=0%20#2p=1g0022g002P#0#0#0#0#0#0#0#0#3#1#1#1#1#1#1#4'5o"). Qed.

(* [comment removed for export] *)
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
  bottomup_floor <= aZ
  \/ no_higher_fit (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h)).

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
  (bottomup_floor <=? aZ)%Z
  || negb (higher_fit_b (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h))).

Lemma placement_ok_b_iff : forall h aZ nZ,
  0 <= aZ -> 0 < nZ -> aZ mod page_size = 0 -> nZ mod page_size = 0 ->
  placement_ok_b h aZ nZ = true <-> placement_ok h aZ nZ.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h05lemmah11Bh21Hh34HaAlh45HaPosh52Hbh65Hbaseh74HnAlh85HnPosh92_Hh:2aZh;1hh<2nZp;2p;3p;1p;4p;6p;9p;;p-1R0g0035R1p4p710p9P0g003aR2p4p710p9P0p1004OR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0g004mR0p4p710p9g005gj23Tg006Cj27Tg006_j2PTg007?j39Tg0000j16Tg007Yj1VTg0087j12Tg0092j2OTg009ej21Tg00:Oj1HTg00;8R3j2GTg00;Sj2?Tg00<0j1DTg00<Sj2WTg00=3j1ATg00=mj1@Tg00>cj3<Tg00?@j4=Tg00@Gj1>Tg00@ej2;Tg00ABj4:Tg00BJR4j24Tg00BdR5j25TP1j2NTg00C=j2LTg00C]j3KTg00DSj4BTg00EFR1j6ITg00F7j2JTg00FWj4FTg00G>j1MTg00G_l9ETP2j4QTg00Hkj3RTg00Imj3STP0l9TTg00Jml;UTg00KhR0f0R2g00LH39p=0p-0R6P5g00Lhf5R7f4R8f3R9f2R:f1R;P2M9Tp=8P6f6R<P5P7P4P1P8P9P:P;P2M;Up=Cg00MYg0022R:g00NPR1/3;171;g00Nn,P9=9:1R9g002P#6#6#6#6#6#6#VR4%2<R='O114=R=,31%H4R>,7='GP3f7R3#2,14R=,3117=>g00OfR=/?3%D4R?/W?R?f8R@#A%@@3<RAP3P<%2@,14RBC=#>';#013=3PAP3P<PBC:'4'5P2f9RB#2,14,31f:R1#2,14/7>P2f;R>#2,14g00Ph'7RAePA1?=>RAf<RC#A%@C5<?RDP>P1%2C,14REC=RF#>RG';#0%0ARH%0GRI'4'51?=CRJf=RK#A%@K5<?R?PCP>%2K,14R4C=RK#>RL';#0%0JRJ%0LRL'4RMP213=CRNP?PCP>P4C:R4'4RCPC1N6CR?E8W01LAG13=>RG,5HPM14NLRMPJPNP2PLPLP6P5g00QaRJ9K65RHPLCBEIPCPCP?E8W01J=>g00RQR=990FRA,5IPMA90K=R=,4NRKP6^16R0P6P6P5P5CFRMPNP6P5PHPNCBRHPLP=P2FCPCPCP?E8W0%MFPDP>P1PEC:RF,5APKPCP0PMPNPHP=P4P2FCPCPCP?E8W0PDP>P1PEPBP@P3P<P2M9EP6P5PJ14GFCQO2O2O2O2b5W6W9P;P2O2n2001000000121000000b2AR<78#0AS<78'5eX79W3W8W4X<:W:W;o"). Qed.

Lemma placement_ok_b_of_floor : forall h aZ nZ,
  bottomup_floor <= aZ -> placement_ok_b h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh12aZh21bh31hh42nZp;2p;1p;3p;4p;6g005gj22Tg0000j10Tg007Yj1;Tg00<0j14Tg00<Sj2DTg00=3j1BTg00=mj1<Tg00>cj3:Tg0087j15Tg009ej26Tg00?@j47Tg00@Gj18Tg00@ej29Tg0013j2CTg00;Sj23Tg00F7j2ATg00S1j4=Tg00SLj6>Tg00Hkj3?Tg007?j3@Tg00KhR0f0R1g00LHR23@p=1g00MYg0022R3g00OfR4f1R5'2P0P2g002P#0#0#0#0#0#0#;R6#4R7/D7f4R7#B%<73:f3R8f2R9%57,66C7#8,91#1X201C021349R2%121248[12491348#1[1A49P1C=E>A?895#1eW0X43W1W3o"). Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_of_floor : forall addr h aZ nZ,
  bottomup_floor <= aZ -> hint_placement_ok_b addr h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h01Hh12aZh24addrh31bi001bh41hh52nZp;1p;2p;3p;4g0000j10Tg007Yj19Tg00<0j13Tg005gj22Tg00Sjj18Tg00Hkj37Tg007?j31Tg00Tdj44Tg0013j25Tg00Uoj46Tg002P#0#0#0#0#0#0#9#3g00MYg0022R0g00Off1R1'2f4R2#8g00KhR3P3P3P3f0R4f5f3R5772g00LHR6n0100000020000=136P4P2P5f2R4P1C41536n0110000020000b3P2P5P4P1C6=136eW0X50W1W4W2o"). Qed.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh12aZh24addrh31bh41hh52nZp;1p;3p;2p;6p;4g0000j10Tg007Yj18Tg00<0j13Tg00Sjj12Tg007?j31Tg00Hkj37Tg0013j26Tg00SLj64Tg00Uoj45Tg002P#0#0#0#0#0#0#8#3g00MYg0022R0g00KhR1f3R2#2g00RQR331P1P3P1P1f0R3f4R4f2R5772g00LHR6n0100000020000=116X311616%24P3E4P4P2P5f1C5=116eW0X50W1W4W2o"). Qed.

(* [comment removed for export] *)
Definition placement_policy : Prop :=
  forall (h : VmMaps) (a : word) (nZ : Z),
    0 < nZ -> nZ mod page_size = 0 ->
    bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
    bv_unsigned a + nZ <= alloc_top h ->
    region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
    bv_unsigned a + nZ <= alloc_ceiling /\ placement_ok_b h (bv_unsigned a) nZ = true.

(* [comment removed for export] *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__with61hp;1p;2p;4p;3p;8p;7g00W6j1STg00X4j1RTg00XTj1CTg00Y4j2?Tg00YRj1QTg00Z0j1LTg001Mj11Tg0000j10Tg000Uj15Tg00Z[j26Tg00[>j2PTg00[aj4<Tg00\Lj1KTg00\nj3:Tg00]Qj3ITg00^4j8HTg00^Xj2BTg0013j2DTg00_:j2ETg007?j3ATg00_fj3FTg00`Ej4GTg005gj27Tg00a7j2;Tg00aTj2@Tg007Yj1>Tg00b1j1MTg009ej2NTg00bjj1=Tg00cbj7OTf0R0#1#1p=J%10#1#1#1p=2%00#0p=4%00#0#0#0p=8%00#0#0#0#0#0#0#0p=3f1R1g00dFR2g00deR3P3g00eER4P0g00eeFOp=9g00MY%S0g0022R5g00fER6#R%C61?51%Q5%L5R6P2P3P3P4P5g002PR2#J#2#2#2R7#1#0#4#8#3#3#3#5R8,65g00g1R91P52R:C<,96%K3P5%07#2#2#0#4#8#3#3#5R7,65P9%02#4R2#5R9,65%02#4R2#8#5R3,65R;5:5=:5;9I5:C<,96GH1B64P0f2R6g00KhR4g00LHR:'D1E06=A4:dg00NP=F51CGb3b4b5W017801;93/;3,@1,77[^05P0%>2%M6'NP1O2b2g00gX%=1'7eW1W6o"). Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h14__x2h24__x3h31Hh42H0h52Hzh67__arithh74__ffh88__varmaph95__with:1hh;1zp;1p;2p;3p;4p;7p;8g00W6j1NTg005gj20Tg00hYj2?Tg00bjj15Tg00igj19Tg00jFj23Tg00joj38Tg00kXj2>Tg00X4j1=Tg00lDj3<Tg00XTj1;Tg00Y4j27Tg00ldj4:Tg00YRj1MTg00Z0j1LTg001Mj1KTg00[>j24Tg0000j1ATg00\Lj1@Tg00^Xj2BTg0013j2CTg00_:j2DTg007?j3ETg00_fj3FTg00`Ej4GTg00[aj4HTg00cbj7ITg00^4j8JTg0022R0f1R1g00g1f0R2CHp=1P1g00dFR3g00deR4P4g00eER5P2g00eeFIp=2f3R6P3P4P4P5f2R3P1P2GJp=6g00MY%N1g00gXR7,011?61%56,07g00fER8g00mBR9#9R:#9,30130:1309580580g00ma'>%=83<%;8P01703P11706C:%M0%L0R8g002PR9#K,40R:%A9,40R;'1,28%@4R4P81409R9/1:,28P4119;,28C6C61B85P2P3g00KhR8g00LHR5'C1D23=E85dg00NP=F01CGb7b8b9X00X10X20103110161036[[^00^10^20P2P7f5#5f4P1P3O5b6b4W5W3X;0W:o"). Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh13Hloh22_Hh33_H0h44brk0h53inph63limh75mbaseh88reservedh92spp;1p;2p;6p;3g0000j12Tg007Yj1@Tg00<0j1;Tg00<Sj29Tg00XTj1?Tg00nMj1<Tg009ej20Tg005gj21Tg000Uj1:Tg006_j24Tg00;8R0j28Tg00oBj65Tg010;j17Tg00W6j16Tg00b1j1>Tg007?j3=Tg0022R1f0R2g00NP3=p=3g002P#2#2#2#2R3#2#2#@R4#;R5/95#?g0112f2R6#<P0g011lR7f3R8,04R9'1g012gR:,19%:3R3,49#3'8f7R9f6R;f5R<f4P8P6E5#7#6P2104<,17104;R6/1:1463#3'8P01049R0/1:1403#3f;R0f:R6f9R8f8P9P;E5#7#6P21048/1:1046/43#3P<f>f=f<P0P6P8E5#7R8#>,04,17e%68eW3W2f1R8P2O2n2001000000120000000W0W1P8P2O2n2001000000120000000W0W5X61X95X75X45W8o"). Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Eh11Hh21bh31hh42h'p;1p;3p;2p;6g0000j10Tg007Yj18Tg00<0j12Tg00b1j11Tg007?j37Tg00W6j16Tg009ej23Tg005gj24Tg00SLj65Tg00MYR0g002P#0#0#0#0#0#0#8R1#2R2f0R3#1f1R4#137f2R5#6R6P2f3#1g011l1313'4X22P3%15P4E5P6eW1W0X40W3o"). Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01bh11hh21lh31mh42mbh52nah61rh72sbp;1p;2p;8g0000j10Tg007Yj19Tg00<0j14Tg00<Sj23Tg00XTj18Tg00W6j12Tg00b1j11Tg013bj85Tg009ej26Tg005gj27Tg00MYg002P#0#0#0#0#0#0#9R0#4R1/31#8R2g0022f7R3#2f0g011lP3f6f5f4f3f2f1f8#1G5R3#1,60'7e%23eUX41W2X01X71X52X32W6W1o"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h52H1h62H2h72H3h82H4h94__p1h:6__sat0h;6__sat1h<4__x1h=4__x2h>4__x3h?1qh@1rhA1HhB2H5hC2H6hD2HrhE1zp;1p;2p;4p;6p;3p;7p;8g0000j1>Tg000Uj1ITg00X4j1jTg00XTj1\Tg014Yj1XTg00YRj1UTg00Z0j1TTg00Z[j2@Tg00[aj49Tg0157j6RTg00^Xj2iTg0013j2gTg00_:j2`Tg007?j3BTg00_fj3ZTg00`Ej4YTg015[j3Vj2KTg016<j24Tg00a7j25Tg006_j22Tg016Yj2:Tg0176j2GTg017gj2FTg018Xj1STg0191j2Ej3QTg006Cj23Tg00;8R0j28Tg019Xj2DTg005gj27Tg01:?j2HTg01:ej2JTg00igj1NTg00jFj2CTg00joj3PTg00kXj2hTg00lDj3fTg00Y4j2OTg00ldj4eTg00\Lj1_Tg01;Kj6^Tg001Mj1]Tg00[>j2?Tg01;oj7[Tg01<Sj3LTg00]Qj3aTg00\nj3MTg01=6j1bTg00aTj2cTg00cbj7dTg00^4j8WTf0R1#>#>p=;f2R2f1R3':/c1p=1P3g00dFR4g00deR5P5g00eER6P1g00eeFdp=<g0022R7g00NPR87B1p=AAB731p=61781p=0f3R9P4P5P5P6P2P3P1GWp==g002PR:#>R;#>#;#;#;#;#;#IR<%I:R=511R>g00fER?#jR@%\?RA%X7RB%U7RC%T7RDP4P5P5P6P71@7<REg01>4RF1@78RGC9,<DERRH1iD6RIP1P2g00KhRJg00LHRK'g1`12=BJKdAZ783CYRKb1b2b3%A<RJg01>[[RLP1b07V<14><,5<12><':,6>A13<=R>1G><%0>%0<RMA19<=RN/2<#0[[A12<=RO/F<%0ORPf4RQ?1<=RR/4<RS#0\M[1KN<%SJRT15<S12R<RS':,6R[1ER<138<RUf5RV?1<=RW/2<RX#013X<'8[1DW<13<8RYf6RZ?1<=R[/2<R\,3<17\8'8[1H[<f7?1<=R]/4<#A\J1J]<f8?1<=R^/2</6^\J14^<R_P7f9R`?1<=Ra/2<RbP7P@PAPBPCP7PGg01?8RGPEC9,<DRBPIPKb1b2b3PUP1b0b@b?b8b7b6b5b4b:b;7Q<12><R>#013><'81GO<%0S\M\P1FN<%0N14W<RN#0\M[1KR<15<N/:X,6W\T1EW<%0\13\<'8\U1D[<12]<R[,3<17[8'8\Y1H]<%A_\J1J^<16ba\J14a<P7f:Ra?1<=/2<P7P0%01131<f<152<'7P`%02139<R`p-0R0g00mBRJ#NRb#N,C71C7b1C7J5P75P7g00ma'h=f?@PAP71O72P31O79CePCPDPDPB%_5RBPDP4P5P5P6PDP4P5P5P6PVE^P7%]:,?7R6PGPEC9,<DF[C=PBPDPDPHPBP71?7:R:=L7E1@7=5a7PF1?7;R;9M7E=L76C9,<DC=PBP7P:g00g1AM7;EC9,<DC=C=PIPKb1b2b3X<7X=7X>7W918Q`\U15<9/:Q,6O\L159<,72[[^<7^=7^>7^90P1%0VPVPZf@Paf;O6b0WCWBP3P1O2n2001000000121000000b@b?b8b7b6b5b4b:b;bDbA%b1,71eXE7o"). Qed.

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;2p;1p;3g0013j25Tg0000j10Tg007Yj12Tg01?_j21Tg01@Ej14Tg007?j33Tg00KhR0g00LHR1'5g002P#0#0#0#0#0#0#2g00NP'1#4=301do"). Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h02HDh12HLh21bi001bh31Hh41eh51xh61yh71zh82H0h92Hbh:2Hch;1ch<5flagsp;1p;3p;2p;6g0000j16Tg007Yj1KTg00<0j1DTg01ALj1ATg007?j33Tg001Mj1JTg000Uj1FTg01BPj20Tg00@Gj19Tg00G>j1@Tg009ej22Tg01C1j2=Tg01COj2<Tg018Xj1>Tg01Clj2ITg01DMj3HTg01E0j21Tg01ENj65Tg01Ejj1ETg01FJj3CTg01Fnj2?Tg01GMj2BTg01Glj1GTg00KhR0f0R1g00LHR233p=8g00RQR39301p=7f1R4=301p=4A3031p=:A3021p=;g002P#6R5#6#6#6#6#6#KR6#Dg0022R7%A4=371%J5#FR5,04#8g00;8R8%91#8%74R9[%71%94#8[R:f2R;#9#8\9%@1P1n2001000000120000000X20P:^20P1f4R:,26g01HlR9'=g00NPR<'<P81<41#7A37;4#>R8[A3741#>1<;4#7[R=f3R>/<;#7\81I41P1n2001000000120000000X67X57P=^67^57P1f5,26/=9R=P<A37=<R=f6,26R8?H951=89/0510851095R8'1'4P7f7,26R;/=91015R9f8R?,26/05/18R@'4X77P1P<P4E510<5R<10;5/18'4P0P<f9R<,26R;/05RA/18,41X20P1P3%E5E5%:@g01IkR@=C;51?;@/0510@5#9R;,1A'4P7f:RA,26R8/?@f;,26/05/1;R@,49X77P1P<P?E510<51085/1;'4P010A5f<,26/05R5/1;,41X20P1P2P?E5%;@P5P0P01112#:%93R5,14#;g01>[R@]0]1P11122R?#:1125#;P0P3P0p-0R;P1P@g01JmR6n0110000020000X40g01KIRAP?P4E5P@1B@1R?b3W0W11132#:1135R5#;P0P2P0P;P1P6P@n0110000020000X40PAP5P1E5P@P?b3W0W1n0110000020000P:P4O2b2b0b0b0b1b1b1W8%>=eO3b3O2b3%G>#8eW9W:W;W<o"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01zp;2p;1p;3g016Yj27Tg000Uj16Tg00aTj20Tg016<j21Tg01Kej25Tg01=6j12Tg006_j23Tg007?j34Tg0022R0f0R1g00NnR2'7g002P#6'0/12/52%21/32g00NP540eW0o"). Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h14__x2h21Hh32Hzh47__arithh54__ffh68__varmaph75__with81zp;2p;1p;3p;4p;7p;8g006Cj25Tg01LEj1NTg01=6j16Tg005gj23Tg00igj19Tg00jFj20Tg00joj34Tg00kXj2@Tg00X4j1>Tg00lDj3=Tg00XTj1<Tg00Y4j2;Tg014Yj1:Tg00ldj4MTg00YRj1LTg00Z0j1KTg0000j1CTg00[>j27Tg00[aj42Tg00\Lj1ATg00Z[j2BTg00^Xj2?Tg0013j2DTg00_:j2ETg007?j3FTg00_fj3GTg00`Ej4HTg00cbj7ITg00^4j8JTf1R0g00dFR1g00deR2P2g00eER3f0R4g00eeFIp=1f3R5P1P2P2P3f2R1P0P4GJp=8g0022R6g00NPR7/54%N0%60,30g00fER8g00mBR9#9R:#9,06106:1069546546g00ma'@%>83=%<8P61;61P0%:6CM%L6%K6R8P6g002PR9#C,76R:g00g11769R9C2,18%A2R2P8P61B67R;g01?8R<P:C2,18P2P6P;P<P9C2,18C8C81?83P4P1g00KhR8g00LHR3'D1E41=F83dAG670CHb5b6b7X06X1613041571R7P7[[^06^16P4P5%65P0P1O4b4b2W3W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;1p;2p;3g0000j12Tg007Yj16Tg00<0j1;Tg00XTj17Tg01MRj2?Tg01NEj3=Tg00X4j1<Tg0013j2:Tg01?_j23Tg01Nhj18Tg01Olj39Tg007?j3>Tg00lDj34Tg00igj15Tf4f3f2f1f0R03434p=0%50#5p=1g002P#2#2#2R0#6R1#;R2#7R3P2g00NPR41?145=1R5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5%<2D0D0D0D0D0D0D0D0':%20#2#2#2#6/34#81314g00mB#1#1#1#1#1#1#1#15925>3do"). Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h02Hih14__x1h21ih31dh41lh53Hi0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4cstrh=1xh>2IHh?5cstr0i001np;1p;2p;3p;4p;6p;5p;<p;7p;8g0000j1ATg007Yj1_Tg00<0j1VTg00XTj1BTg01PKj21Tg01PkR0j22Tg00igR1j13Tg01QCj39Tg01Qaj38Tg01R@j4:Tg00X4j1CTg00lDj30Tg007?j35Tg01R\R2j14Tg006CR3j27Tg0013j26Tg01S<j4JTg01Scj1@Tg005gj2;Tg00Y4j2ITg00YRj1WTg00Z0j1UTg00Z[j2HTg00[>j2GTg00[aj4DTg00\Lj1TTg01;Kj6STg00^Xj2QTg00_:j2PTg00_fj3OTg00`Ej4NTg000Uj1RTg016Yj2<Tg014Yj1MTg00ldj4^Tg01<Sj3LTg01THj4]Tg01U3j5\Tg01UUl<KTg00cbj7[Tg00^4j8YTg01V:l<ZTg01V_R4g0022R5P0P2P3g01W>R6f3R7f2R8f1R9g00mBR:g00NPR;f0R<M<Kp=XP9g00dFR=g00deR>P>g00eER?P<g00eeF[p==P5P9g01?8P<CDp=?P7P=P>P>P?P8P9P<GYp=>P4P5P0P2P3P6f5R6f4R3P7P8P9P<M<Kp=FP4P4P5P5P1P2P2P7g01W`P8P9P<M<Zp=Eg002PR2#AR1#A#A#_#VR0#BR@P01108,29%3:RAA9087580P0P8P7P9C:%C0RB50055@[^30^24RCX4@110B,29128:%48RD/7;REP8PD165D165;CXP<CJPE%@7%47,;;p-0REg00fERF#CRG%BFRF1I59%W5RH%U5RIP51H5;RJg00g11G52RKCD,=I%T>RLPI1?KJ,=IPLPIP=P>P>P?P7ESC>C>1QI?R?P<P8g00KhR>g00LHR='61P<8=5>=dAO5;9CNR=b7b9b:X15W81;;<179;P7[[^15^8EP<A906B980AP0P6PBP3C:=00B55@%46REP9P8O4b6b<b5W0X30X24A0037,10,29P41106#3,2<f7R>f6RJ500RM9909980AP0P9PMP7C:=00B55@]0P81103#3,2:A00JB,6@A00J6R6990:980AP0P:P6P8C:=00B55@eW0%3<110J#3'2PJP9P3110>RJ,29%49R6%4JR:'7P9P61656RMPJP:165:RNEF%39RO%3JRP'2%R2R2,<61<:2'7RQPO1<<2RRX=5RSP6O1PSP9P6PMCEPPPSP:O1PSPJP:PNCEEFP<CJPQ%@81;;Df9,10RD#@%4D,;;PGPFP51I58P9%M5C^PHPI1H52RH9L5K1G51R1=L5H'?,=IPL1?K1,=IC>P?P=b7b9b:X15X;51<92,7R1798[^15^;5P<f;,10#4PEP7O3b6b?b<b5C]O3f8=00>R>990O980AP0POP>P3C:=00B55@eW0X24P<O1n0110000020011100P<O1W0X30X24X>CX4@X=0P<D\W4o"). Qed.
