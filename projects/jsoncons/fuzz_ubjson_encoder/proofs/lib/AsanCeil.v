(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PlacementSearch.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanCeil () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?PlacementSearch<higher_fit_bC13~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3orbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?PlacementSearch=no_higher_fitC13~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC46Stdlib4Bool4Bool=negb_true_iffC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?PlacementSearchAno_higher_fit_iffC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil>placement_ok_bC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil<placement_okC13~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil>bottomup_floorC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_ind_rC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeilGplacement_ok_b_of_floorC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeilChint_placement_ok_bC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil:init_sp_okC13~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil=alloc_ceilingC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeilJalloc_ceiling_le_alloc_topC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7Z_to_bvC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib4Init5Logic9False_indC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C46Stdlib6ZArith4Zdiv:Z_mod_multC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?PlacementSearchBpage_round_up_Z_geC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef6repeatC47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succ".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h05lemmah11Bh21Hh34HaAlh45HaPosh52Hbh65Hbaseh74HnAlh85HnPosh92_Hh:2aZh;1hh<2nZp;2p;3p;1p;4p;6p;9p;;p-1R0g0035R1p4p710p9P0g003aR2p4p710p9P0p1004OR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0g004mR0p4p710p9g005gj23Tg006Cj27Tg006_j2PTg007?j39Tg0000j16Tg007Yj1VTg0087j12Tg0092j2OTg009ej21Tg00:Oj1HTg00;8R3j2GTg00;Sj2?Tg00<0j1DTg00<Sj2WTg00=3j1ATg00=mj1@Tg00>cj3<Tg00?@j4=Tg00@Wj1>Tg00A5j2;Tg00ARj4:Tg00BjR4j24Tg00CDR5j25TP1j2NTg00C]j2LTg00D=j3KTg00E3j4BTg00EfR1j6ITg00FWj2JTg00G7j4FTg00G^j1MTg00H?l9ETP2j4QTg00I[j3RTg00Jmj3STP0l9TTg00L=l;UTg00M8R0f0R2g00MX39p=0p-0R6P5g00N8f5R7f4R8f3R9f2R:f1R;P2M9Tp=8P6f6R<P5P7P4P1P8P9P:P;P2M;Up=Cg00Nig0022R:g00O`R1/3;171;g00P>,P9=9:1R9g002P#6#6#6#6#6#6#VR4%2<R='O114=R=,31%H4R>,7='GP3f7R3#2,14R=,3117=>g00Q6R=/?3%D4R?/W?R?f8R@#A%@@3<RAP3P<%2@,14RBC=#>';#013=3PAP3P<PBC:'4'5P2f9RB#2,14,31f:R1#2,14/7>P2f;R>#2,14g00RH'7RAePA1?=>RAf<RC#A%@C5<?RDP>P1%2C,14REC=RF#>RG';#0%0ARH%0GRI'4'51?=CRJf=RK#A%@K5<?R?PCP>%2K,14R4C=RK#>RL';#0%0JRJ%0LRL'4RMP213=CRNP?PCP>P4C:R4'4RCPC1N6CR?E8W01LAG13=>RG,5HPM14NLRMPJPNP2PLPLP6P5g00SARJ9K65RHPLCBEIPCPCP?E8W01J=>g00T1R=990FRA,5IPMA90K=R=,4NRKP6^16R0P6P6P5P5CFRMPNP6P5PHPNCBRHPLP=P2FCPCPCP?E8W0%MFPDP>P1PEC:RF,5APKPCP0PMPNPHP=P4P2FCPCPCP?E8W0PDP>P1PEPBP@P3P<P2M9EP6P5PJ14GFCQO2O2O2O2b5W6W9P;P2O2n2001000000121000000b2AR<78#0AS<78'5eX79W3W8W4X<:W:W;o"). Qed.

Lemma placement_ok_b_of_floor : forall h aZ nZ,
  bottomup_floor <= aZ -> placement_ok_b h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh12aZh21bh31hh42nZp;2p;1p;3p;4p;6g005gj22Tg0000j10Tg007Yj1;Tg00<0j14Tg00<Sj2DTg00=3j1BTg00=mj1<Tg00>cj3:Tg0087j15Tg009ej26Tg00?@j47Tg00@Wj18Tg00A5j29Tg0013j2CTg00;Sj23Tg00FWj2ATg00TQj4=Tg00Tlj6>Tg00I[j3?Tg007?j3@Tg00M8R0f0R1g00MXR23@p=1g00Nig0022R3g00Q6R4f1R5'2P0P2g002P#0#0#0#0#0#0#;R6#4R7/D7f4R7#B%<73:f3R8f2R9%57,66C7#8,91#1X201C021349R2%121248[12491348#1[1A49P1C=E>A?895#1eW0X43W1W3o"). Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_of_floor : forall addr h aZ nZ,
  bottomup_floor <= aZ -> hint_placement_ok_b addr h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h01Hh12aZh24addrh31bi001bh41hh52nZp;1p;2p;3p;4g0000j10Tg007Yj19Tg00<0j13Tg005gj22Tg00UJj18Tg00I[j37Tg007?j31Tg00VDj44Tg0013j25Tg00W_j46Tg002P#0#0#0#0#0#0#9#3g00Nig0022R0g00Q6f1R1'2f4R2#8g00M8R3P3P3P3f0R4f5f3R5772g00MXR6n0100000020000=136P4P2P5f2R4P1C41536n0110000020000b3P2P5P4P1C6=136eW0X50W1W4W2o"). Qed.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh12aZh24addrh31bh41hh52nZp;1p;3p;2p;6p;4g0000j10Tg007Yj18Tg00<0j13Tg00UJj12Tg007?j31Tg00I[j37Tg0013j26Tg00Tlj64Tg00W_j45Tg002P#0#0#0#0#0#0#8#3g00Nig0022R0g00M8R1f3R2#2g00T1R331P1P3P1P1f0R3f4R4f2R5772g00MXR6n0100000020000=116X311616%24P3E4P4P2P5f1C5=116eW0X50W1W4W2o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__with61hp;1p;2p;4p;3p;8p;7g00Y6j1STg00ZDj1RTg00Zdj1CTg00[Dj2?Tg00[bj1QTg00\@j1LTg001Mj11Tg0000j10Tg000Uj15Tg00\kj26Tg00]Nj2PTg00^1j4<Tg00^\j1KTg00_>j3:Tg00_aj3ITg00`Dj8HTg00`hj2BTg0013j2DTg00aJj2ETg007?j3ATg00b6j3FTg00bUj4GTg005gj27Tg00cGj2;Tg00cdj2@Tg007Yj1>Tg00dAj1MTg009ej2NTg00e:j1=Tg00f2j7OTf0R0#1#1p=J%10#1#1#1p=2%00#0p=4%00#0#0#0p=8%00#0#0#0#0#0#0#0p=3f1R1g00fVR2g00g5R3P3g00gUR4P0g00h5FOp=9g00Ni%S0g0022R5g00hUR6#R%C61?51%Q5%L5R6P2P3P3P4P5g002PR2#J#2#2#2R7#1#0#4#8#3#3#3#5R8,65g00iAR91P52R:C<,96%K3P5%07#2#2#0#4#8#3#3#5R7,65P9%02#4R2#5R9,65%02#4R2#8#5R3,65R;5:5=:5;9I5:C<,96GH1B64P0f2R6g00M8R4g00MXR:'D1E06=A4:dg00O`=F51CGb3b4b5W017801;93/;3,@1,77[^05P0%>2%M6'NP1O2b2g00ih%=1'7eW1W6o"). Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h14__x2h24__x3h31Hh42H0h52Hzh67__arithh74__ffh88__varmaph95__with:1hh;1zp;1p;2p;3p;4p;7p;8g00Y6j1NTg005gj20Tg00k9j2?Tg00e:j15Tg00lWj19Tg00m6j23Tg00m_j38Tg00nHj2>Tg00ZDj1=Tg00o4j3<Tg00Zdj1;Tg00[Dj27Tg00oTj4:Tg00[bj1MTg00\@j1LTg001Mj1KTg00]Nj24Tg0000j1ATg00^\j1@Tg00`hj2BTg0013j2CTg00aJj2DTg007?j3ETg00b6j3FTg00bUj4GTg00^1j4HTg00f2j7ITg00`Dj8JTg0022R0f1R1g00iAf0R2CHp=1P1g00fVR3g00g5R4P4g00gUR5P2g00h5FIp=2f3R6P3P4P4P5f2R3P1P2GJp=6g00Ni%N1g00ihR7,011?61%56,07g00hUR8g0102R9#9R:#9,30130:1309580580g010Q'>%=83<%;8P01703P11706C:%M0%L0R8g002PR9#K,40R:%A9,40R;'1,28%@4R4P81409R9/1:,28P4119;,28C6C61B85P2P3g00M8R8g00MXR5'C1D23=E85dg00O`=F01CGb7b8b9X00X10X20103110161036[[^00^10^20P2P7f5#5f4P1P3O5b6b4W5W3X;0W:o"). Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Hh13Hloh22_Hh33_H0h44brk0h53inph63limh75mbaseh88reservedh92spp;1p;2p;6p;3g0000j12Tg007Yj1@Tg00<0j1;Tg00<Sj29Tg00Zdj1?Tg011=j1<Tg009ej20Tg005gj21Tg000Uj1:Tg006_j24Tg00;8R0j28Tg0122j65Tg012kj17Tg00Y6j16Tg00dAj1>Tg007?j3=Tg0022R1f0R2g00O`3=p=3g002P#2#2#2#2R3#2#2#@R4#;R5/95#?g013bf2R6#<P0g014\R7f3R8,04R9'1g015WR:,19%:3R3,49#3'8f7R9f6R;f5R<f4P8P6E5#7#6P2104<,17104;R6/1:1463#3'8P01049R0/1:1403#3f;R0f:R6f9R8f8P9P;E5#7#6P21048/1:1046/43#3P<f>f=f<P0P6P8E5#7R8#>,04,17e%68eW3W2f1R8P2O2n2001000000120000000W0W1P8P2O2n2001000000120000000W0W5X61X95X75X45W8o"). Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01Eh11Hh21bh31hh42h'p;1p;3p;2p;6g0000j10Tg007Yj18Tg00<0j12Tg00dAj11Tg007?j37Tg00Y6j16Tg009ej23Tg005gj24Tg00Tlj65Tg00NiR0g002P#0#0#0#0#0#0#8R1#2R2f0R3#1f1R4#137f2R5#6R6P2f3#1g014\1313'4X22P3%15P4E5P6eW1W0X40W3o"). Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01bh11hh21lh31mh42mbh52nah61rh72sbp;1p;2p;8g0000j10Tg007Yj19Tg00<0j14Tg00<Sj23Tg00Zdj18Tg00Y6j12Tg00dAj11Tg016Rj85Tg009ej26Tg005gj27Tg00Nig002P#0#0#0#0#0#0#9R0#4R1/31#8R2g0022f7R3#2f0g014\P3f6f5f4f3f2f1f8#1G5R3#1,60'7e%23eUX41W2X01X71X52X32W6W1o"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h52H1h62H2h72H3h82H4h94__p1h:6__sat0h;6__sat1h<4__x1h=4__x2h>4__x3h?1qh@1rhA1HhB2H5hC2H6hD2HrhE1zp;1p;2p;4p;6p;3p;7p;8g0000j1>Tg000Uj1ITg00ZDj1jTg00Zdj1\Tg017Ij1XTg00[bj1UTg00\@j1TTg00\kj2@Tg00^1j49Tg017gj6RTg00`hj2iTg0013j2gTg00aJj2`Tg007?j3BTg00b6j3ZTg00bUj4YTg018Kj3Vj2KTg018lj24Tg00cGj25Tg006_j22Tg019Ij2:Tg019fj2GTg01:Wj2FTg01;Hj1STg01;aj2Ej3QTg006Cj23Tg00;8R0j28Tg01<Hj2DTg005gj27Tg01<oj2HTg01=Uj2JTg00lWj1NTg00m6j2CTg00m_j3PTg00nHj2hTg00o4j3fTg00[Dj2OTg00oTj4eTg00^\j1_Tg01>;j6^Tg001Mj1]Tg00]Nj2?Tg01>_j7[Tg01?Cj3LTg00_aj3aTg00_>j3MTg01?fj1bTg00cdj2cTg00f2j7dTg00`Dj8WTf0R1#>#>p=;f2R2f1R3':/c1p=1P3g00fVR4g00g5R5P5g00gUR6P1g00h5Fdp=<g0022R7g00O`R87B1p=AAB731p=61781p=0f3R9P4P5P5P6P2P3P1GWp==g002PR:#>R;#>#;#;#;#;#;#IR<%I:R=511R>g00hUR?#jR@%\?RA%X7RB%U7RC%T7RDP4P5P5P6P71@7<REg01@dRF1@78RGC9,<DERRH1iD6RIP1P2g00M8RJg00MXRK'g1`12=BJKdAZ783CYRKb1b2b3%A<RJg01AK[RLP1b07V<14><,5<12><':,6>A13<=R>1G><%0>%0<RMA19<=RN/2<#0[[A12<=RO/F<%0ORPf4RQ?1<=RR/4<RS#0\M[1KN<%SJRT15<S12R<RS':,6R[1ER<138<RUf5RV?1<=RW/2<RX#013X<'8[1DW<13<8RYf6RZ?1<=R[/2<R\,3<17\8'8[1H[<f7?1<=R]/4<#A\J1J]<f8?1<=R^/2</6^\J14^<R_P7f9R`?1<=Ra/2<RbP7P@PAPBPCP7PGg01AhRGPEC9,<DRBPIPKb1b2b3PUP1b0b@b?b8b7b6b5b4b:b;7Q<12><R>#013><'81GO<%0S\M\P1FN<%0N14W<RN#0\M[1KR<15<N/:X,6W\T1EW<%0\13\<'8\U1D[<12]<R[,3<17[8'8\Y1H]<%A_\J1J^<16ba\J14a<P7f:Ra?1<=/2<P7P0%01131<f<152<'7P`%02139<R`p-0R0g0102RJ#NRb#N,C71C7b1C7J5P75P7g010Q'h=f?@PAP71O72P31O79CePCPDPDPB%_5RBPDP4P5P5P6PDP4P5P5P6PVE^P7%]:,?7R6PGPEC9,<DF[C=PBPDPDPHPBP71?7:R:=L7E1@7=5a7PF1?7;R;9M7E=L76C9,<DC=PBP7P:g00iAAM7;EC9,<DC=C=PIPKb1b2b3X<7X=7X>7W918Q`\U15<9/:Q,6O\L159<,72[[^<7^=7^>7^90P1%0VPVPZf@Paf;O6b0WCWBP3P1O2n2001000000121000000b@b?b8b7b6b5b4b:b;bDbA%b1,71eXE7o"). Qed.

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;2p;1p;3g0013j25Tg0000j10Tg007Yj12Tg01BOj21Tg01C5j14Tg007?j33Tg00M8R0g00MXR1'5g002P#0#0#0#0#0#0#2g00O`'1#4=301do"). Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h02HDh12HLh21bi001bh31Hh41eh51xh61yh71zh82H0h92Hbh:2Hch;1ch<5flagsp;1p;3p;2p;6g0000j16Tg007Yj1KTg00<0j1DTg01D<j1ATg007?j33Tg001Mj1JTg000Uj1FTg01E@j20Tg00@Wj19Tg00G^j1@Tg009ej22Tg01Eaj2=Tg01F?j2<Tg01;Hj1>Tg01F\j2ITg01G=j3HTg01G`j21Tg01H>j65Tg01HZj1ETg01I:j3CTg01I^j2?Tg01J=j2BTg01J\j1GTg00M8R0f0R1g00MXR233p=8g00T1R39301p=7f1R4=301p=4A3031p=:A3021p=;g002P#6R5#6#6#6#6#6#KR6#Dg0022R7%A4=371%J5#FR5,04#8g00;8R8%91#8%74R9[%71%94#8[R:f2R;#9#8\9%@1P1n2001000000120000000X20P:^20P1f4R:,26g01K\R9'=g00O`R<'<P81<41#7A37;4#>R8[A3741#>1<;4#7[R=f3R>/<;#7\81I41P1n2001000000120000000X67X57P=^67^57P1f5,26/=9R=P<A37=<R=f6,26R8?H951=89/0510851095R8'1'4P7f7,26R;/=91015R9f8R?,26/05/18R@'4X77P1P<P4E510<5R<10;5/18'4P0P<f9R<,26R;/05RA/18,41X20P1P3%E5E5%:@g01L[R@=C;51?;@/0510@5#9R;,1A'4P7f:RA,26R8/?@f;,26/05/1;R@,49X77P1P<P?E510<51085/1;'4P010A5f<,26/05R5/1;,41X20P1P2P?E5%;@P5P0P01112#:%93R5,14#;g01AKR@]0]1P11122R?#:1125#;P0P3P0p-0R;P1P@g01M]R6n0110000020000X40g01N9RAP?P4E5P@1B@1R?b3W0W11132#:1135R5#;P0P2P0P;P1P6P@n0110000020000X40PAP5P1E5P@P?b3W0W1n0110000020000P:P4O2b2b0b0b0b1b1b1W8%>=eO3b3O2b3%G>#8eW9W:W;W<o"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h01zp;2p;1p;3g019Ij27Tg000Uj16Tg00cdj20Tg018lj21Tg01NUj25Tg01?fj12Tg006_j23Tg007?j34Tg0022R0f0R1g00P>R2'7g002P#6'0/12/52%21/32g00O`540eW0o"). Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "h04__x1h14__x2h21Hh32Hzh47__arithh54__ffh68__varmaph75__with81zp;2p;1p;3p;4p;7p;8g006Cj25Tg01O5j1NTg01?fj16Tg005gj23Tg00lWj19Tg00m6j20Tg00m_j34Tg00nHj2@Tg00ZDj1>Tg00o4j3=Tg00Zdj1<Tg00[Dj2;Tg017Ij1:Tg00oTj4MTg00[bj1LTg00\@j1KTg0000j1CTg00]Nj27Tg00^1j42Tg00^\j1ATg00\kj2BTg00`hj2?Tg0013j2DTg00aJj2ETg007?j3FTg00b6j3GTg00bUj4HTg00f2j7ITg00`Dj8JTf1R0g00fVR1g00g5R2P2g00gUR3f0R4g00h5FIp=1f3R5P1P2P2P3f2R1P0P4GJp=8g0022R6g00O`R7/54%N0%60,30g00hUR8g0102R9#9R:#9,06106:1069546546g010Q'@%>83=%<8P61;61P0%:6CM%L6%K6R8P6g002PR9#C,76R:g00iA1769R9C2,18%A2R2P8P61B67R;g01AhR<P:C2,18P2P6P;P<P9C2,18C8C81?83P4P1g00M8R8g00MXR3'D1E41=F83dAG670CHb5b6b7X06X1613041571R7P7[[^06^16P4P5%65P0P1O4b4b2W3W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p;1p;2p;3g0000j12Tg007Yj16Tg00<0j1;Tg00Zdj17Tg01PRj2?Tg01QEj3=Tg00ZDj1<Tg0013j2:Tg01BOj23Tg01Qhj18Tg01Rlj39Tg007?j3>Tg00o4j34Tg00lWj15Tf4f3f2f1f0R03434p=0%50#5p=1g002P#2#2#2R0#6R1#;R2#7R3P2g00O`R41?145=1R5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5P2P5%<2D0D0D0D0D0D0D0D0':%20#2#2#2#6/34#81314g0102#1#1#1#1#1#1#1#15925>3do"). Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCeil ()) [] "p'0h02Hih14__x1h21ih31dh41lh53Hi0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4cstrh=1xh>2IHh?5cstr0i001np;1p;2p;3p;4p;6p;5p;<p;7p;8g0000j1ATg007Yj1_Tg00<0j1VTg00Zdj1BTg01SKj21Tg01SkR0j22Tg00lWR1j13Tg01TCj39Tg01Taj38Tg01U@j4:Tg00ZDj1CTg00o4j30Tg007?j35Tg01U\R2j14Tg006CR3j27Tg0013j26Tg01V<j4JTg01Vcj1@Tg005gj2;Tg00[Dj2ITg00[bj1WTg00\@j1UTg00\kj2HTg00]Nj2GTg00^1j4DTg00^\j1TTg01>;j6STg00`hj2QTg00aJj2PTg00b6j3OTg00bUj4NTg000Uj1RTg019Ij2<Tg017Ij1MTg00oTj4^Tg01?Cj3LTg01WHj4]Tg01X3j5\Tg01XUl<KTg00f2j7[Tg00`Dj8YTg01Y:l<ZTg01Y_R4g0022R5P0P2P3g01Z>R6f3R7f2R8f1R9g0102R:g00O`R;f0R<M<Kp=XP9g00fVR=g00g5R>P>g00gUR?P<g00h5F[p==P5P9g01AhP<CDp=?P7P=P>P>P?P8P9P<GYp=>P4P5P0P2P3P6f5R6f4R3P7P8P9P<M<Kp=FP4P4P5P5P1P2P2P7g01Z`P8P9P<M<Zp=Eg002PR2#AR1#A#A#_#VR0#BR@P01108,29%3:RAA9087580P0P8P7P9C:%C0RB50055@[^30^24RCX4@110B,29128:%48RD/7;REP8PD165D165;CXP<CJPE%@7%47,;;p-0REg00hURF#CRG%BFRF1I59%W5RH%U5RIP51H5;RJg00iA1G52RKCD,=I%T>RLPI1?KJ,=IPLPIP=P>P>P?P7ESC>C>1QI?R?P<P8g00M8R>g00MXR='61P<8=5>=dAO5;9CNR=b7b9b:X15W81;;<179;P7[[^15^8EP<A906B980AP0P6PBP3C:=00B55@%46REP9P8O4b6b<b5W0X30X24A0037,10,29P41106#3,2<f7R>f6RJ500RM9909980AP0P9PMP7C:=00B55@]0P81103#3,2:A00JB,6@A00J6R6990:980AP0P:P6P8C:=00B55@eW0%3<110J#3'2PJP9P3110>RJ,29%49R6%4JR:'7P9P61656RMPJP:165:RNEF%39RO%3JRP'2%R2R2,<61<:2'7RQPO1<<2RRX=5RSP6O1PSP9P6PMCEPPPSP:O1PSPJP:PNCEEFP<CJPQ%@81;;Df9,10RD#@%4D,;;PGPFP51I58P9%M5C^PHPI1H52RH9L5K1G51R1=L5H'?,=IPL1?K1,=IC>P?P=b7b9b:X15X;51<92,7R1798[^15^;5P<f;,10#4PEP7O3b6b?b<b5C]O3f8=00>R>990O980AP0POP>P3C:=00B55@eW0X24P<O1n0110000020011100P<O1W0X30X24X>CX4@X=0P<D\W4o"). Qed.
