(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_malloc_small () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:alloc_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocAmalloc_small_ctrlC13~~~C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=size_to_classC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>F_malloc_small9coarse_scC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6lowbitC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_set_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5ctz32C13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option02K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev06C13~~~K47Corelib4Init5Logic2eq01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;layout_hook00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4FUELC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<undef_reason03C13~~~C47Corelib5Lists7ListDef3seqC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List:length_seqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5usageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?bits_above_log2C46Stdlib4Bool4Bool<andb_false_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z?pow2_bits_falseC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4evenC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z4EvenC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z9even_specC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z4onesC47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib4Init5Logic4True01I47Corelib4Init5Logic2ex00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>F_malloc_small:lor1_checkC13~~~C56Stdlib6ZArith6BinInt1Z3lebC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe<forallb_zseqC13~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>F_malloc_small?lor1_check_trueC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>F_malloc_small@lor1_range_checkC13~~~C47Corelib4Init9Datatypes9andb_propc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>F_malloc_smallElor1_range_check_trueC13~~~C47Corelib4Init9Datatypes2idC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p'0h01Rh14bailh23idxh31kh43layh51nh62sth73st1h85firsth91gi001gh:4maskh;2sci012gpi021xp;2p;1p;3p;4p;5p;9p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022R1p4p710p8P0P1p4p7210p8P0p1002Mp5p710p8g002iR0p4p70g0047R1p4p710p8p200R2g005GR3p4p710p8P2g006RR4p4p7210p8P2p1007fp4p7210p8p1009Ap4p7210p1009^p4p710p8g00:<j2FTg00:\R5j1ETP3j10Tg00;>j16Tg00<Uj2DTg00>1j21Tg00?Aj2>Tg00@Wj1=Tg00Ahj1;Tg00C8j2:Tg00CUj17Tg00D3j28Tg00DPj19Tg00Eej3CTg00G7j1BTg00HFj42Tg00Hfj23Tg00IHj2ATg00Iej1@Tg00JGj1?TP1j54TP4l95Tg00KUj2<Tg00KoR4g00MFR1g00NXR31F03R6#Ef5R7#0R8[\1R9f4R:#0R;f3R<f2R=#6'DP3f0R>,1:g00O6P5P0P3P>f6R?/>>#=g00PDR@n10110000021010100P3%;>P3P5P0f:RA#0P=g00PbRBf;RC#0f1RD/:@#7P?18=D#9f8RE5C>P0P3P>%BDC2,36O2p,4RUNpRFPAf9RAg00QBRGPEP:f7RHPBf=#0RI1A>@R@PEPD%@6RJO2P5P0PI11D?PAP=P0P3P>PDC2,36R6O2g00RPRIP3f<RKg00S^#?RLPEV3D4n10110200021010100n0100000020000X23X71P7M95n0110200020000PFPAPEPGPHP<P?PB%0KRKP@PHPDPJO2P5P0PK11D7PEP=P6O2PIP3PCPLPHV3D4n10110200021010100n0100000020000X23X71P:M95n10110000021010100b8b:b9b;,<8X1;X39X53X61X44X02P7P:P<P=PDP>O6W1W3W5W6W4X02o"). Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "h01ih11nh22stp;2p;3p;6p;1p;4g00U6j2@Tg00URj23Tg00V2j34Tg00KUj2?Tg00VLj2;Tg009^j65Tg00Vkj11Tg00WPj18Tg00Wnj17Tg00XQj16Tg00Y1j29Tg00Z@j1:Tg00[Pj4>Tg00[lj4=Tg00\Kj1<Tg00]_j10Tf0R0#0#0#0#0#0#0#0#0p=2g00MFg00^>R1g00^]R2%22#2#2#2#2#2R3'@R4,31R5A4103X11R6P1P3P61?13P51;32E5g00_<#1#1#1#1#1#1#8#7R2P1P2f1%60'9#:X01R5P4C>'3P1P2P5P4C=E5%<0,32=413eW2o"). Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "h04__p1h14__x1h21ih31Hh47__arithh54__ffh64__p2h74__p3h88__varmaph95__with:4__x2h;1mh<1nh=1oh>1xh?2H0h@3HschA1bhB2schC2sthD1zhE2z0p;2p;1p;3p;4p;7p;6p;5p;<p;8g00_aj29Tg00`=j1wTg00Vkj12Tg00`bj1XTg00a@R0j27Tg00a\R1j23Tg00WPj1bTg00Wnj1^Tg00:\j1MTg00XQR2j1LTg00Y1j24Tg00Z@j15Tg00]_j10Tg00U6j2jTg00b7R3j1DTg00bWj3ETg00c5j4?Tg00Hfj26Tg00V2j31Tg00cYj28Tg00d9j2ITg00Iej1NTg00dPR4j2CTg00dhj2ZTg00eKj2BTg00KUj2@Tg00ehj2VTg00fJj2KTg00fdj2HTg00gMj3JTg00h6j2UTg00hbj1RTg00iBj3STg00ibj1TTg00jBj2QTg00j`j1uTg00k>j4tTg00k\j1qTg00l:j1oTg00lej2PTg00mHj4:Tg00n3j2OTg00nVj7iTg00o:j2hTg00o\j2gTg010Hj3cTg010gj4dTg011Yj4eTg012Dj4aTg012`j2fTg009^j6GTg013>j6`Tg013Zj3kTg00[Pj4lTg014<j5_Tg00\Kj1mTg014^l<nTg015Cl<]Tg015hj6\Tg016Lj7pTg0170j7[Tg017Tj8sTf0R5#0#0p=v%05#0#0#0p=r%05#0#0#0#0#0#0#0p=<g00PbR6g0188R7715p==g00NXR8g00^>R9P8P8P3f4R3P2f3R:g018Xf2R;f1R<P5M<np=YP9P8P4P2P0g019Ef5R0P3P:P;P<P5M<]p=WP<g019gR2g01:FR4P4g01:fR=P5E\p=AP<P2P4P4P=P5g01;FFpp=;P;P2P4P4P=P<P5F[p=>P:P2P4P4P=P;P<P5Gsp=Fg00MFg00PDR>/95R?g00_<R@#w#2#2#2#2#XRA,75'3%2@RB#2#2#2#2#2#b#^RC#MRDP9PC%L5RE,4:#5X29RFg00^]RG%0GRH#0RI#v#r#<#<#<#<#<RJ'jRK%D<RL5E9RMC?14:;#5,6CRN91D5X=D%M9ROP6PO18LJRP1IGL,69%N9RQn0100000020000P9PC143E#5X29RRP5C?=1DNX=OP6PPP7P118<5#=1C;<R1[1C<518;<#=[RS18:;#=\11Z<5P5n2001000000120000000X;9X<9PS^;9^<9P5%D;RSPJ1CSJ1B>;R1/7APSP1P5X>81B>5X>8P;P;1@8;DYPJPA1@8AEW1V>;17>;A181;'319;>A181>'3'K1B>:P8p-0R1g01;fRT1H8I1H8H1H8G5J85J8g01<R'U%RTRH3S%TTRTP81Q8;P<%u8Ct%q8RI%o8RUPUP2P4P4P=1AU3P81P8@R@g01=>R21P8BRBC:,;U5>U1AU0P8P@P21O8>R2C:,;U5>UFi%N4R4PUf6,AUP8PBg01=eRB1O8ARVC:,;U5>UP4P8P@PBPVC:,;UCFCF1hU=R=P5P;1@671g5;#=dAc8><CdRVb5b8b9X18X:8X01X61W7A185<,3;A185>,3:'K17;ARB,30PB[[^18^:8^01^61^71P519>0190>17>0P0P<P;P3O7b4bEb?CeO3b3CaA167PP6P7P9PC140E#5X29P6POP5%D:,IG,69PQn0100000020000C?143:#5,6CRQ51DXA6P8P;1435#5,6C=1DQXD81@DN%LSPHPT1Q8<PIPUP8P2g01>LP@C:,;UR@1AU:5>UP4P@CFP=PVb5b8b9X18X0113?<19><[^18^01P517:AP:P;O3b4,f;EGP9PCPR1IGS,69C?=1DNe18SJP5E`b3PMAkGJLEGP9PCPFPKCl=ECLP9PCPFPLPKD_EG%m;=ECL14;<#5,6C51DeW@XB8WCo"). Qed.
(* [comment removed for export] *)

Lemma lxor_sign_small x : 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p'0h06__sat1h14__x1h24__p1h31bh47__arithh54__ffh66__sat0h78__varmaph85__with92Hih:2Hxh;1xh<1Hh=2Hah>1ah?1ei001eh@1ihA1si011shB2NEhC2NZhD1zi021np;1p;2p;3p;4p;6p;7p;8g00Vkj1wTg00`bj1MTg00`=j1;Tg01?3j2ETg00a@j20Tg00a\R0j2:Tg01?Pj2NTg00KUj2>Tg01?mj2VTg01@Kj2FTg01@ij21Tg01AJj25Tg00V2j33Tg01Ahj2KTg01BHj17Tg01BaR1j2HTg01CAj2bTg01Cij3`Tg01DMj2_Tg00hbj1^Tg00ibj1[Tg00jBj2ZTg00k\j1YTg00l:j1XTg00n3j2CTg00lej2WTg00mHj4?Tg015hj6UTg00Iej1TTg00o:j2RTg00o\j2QTg010Hj3PTg010gj4STg01Dnj14Tg00_aj2OTg00j`j1vTg009^j7Lj6DTg01ELj3uTg00WPj1tTg01F2j3pTg01FUj4oTg012Dj4nTg013>j6JTg01G>j1fTg00]_j1eTg00fdj2ITg01G^j1cTg01H<j2dTg01H]j3aTg00gMj3gTg00h6j2hTg00iBj3iTg01IFj3jTg01Ioj1kTg01JOj3lTg01K2j3mTg01KUj3]Tg016Lj7\Tg0170j7qTg017Tj8rTg01L?j6sTg00PDR2f0R3'Op=6g00NXR4f1R5;33p=8g00PbR6g01LcR7733p==P5g019gR8g01:FR9P9g01:fR:P3g01;FF\p=2f2R;P8P9P9P:P5P3Fqp=Gf3R<P8P9P9P:P;P5P3Grp=9A3432p=<P4P5g01=eP3C?p=@P4P5g01=>P3C?p=AP5P8P9P9P:P3Esp=B%63R=g00_<R>#w#MR?%;>#;#;#;#;R@#MRA'ERB,03RC':RDP41N5BRE1N;B,83XD41>4E1V5B1F5BP611<511B5RE'5112;9363X36P6P7f4RF/1;11B;'5=363X361K5A185ARG%7G'HP118;ARG%7Gf5RG/1<11B<'5#=P318<ARHP4PAf8RI/15/5E#=^9=X@4%6AREP6f7RJ/1ARKP7PJPA1b?ARL102?RM102BRN\ERE[RO%6?RPg01MCRQA`?A5UW=RR%6B\Q^=PRPP5g01M_1_2?'>PMeO1RMPEp-0RQg01;fRS#^RT%[SRU1Z45RV%Y4RW%X4RXP41C42RYg01>L1W4>RZC?,2XR[PXP8P9P9P:P<EUR85GXR\%T9R9P[C91RX:R:P3P;g0188R[,>61Q3;=36[dAP425CSR[b5b7b8X14W21:=5%65R][^14^2QP3f;R^/0BP^f:R_O3b4b0b6b01KJ2%<JR`%7`'HP1%<IR1%71f9R1#4/0AP3%<1R`P4P2%45/0A^:DX;41O22/:NPLPOPRPPPMPEPTPU%v4PW1C4ARN,@Y,2XP:P[b5b7b8102AP3b4b0b6b0%42/0AeW:P_P3P1FLW?P3O1%7`1025R`P01E?5,0;%4</0;[R0%4;/051E?;,0<R1[%4F/0<\1Au;53P5n2001000000120000000UX34X>4P0\`^34^>4P3P^PAPLPOPRPPPMPEPTPUPVPWPX1AZY,2X,BXP9PXP\P91@YZ,2XC9C9P:P[b5b7b8X14X2Q%<3g01NERY[1:];102;[[^14^2QP3f?R;/0BP;PGf>R]O4b4b0b6b0PLPOPRPPPMPEPTPUPVPWPX1C4?%t@5p4,@Z,2XR@9GX8P9P@C9P:P[b5b7b8X14X2Q1:5C105B[^14^2QP3%6;P;P]O3b4b0b6b0O4b<WCP3O1n200110100021110011102bACoCnA367KP6P711BA,53#=X361>6711IAP3EJb<W9PFP3P<FLW?P3O1%7HP6P711JG/53#=X36f6/1F#f11BFPLPOPRPPPMPEg00^]RE#e,I4%c>,d41I4E5a45g4g01<R'h=iSTPUPVPWPX1AZN,2X,BXP91ANZ,2X,BXC9P:P[b5b7b8X14183APY[18A5PY[[^14P3PIPFO2b4b0b6b09jAFEDWBP3O1n200110100021110011102bA1125%k5ED1F<B/15Al<B5EDX9=X@47m29]5BEJW:X;4P3O1X;4o"). Qed.

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "h01yh17__arithh24__ffh38__varmaph45__witp;1p;2p;4p;7p;3g00Vkj10Tg00`bj1ATg00hbj13Tg00ibj12Tg00j`j1@Tg00k\j1:Tg00l:j14Tg00n3j21Tg00mHj45Tg016Lj76Tg00o:j27Tg00KUj28Tg00o\j29Tg00V2j3?Tg010Hj3>Tg010gj4;Tg00_aj2<Tg01Nbj3=Tg00NXR0f0R1g00_<#0#0#0#0#0#0#AR2g01;fR3#3%23%@0%:0%40R3g019gg01:FR4P4g01:fR4P0g00PDR5,10g01>L1102C5g01;FF61734P1f2R4g00PbR3g0188R6'81914=?36df19>05C;b2b3b41<52P1b13=X00P1O1W0o"). Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p'0h01Hh11xi001xh21zh32H1h47__arithh54__ffh68__varmaph75__with84__x1h94__x2h:4__x3h;2H0h<2H2h=2H3h>2H4h?2H5h@6__sat0hA6__sat1hB1bhC1khD5lemmap;1p;2p;3p;7p;4p;6p;8g00Vkj1wTg00`bj1NTg01?3j2\Tg01OEj20Tg01Oej1JTg01PCR0j2ITg01P\j1GTg01Q:j3VTg01Qlj7STg01Rgj1PTg01SJj23Tg01Sgj26Tg01TDj2qTg01U5j2iTg01Ufj2aTg01BHj1`Tg01?Pj2LTg01VGj2]Tg00a@j25Tg00a\j2BTg01Vnj2YTg00_aj2FTg01WUj2XTg01X;j2WTg01Xaj2UTg01DMj2TTg00KUj2ATg01G^j1RTg01H<j2QTg00]_j1DTg00fdj2;Tg01H]j3CTg00gMj38Tg00h6j2HTg00hbj1OTg00iBj3ETg00ibj1vTg00jBj2MTg00k>j4uTg00k\j1tTg00l:j1sTg00n3j2=Tg01L?j6pTg00Iej1kTg00lej2@Tg01Z6j3jTg00`=j1hTg01ZYj3eTg00o:j2bTg00o\j2cTg010Hj3dTg010gj4_Tg01[<j4fTg01[Vj2gTg009^j6:Tg01\6j2^Tg01\Xj4lTg01]3j1mTg01@Kj2nTg00j`j1oTg00mHj4KTg01Nbj3[Tg00V2j3<Tg016Lj7ZTg017Tj8rTg00NXR1f0R2g00PDR33<p=2g00PbR4g0188R57<2p=?f1R6=<12p=41F32p=1P1P6g01=>P2CKp=9P6g019gR7g01:FR8P8g01:fR9P2g01;FFZp=7f3R:P7P8P8P9f2R;P6P2Grp=>P1g00_<R<#wR=#NR>%N<R?'\,02%22R@%J6#?RA'IX21%J2#?%G2RB'Ip-0RCP0g01]Q9VC0106>#2RCPA%G6RAP2FSWD%P2102>#2R0PA[PC\BP113>2RC,4;XB1RA166>1q6>%16%1>RD10:>#1[[1i;>%1;f4RE/6>RF#1\D[1a:>%2>RD#`13>F10E>'L,4E[1]E>153>RFf5RG/0>RH#115H>'B[1YG>15>3f6RH/0>RI,5>1FI3'B[1XH>f7RH/6>#2\D1WH>f8RI/0>/4I\Dg01^C1UI>RIePIPEg01M_1T3>'APFeO1f9RF/0>RI#115I>'Bg01;fRI%R<,Q1RJg00^]RK#DRL#D,;1RM5C11;1LRL9C1J1;1KRK581581g01<RRJ'HA81LK981M/HJ%OIRJ5EI3E%vIRIP11M1;P61M1:Cu%t1RM%s1RKPKPKP7P8P8P91=1>R71=13RL'9,7KEp%k8R81@1<RN1@1=9j17R7%h<,@1R<5e1'9,7KC>P8PK19<L,7KP819N7,7KC>C>1bK9R9P2P;1A451c2;#?dAd136C_R5b5b6b7X81X91X:1g01NE\D13>;/L:,46[%2:13>:,4;[[^81^91^:1P2f;R:/0>16:>P:PHf:O5b4b316F>,3>,4Feb?b>b=b<b3b;b@bACfX00g01^_P1PA10;>#2P214ECP113>6REP0X11P1136>RCP0X21P1P3P@X211A1310C>1g6>E:PE1^>6E:PGP2E:W0XC1P6P2O2n2001000000120100000X0BClO2%m?,n2PJPI%o1PMP1PLg01>L1=1?CK,7KP9P5b5b6b7%1?P2b49[2?E:X11P2O1X11o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p;2p;3g00KUj21Tg00V2j30Tg00PbR0g0188R1'1g01_9=001do"). Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "h04__x1h11mh21nh32H0h41Xh57__arithh64__ffh74__p1h88__varmaph95__with:1bh;2sch<1Eh=1Hp;1p;2p;3p;4p;7p;6p;8g00Vkj14Tg00`bj1@Tg00_aj25Tg00a@j2:Tg00a\R0j2?Tg01Oej1;Tg01`Vj23Tg00IHj28Tg01AJj22Tg00CUj16Tg01a3j11Tg01bGj29Tg01bdj27Tg00`=j1]Tg00hbj1XTg00ibj1WTg00j`j1VTg00k\j1UTg00l:j1TTg00n3j2>Tg00o:j2QTg00KUj2PTg00o\j2OTg010Hj3NTg010gj4MTg00jBj2LTg00lej2KTg00mHj4ATg00Iej1JTg01ZYj3ITg01?Pj2HTg01cAj7RTg01dbj2GTg015hj6STg012Dj4ETg00V2j3DTg009^j6FTg01eBj2^Tg013>j6\Tg016Lj7[Tg0170j7ZTg017Tj8YTg00PbR1f0R2g0188R33Dp=0g00NXR4f1R5g01>LP2CAp=CP5g019gR6g01:FR7P7g01:fR8P2g01;FF[p=<f2R9P6P7P7P8P5P2FZp==f3R:P6P7P7P8P9P5P2GYp=Bg00_<R;#4#4R<#@R=/52R>%4<#4#4#@R<,:2R?'?R@%;5#013=2182<'2%;2'2#6%12%@;RA,92#1'3'7X;4RBg00PDRC%];#4#4#4#4#@RDP9g01ebg01;fRE#XRF%WERE%V4%U4RG%T4RH1>4CRI/CI'<1QH8RJP2P91P131O29#0dAN4C5CMRKb6b8b915CCP2b5PFPE1L45RLPGPH1>4=1K4;R;'C,<HRMP4P;g01=eRN1>4<CA,<HRO5=H%J7RP1CI;,<HP4P;PN1>4D9I4ICA,<H5=HCBPJPKb6b8b9X0415C51HCD,:5'?\@^04P2P:P9O2b5FRPBP9O1#0P113=:RBP3P01352#01595R@[RD15521395#0RC[RI13:9#0\@1G52R@P2n2001000000120000000X14X24PI^14^24P2P=f4RNp-0R;PFPEPLPGPHPHP6P7P7P8P:ESR89=HMPPPMCBPJPKb6b8b9X04W71?>515=5[^04^7;P2f5R>/:<P>PNO3b5O3b3CEAD13BP113=N18><RB,22%;>'2#6%1>19>A#1'3'7#0X:1P5P3P2EF18N<,23%;N'2#6%1N19NA#1'3'7#0P1PBP3P01852#01:95RN[1:521895#0[RM18:9#0\N1^52P2n2001000000120000000X14X24PM^14^24P2f6RMP<PFPEPLPGPHA=H8OPPPOCBPJPKb6b8b9X04X7;1?5?1:5<[^04^7;P2f7R;,5=P;PMO3b5O3b3CEAD13BP118M<1232%;;R<'2#6%1;19;A#1'3R;'7#0X:1P5P3P2EF1233RB%;M'2#6%1M19MA#1'3'7#0P1P<12B2#6f8R<#119<A#1'3'7#0X:1P2P3P>E\12B3#6/7;#0P0PDPI15:9\CP@P5n2001000000120000000X14X24PD^14^24P2f9RD#119DA#1P5O3b3b4b4b3b4b3b4W<W=X;4P2O1X;4o"). Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p;2p;3g00KUj21Tg00V2j30Tg00PbR0g0188R1'1g01gD=001do"). Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "h04__x1h11mh21nh37__arithh44__ffh58__varmaph65__with72sch82H0h91Xh:2X1h;2X2h<1Hp;2p;1p;4p;3p;7p;8g00_aj22Tg00`=j1VTg00Vkj18Tg00`bj1<Tg00a@j23Tg00a\R0j26Tg01bGj21Tg01`Vj24Tg00IHj25Tg01AJj2BTg00hbj1ATg00ibj1?Tg00j`j1>Tg00k\j1UTg00l:j1TTg00n3j2=Tg00mHj49Tg00o:j2LTg00KUj2JTg00o\j2ITg010Hj3ETg010gj4DTg00jBj2FTg00lej2CTg00Iej1GTg01ZYj3HTg01?Pj2KTg01cAj7@Tg01hgj3MTg01dbj2NTg01eBj2OTg016Lj7PTg00V2j3QTg0170j7RTg017Tj8STf1R1g019gR2g01:FR3P3g01:fR4f0R5g01;FFPp=7g00PbR6g0188R77Q5p=0f2R8P2P3P3P4P1P5FRp=;f3R9P2P3P3P4P8P1P5GSp=:g00NXR2g00PDR:/25g00_<R;#V#8#8#8#8#<R<,35R='6R>%<;R?,15R@,4:15@<'BX72R@P:P<P1g01iJg01;fRA#ARB%?ARA%>2%U2RC%T2RDP21=2:REg01>LRFPEC9'71LD4R4P5P81J671I58#0dAE2:1CDR7b4b5b612::P5b3PBPA1F21R6PCPDP2PEPF1C2;R;C9,7DRFP2P;g01=eRG1=2<RHC9,7DRI5;DRJ%G3R3P2P;PGAH2EHC9,7D9;DFC:P4P7b4b5b6X0212:1RH1K:<,31'6\>^02P5P8P1O2b3F@P@P1O1#0118?R@,4:R>15@<R@;M5%0>%0@'6P0119?R@,4:#015@<#0f4/1?R@,2:13@<'6P5f5/1?,4:#0f6/1?/5<#0P01415#01281[R@12151481#0R>[1298\>1N15P1n2001000000120000000X12X22P@^12^22P5P:f8/1?R@P8O312:@P01515#01381[R013151581#0R@[1398\@1O15P1n2001000000120000000X12X22P0^12^22P5f:/1?R0P<P9O3130<PBPAP6PCPDPIP3PDPFP3PJC:C:P4P7b4b5b6X0212:8138<'6\H\=^02P5f</1?P1P9O3b3b;b8b:b8W;W:P1P5O2n2001000000121000000b9b9W<X72P5O1W7o"). Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["CEIL_WRAP_1"] "p'0h01Eh11mh21nh32E1h42E2h52H0h61bi001bh72sch82sth92E3h:2E4h;2E5h<1Hh=1ai011ah>1oi021oi031xp;1p;2p;4p;5p;3g00`=j1^Tg00Vkj1@Tg00`bj1BTg00a@j24Tg00>1j26Tg01`Vj22Tg00IHj23Tg01Oej1ATg00Y1j21Tg01bGj25Tg00:<j2XTg01k2j1VTg01G^j1UTg00HFj4TTg0022j5GTg00?Aj2FTg00@Wj1ETg01kNj1DTg01?Pj27Tg00_aj2?Tg00KUj2JTg01l_j3NTg00V2j3<Tg01AJj2ITg01hgj3MTg01dbj2STg01eBj2RTg00a\R0j2;Tg01\Xj4PTg01m9j3\Tg00<Uj2WTg00C8j2OTg00CUj1YTg00fJj2ZTf2R1f1R2'?f0R3';p=]1O23#Yp=91I12/I3p=:g00PDR4,O3p=81O34,I2p=Cg00PbR5g0188R67<3p=0g00NXR7f7R8f6R93<f5R:f4R;5<7f3R</?1/;2/;3';'Zp=>A<723p=KA<7;<1;12/;3';p=Q1212/I3p=HA<536,;2p=L%A3=<56p==A<712/;3p=[g00MFR6g00_<R=#^R>#@R?#@R@#@#@#B,439]431612g00O6g00:\R4g002iRAP4PAP7P3P;P5P7%@=#@RB#BRC/2<%@B#@#@#BRB,3<%B?R?,9<3:%A<RD11;<#83:REP5P7P4PAP7%B=RF,5<RG,6;P5P7g01mSRH/X7RIPI%VIRJPHP7g01n1%U=CTR=15;FRH,6:DG,F:RK#E#8%DK'C11:HRK%B>R>'7PKn010000002000011;G/7>n10110300021010100%B@R@'2PGP<n0100000020000P<n0100000020000n10110300021010100RKP<PKPGPCP<14<B%0DG>P31K;;P;PH1?C;14;B%A;RH#0DQ1J7;3NX=AP3O112C1131B191?3:%A111<1#83:P51J53A<5E3P513:B9HC:19:?%A:RE3:RD119:#8RG'I=<53P5P7P2P5P7P4PAP7159FRK,68P5P7f8RLPIPIPJP=158FRM,6LRNDG'FRO#E#8%DO'C11LMRO/7>RPPOn0100000020000118K/7>n10110300021010100/2@PKP9n0100000020000P9n0100000020000ROP9POPKPCP9149B%A9RK#0G>]0P212C;13;B19;?3:11:;#87:HRH#0AMDG3%0D/LGP0139B9HC9199?;:K#01189#8#0P5P7P4PAP7PNP5P7f9RNPIPIPJP=15LFR9,6NDG'FRK#E#8%DK'C11N9R9/7>P9n0100000020000PPn10110300021010100/2@PMP8n0100000020000RPP8PPPMPCP8148B%=8G>P313LB9HCL19L?%AL3:#0f:RL/1N#8#012CL13LB19L?3:RN%ALRL;M2%0N/LLP0f;RL,2C13LB19L?3:#0%=LP5P7P4PAP7f=RLf<RN/5FR8'6P5P7f>RMPIPIPJP=15LFRP,6MDG'FR9#E#8%D9'C11MPRP/7>PPn010000002000011L8/7>n10110300021010100/2@P8PNn0100000020000RPPNPPP8PCPN14NB%=NG>P312CL13LB19L?3:#0%=Mf?RM13MB5HCRL19M?RN;M2%0L/LNP0f@RN13NB5HC#019N?#0P5P7P4PAP7fBRNfARL/5FR8'6P5P7fCRPPIPIPJP=15NFR9,6PDG'FRK#E#8%DK'C11P9R9/7>P9n010000002000011N8/7>n10110300021010100/2@P8PLn0100000020000R9PLP9P8PCPL14LB%=LG>P313NB9HCN#019P?#0fDRP,2CR?13PBRP;M2%0?/LPP0fERP,2C#013PB#0P5P7P4PAP7fGRPfFR?/5FRN'6P5P7fHRLPIPIPJP=15PFR8,6LDG'FR9#E#8%D9'C11L8R8/7>P8n010000002000011PN/7>n10110300021010100/2@PNP?n0100000020000R8P?P8PNPCP?14?B%=?G>P312CP#013LB#0P01223#01?12[RL1?231212#0RP[1?<1\P1S23P2n2001000000120000000X17X27PL^17^27P3PCfJRLP1O31?CLP01323#01412[R014231312#0RL[14<1\L1R23P2n2001000000120000000X17X27P0^17^27P3fLR0PBP<O3140BP4PAP7fNRAfMR4/5FR0'6P5P7fORLPIPIPJP=15AFR=,6LDG'FRJ#E#8%DJ'C11L=RJ/7>PJn010000002000011A0/7>n10110300021010100/2@R@P5P5P5P7P315LFR>PLn0100000020000RJPLPJP>PCPL14LB%=LG>P31K=A1K==RL1?CAR>14ABRJ';RI%=ARP';R?';PLP?1J7=PIPPP>PJP<P2CPPMCPCP3\1KAAA[A=?1J7A3Nn0110000020000b6P5P7P@P0P4n0100000020000R@P4P@P0PCP4144B%=4G>eb4b5b3b5W4W3P2P3O2n2001000010121000000b0W9W0P2P3O2n2001000010121000000b0W:W0P2P3O2n2001000010121000000b0W;W0P2P3O2n2001000010121000000b0W0g01Lc9<5H1K::P:15:F1?C:14:B%0EDQ1J7:3NW0n0110001020100P3O1b0b6n10110201021010101b>1W12R1P2P1152FPCP2142B%=2G>eW<X77X86P2P3O2X77W8o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
