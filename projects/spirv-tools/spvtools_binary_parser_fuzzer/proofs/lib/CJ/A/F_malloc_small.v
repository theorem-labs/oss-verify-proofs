(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_malloc_small () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2CJ4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A>F_malloc_small9coarse_scC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2CJ4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib2CJ4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2CJ4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib2CJ4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List:length_seqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2CJ4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocRep2wzC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib2CJ1A9MallocRep6usagesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4evenC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z4EvenC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z9even_specC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib2CJ1A>F_malloc_small:lor1_checkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2CJ4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib2CJ1A@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc69OSSVerify5KrLib2CJ1A>F_malloc_small?lor1_check_trueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A>F_malloc_small@lor1_range_checkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propc69OSSVerify5KrLib2CJ1A>F_malloc_smallElor1_range_check_trueC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC69OSSVerify5KrLib2CJ4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes4bool02".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "p'0h03idxh13st1h21Rh34bailh45firsth51gi001gh61kh73layh84maskh91nh:2sch;2sti012gpi021xp;2p;1p;3p;4p;5p;9p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022R1p4p710p8P0P1p4p7210p8P0p1002Mp5p710p8g002iR0p4p70g003aR1p4p710p8p200R2g004[R3p4p710p8P2g005PR4p4p7210p8P2p1006Np4p7210p8p1007Sp4p7210p10080p4p710p8g008Nj2FTg008nR5j1ETP3j10Tg009Pj16Tg00:Qj2DTg00;Sj21Tg00<Mj2>Tg00=Mj1=Tg00>Hj1;Tg00?Bj2:Tg00?_j17Tg00@=j28Tg00@Zj19Tg00AYj3CTg00BUj1BTg00CNj42Tg00Cnj23Tg00DPj2ATg00Dmj1@Tg00EOj1?TP1j54TP4l95Tg00FGj2<Tg00Fag00GbR4g00H^R11F01R3#Ef5R6#0R7[\4f4R8#0f3R9f2R:#6'DP1f0R;,18g00I<P5P0P1P;f6R</>;#=g00J4R=n10110000021010100P1%;;P1P5P0f:R>#0P:g00JRR?f;R@#0f1RA/:=#7P<18:A#9f8RB5C;P0P1P;%BAC2,33O2p,5ACEILRCP>f9R>g00K2RDPBP8f7REP?f=#0RF1A;=R=PBPA%@3RGO2P5P0PF11A<P>P:P0P1P;PAC2,33R3O2g00KjR;P1f<RFg00Lb#?RHPBV1D4n10110200021010100n0100000020000X01X14P6M95n0110200020000PCP>PBPDPEP9P<P?%0FRFP=PEPAPGO2P5P0PF11A6PBP:P3O2P;P1P@PHPEV1D4n10110200021010100n0100000020000X01X14P8M95n10110000021010100b4b8b5b:,<7W3W6W9W;W7X22o"). Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "h01ih11nh22stp;2p;3p;6p;1p;4g00Mdj2@Tg00N@j23Tg00N`j34Tg00FGj2?Tg00O:j2;Tg0080j65Tg00OYj11Tg00P>j18Tg00P\j17Tg00Q?j16Tg00Q_j29Tg00RXj1:Tg00SNj4>Tg00Sjj4=Tg00TIj1<Tg00UCj10Tf0R0#0#0#0#0#0#0#0#0p=2g00Gbg00UbR1g00VAR2%22#2#2#2#2#2R3'@R4,31R5A4103X11R6P1P3P61?13P51;32E5g00V`#1#1#1#1#1#1#8#7R2P1P2f1%60'9#:X01R5P4C>'3P1P2P5P4C=E5%<0,32=413eW2o"). Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "h04__p1h14__x1h21ih31Hh47__arithh54__ffh64__p2h74__p3h88__varmaph95__with:4__x2h;1mh<1nh=1oh>1xh?2H0h@3HschA1bhB2schC2sthD1zhE2z0p;2p;1p;3p;4p;7p;6p;5p;<p;8g00WEj29Tg00Waj1wTg00OYj12Tg00XFj1XTg00XdR0j27Tg00Y@R1j23Tg00P>j1bTg00P\j1^Tg008nj1MTg00Q?R2j1LTg00Q_j24Tg00RXj15Tg00UCj10Tg00Mdj2jTg00Y[R3j1DTg00Z;j3ETg00ZYj4?Tg00Cnj26Tg00N`j31Tg00[=j28Tg00[]j2ITg00Dmj1NTg00\4R4j2CTg00\Lj2ZTg00\oj2BTg00FGj2@Tg00]Lj2VTg00]nj2KTg00^Hj2HTg00_1j3JTg00_Zj2UTg00`Fj1RTg00`fj3STg00aFj1TTg00afj2QTg00bDj1uTg00bbj4tTg00c@j1qTg00c^j1oTg00dIj2PTg00dlj4:Tg00eWj2OTg00f:j7iTg00f^j2hTg00g@j2gTg00glj3cTg00hKj4dTg00i=j4eTg00ihj4aTg00jDj2fTg0080j6GTg00jbj6`Tg00k>j3kTg00SNj4lTg00k`j5_Tg00TIj1mTg00lBl<nTg00lgl<]Tg00mLj6\Tg00n0j7pTg00nTj7[Tg00o8j8sTf0R5#0#0p=v%05#0#0#0p=r%05#0#0#0#0#0#0#0p=<g00JRR6g00o\R7715p==g00H^R8g00UbR9P8P8P3f4R3P2f3R:g010<f2R;f1R<P5M<np=YP9P8P4P2P0g010if5R0P3P:P;P<P5M<]p=WP<g011KR2g011jR4P4g012JR=P5E\p=AP<P2P4P4P=P5g012jFpp=;P;P2P4P4P=P<P5F[p=>P:P2P4P4P=P;P<P5Gsp=Fg00Gbg00J4R>/95R?g00V`R@#w#2#2#2#2#XRA,75'3%2@RB#2#2#2#2#2#b#^RC#MRDP9PC%L5RE,4:#5X29RFg00VARG%0GRH#0RI#v#r#<#<#<#<#<RJ'jRK%D<RL5E9RMC?14:;#5,6CRN91D5X=D%M9ROP6PO18LJRP1IGL,69%N9RQn0100000020000P9PC143E#5X29RRP5C?=1DNX=OP6PPP7P118<5#=1C;<R1[1C<518;<#=[RS18:;#=\11Z<5P5n2001000000120000000X;9X<9PS^;9^<9P5%D;RSPJ1CSJ1B>;R1/7APSP1P5X>81B>5X>8P;P;1@8;DYPJPA1@8AEW1V>;17>;A181;'319;>A181>'3'K1B>:P8p-0R1g013JRT1H8I1H8H1H8G5J85J8g0146'U%RTRH3S%TTRTP81Q8;P<%u8Ct%q8RI%o8RUPUP2P4P4P=1AU3P81P8@R@g014bR21P8BRBC:,;U5>U1AU0P8P@P21O8>R2C:,;U5>UFi%N4R4PUf6,AUP8PBg015IRB1O8ARVC:,;U5>UP4P8P@PBPVC:,;UCFCF1hU=R=P5P;1@671g5;#=dAc8><CdRVb5b8b9X18X:8X01X61W7A185<,3;A185>,3:'K17;ARB,30PB[[^18^:8^01^61^71P519>0190>17>0P0P<P;P3O7b4bEb?CeO3b3CaA167PP6P7P9PC140E#5X29P6POP5%D:,IG,69PQn0100000020000C?143:#5,6CRQ51DXA6P8P;1435#5,6C=1DQXD81@DN%LSPHPT1Q8<PIPUP8P2g0160P@C:,;UR@1AU:5>UP4P@CFP=PVb5b8b9X18X0113?<19><[^18^01P517:AP:P;O3b4,f;EGP9PCPR1IGS,69C?=1DNe18SJP5E`b3PMAkGJLEGP9PCPFPKCl=ECLP9PCPFPLPKD_EG%m;=ECL14;<#5,6C51DeW@XB8WCo"). Qed.

Definition coarse_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a0 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a4 a6 (pc' : Z),
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 a0 a1 a2 (Z_to_bv 64 CTX) a4 (Z_to_bv 64 sc') a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc') fc None m (seg_rom asegs)
    /\ match active st sc' with
       | Some g => a6 = pw st (Some g) /\ pc' = 0x16fa8
       | None => pc' = 0x16f18
       end.

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "h07__arithh14__ffh28__varmaph35__with41yp;1p;2p;4p;7p;3g00OYj10Tg00XFj1ATg00`Fj13Tg00aFj12Tg00bDj1@Tg00c@j1:Tg00c^j14Tg00eWj21Tg00dlj45Tg00n0j76Tg00f^j27Tg00FGj28Tg00g@j29Tg00N`j3?Tg00glj3>Tg00hKj4;Tg00WEj2<Tg016Wj3=Tg00H^R0f0R1g00V`#0#0#0#0#0#0#AR2g013JR3#3%23%@0%:0%40R3g011Kg011jR4P4g012JR4P0g00J4R5,10g01601102C5g012jF61734P1f2R4g00JRR3g00o\R6'81914=?36df19>05C;b1b2b31<52P1b03=W4o"). Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "p'0h01Hh11zh22H1h37__arithh44__ffh58__varmaph65__with74__x1h84__x2h94__x3h:1xi001xh;2H0h<2H2h=2H3h>2H4h?2H5h@6__sat0hA6__sat1hB1bhC1khD5lemmap;1p;2p;3p;7p;4p;6p;8g00OYj1wTg00XFj1NTg017:j2\Tg017Wj20Tg0187j1JTg018UR0j2ITg018nj1GTg019Lj3VTg01:>j7STg01;9j1PTg01;\j23Tg01<9j26Tg01<Vj2qTg01=Gj2iTg01>8j2aTg01>Yj1`Tg01?2j2LTg01?Oj2]Tg00Xdj25Tg00Y@j2BTg01@6j2YTg00WEj2FTg01@]j2XTg01ACj2WTg01Aij2UTg01Bhj2TTg00FGj2ATg01CIj1RTg01Cgj2QTg00UCj1DTg00^Hj2;Tg01DHj3CTg00_1j38Tg00_Zj2HTg00`Fj1OTg00`fj3ETg00aFj1vTg00afj2MTg00bbj4uTg00c@j1tTg00c^j1sTg00eWj2=Tg01E1j6pTg00Dmj1kTg00dIj2@Tg01EUj3jTg00Waj1hTg01F8j3eTg00f^j2bTg00g@j2cTg00glj3dTg00hKj4_Tg01F[j4fTg01G5j2gTg0080j6:Tg01GUj2^Tg01H7j4lTg01HRj1mTg01I0j2nTg00bDj1oTg00dlj4KTg016Wj3[Tg00N`j3<Tg00n0j7ZTg00o8j8rTg00H^R1f0R2g00J4R33<p=2g00JRR4g00o\R57<2p=?f1R6=<12p=41F32p=1P1P6g014bP2CKp=9P6g011KR7g011jR8P8g012JR9P2g012jFZp=7f3R:P7P8P8P9f2R;P6P2Grp=>P1g00V`R<#wR=#NR>%N<R?'\,02%22R@%J6#?RA'IX11%J2#?%G2RB'Ip-0RCP0g01IN9VC0106>#2RCPA%G6RAP2FSWD%P2102>#2R0PA[PC\BP113>2RC,4;XB1RA166>1q6>%16%1>RD10:>#1[[1i;>%1;f4RE/6>RF#1\D[1a:>%2>RD#`13>F10E>'L,4E[1]E>153>RFf5RG/0>RH#115H>'B[1YG>15>3f6RH/0>RI,5>1FI3'B[1XH>f7RH/6>#2\D1WH>f8RI/0>/4I\Dg01J@1UI>RIePIPEg01J\1T3>'APFeO1f9RF/0>RI#115I>'Bg013JRI%R<,Q1RJg00VARK#DRL#D,;1RM5C11;1LRL9C1J1;1KRK581581g0146RJ'HA81LK981M/HJ%OIRJ5EI3E%vIRIP11M1;P61M1:Cu%t1RM%s1RKPKPKP7P8P8P91=1>R71=13RL'9,7KEp%k8R81@1<RN1@1=9j17R7%h<,@1R<5e1'9,7KC>P8PK19<L,7KP819N7,7KC>C>1bK9R9P2P;1A451c2;#?dAd136C_R5b4b5b6X71X81X91g01KB\D13>;/L:,46[%2:13>:,4;[[^71^81^91P2f;R:/0>16:>P:PHf:O5b3b216F>,3>,4Feb?b>b=b<b2b;b@bACfX00g01K_P1PA10;>#2P214ECP113>6REP0X:1P1136>RCP0X11P1P3P@X111A1310C>1g6>E:PE1^>6E:PGP2E:W0XC1P6P2O2n2001000000120100000X0BClO2%m?,n2PJPI%o1PMP1PLg01601=1?CK,7KP9P5b4b5b6%1?P2b39[2?E:X:1o"). Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
Hypothesis MR : mrep st1 m1.
Hypothesis MI : mem_inv asegs m1.

Ltac fin_coarse pc :=
  apply evt_done; unfold coarse_post; do 4 eexists; exists pc; split; [reflexivity|].

End COARSE.

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "p;2p;3g00FGj21Tg00N`j30Tg00JRR0g00o\R1'1g01L9=001do"). Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "h04__x1h11mh21nh32H0h41Xh57__arithh64__ffh74__p1h88__varmaph95__with:1bh;2sch<1Eh=1Hp;1p;2p;3p;4p;7p;6p;8g00OYj14Tg00XFj1@Tg00WEj25Tg00Xdj2:Tg00Y@R0j2?Tg0187j1;Tg01M<j23Tg00DPj28Tg01MYj22Tg00?_j16Tg01N7j11Tg01O5j29Tg01ORj27Tg00Waj1]Tg00`Fj1XTg00aFj1WTg00bDj1VTg00c@j1UTg00c^j1TTg00eWj2>Tg00f^j2QTg00FGj2PTg00g@j2OTg00glj3NTg00hKj4MTg00afj2LTg00dIj2KTg00dlj4ATg00Dmj1JTg01F8j3ITg01?2j2HTg01Ooj7RTg01Q6j2GTg00mLj6STg00ihj4ETg00N`j3DTg0080j6FTg01QVj2^Tg00jbj6\Tg00n0j7[Tg00nTj7ZTg00o8j8YTg00JRR1f0R2g00o\R33Dp=0g00H^R4f1R5g0160P2CAp=CP5g011KR6g011jR7P7g012JR8P2g012jF[p=<f2R9P6P7P7P8P5P2FZp==f3R:P6P7P7P8P9P5P2GYp=Bg00V`R;#4#4R<#@R=/52R>%4<#4#4#@R<,:2R?'?R@%;5#013=2182<'2%;2'2#6%12%@;RA,92#1'3'7X;4RBg00J4RC%];#4#4#4#4#@RDP9g01R6g013JRE#XRF%WERE%V4%U4RG%T4RH1>4CRI/CI'<1QH8RJP2P91P131O29#0dAN4C5CMRKb6b8b915CCP2b5PFPE1L45RLPGPH1>4=1K4;R;'C,<HRMP4P;g015IRN1>4<CA,<HRO5=H%J7RP1CI;,<HP4P;PN1>4D9I4ICA,<H5=HCBPJPKb6b8b9X0415C51HCD,:5'?\@^04P2P:P9O2b5FRPBP9O1#0P113=:RBP3P01352#01595R@[RD15521395#0RC[RI13:9#0\@1G52R@P2n2001000000120000000X14X24PI^14^24P2P=f4RNp-0R;PFPEPLPGPHPHP6P7P7P8P:ESR89=HMPPPMCBPJPKb6b8b9X04W71?>515=5[^04^7;P2f5R>/:<P>PNO3b5O3b3CEAD13BP113=N18><RB,22%;>'2#6%1>19>A#1'3'7#0X:1P5P3P2EF18N<,23%;N'2#6%1N19NA#1'3'7#0P1PBP3P01852#01:95RN[1:521895#0[RM18:9#0\N1^52P2n2001000000120000000X14X24PM^14^24P2f6RMP<PFPEPLPGPHA=H8OPPPOCBPJPKb6b8b9X04X7;1?5?1:5<[^04^7;P2f7R;,5=P;PMO3b5O3b3CEAD13BP118M<1232%;;R<'2#6%1;19;A#1'3R;'7#0X:1P5P3P2EF1233RB%;M'2#6%1M19MA#1'3'7#0P1P<12B2#6f8R<#119<A#1'3'7#0X:1P2P3P>E\12B3#6/7;#0P0PDPI15:9\CP@P5n2001000000120000000X14X24PD^14^24P2f9R2#1192A#1P5O3b3b4b4b3b4b3b4W<W=X;4o"). Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "p;2p;3g00FGj21Tg00N`j30Tg00JRR0g00o\R1'1g01S>=001do"). Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "h04__x1h11mh21nh37__arithh44__ffh58__varmaph65__with72H0h81Xh92X1h:2X2h;2sch<1Hp;2p;1p;4p;3p;7p;8g00WEj22Tg00Waj1VTg00OYj18Tg00XFj1<Tg00Xdj23Tg00Y@R0j26Tg01O5j21Tg01M<j24Tg00DPj25Tg01MYj2BTg00`Fj1ATg00aFj1?Tg00bDj1>Tg00c@j1UTg00c^j1TTg00eWj2=Tg00dlj49Tg00f^j2LTg00FGj2JTg00g@j2ITg00glj3ETg00hKj4DTg00afj2FTg00dIj2CTg00Dmj1GTg01F8j3HTg01?2j2KTg01Ooj7@Tg01TGj3MTg01Q6j2NTg01QVj2OTg00n0j7PTg00N`j3QTg00nTj7RTg00o8j8STf1R1g011KR2g011jR3P3g012JR4f0R5g012jFPp=7g00JRR6g00o\R77Q5p=0f2R8P2P3P3P4P1P5FRp=;f3R9P2P3P3P4P8P1P5GSp=:g00H^R2g00J4R:/25g00V`R;#V#8#8#8#8#<R<,35R='6R>%<;R?,15R@,4:15@<'BX;2R@P:P<P1g01Tjg013JRA#ARB%?ARA%>2%U2RC%T2RDP21=2:REg0160RFPEC9'71LD4R4P5P81J671I58#0dAE2:1CDR7b4b5b612::P5b3PBPA1F21R6PCPDP2PEPF1C2;R;C9,7DRFP2P;g015IRG1=2<RHC9,7DRI5;DRJ%G3R3P2P;PGAH2EHC9,7D9;DFC:P4P7b4b5b6X0212:1RH1K:<,31'6\>^02P5P8P1O2b3F@P@P1O1#0118?R@,4:R>15@<R@;M5%0>%0@'6P0119?R@,4:#015@<#0f4/1?R@,2:13@<'6P5f5/1?,4:#0f6/1?/5<#0P01415#01281[R@12151481#0R>[1298\>1N15P1n2001000000120000000X12X22P@^12^22P5P:f8/1?R@P8O312:@P01515#01381[R013151581#0R@[1398\@1O15P1n2001000000120000000X12X22P0^12^22P5f:/1?R0P<P9O3130<PBPAP6PCPDPIP3PDPFP3PJC:C:P4P7b4b5b6X0212:8138<'6\H\=^02P5f</1?P1P9O3b3b:b7b9b7W:W9P1P5O2n2001000000121000000b8b8W<W;o"). Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_small ()) ["AC_1"] "p'0h01Eh11mh21nh32E1h42E2h52H0h61bi001bh72E3h82E4h92E5h:1Hh;1ai011ah<1oi021oh=2sch>2sti031xp;1p;2p;4p;5p;3g00Waj1^Tg00OYj1@Tg00XFj1BTg00Xdj24Tg00;Sj26Tg01M<j22Tg00DPj23Tg0187j1ATg00Q_j21Tg01O5j25Tg008Nj2XTg01V8j1VTg01CIj1UTg00CNj4TTg0022j5GTg00<Mj2FTg00=Mj1ETg01VTj1DTg01?2j27Tg00WEj2?Tg00FGj2JTg01WOj3NTg00N`j3<Tg01MYj2ITg01TGj3MTg01Q6j2STg01QVj2RTg00Y@R0j2;Tg01H7j4PTg01Wij3\Tg00:Qj2WTg00?Bj2OTg00?_j1YTg00]nj2ZTf2R1f1R2'?f0R3';p=]1O23#Yp=91I12/I3p=:g00J4R4,O3p=81O34,I2p=Cg00JRR5g00o\R67<3p=0g00H^R7f7R8f6R93<f5R:f4R;5<7f3R</?1/;2/;3';'Zp=>A<723p=KA<7;<1;12/;3';p=Q1212/I3p=HA<536,;2p=L%A3=<56p==A<712/;3p=[g00Gbg00V`R6#^R=#@R>#@R?#@#@#B,439]431612g00I<g008nR4g002iR@P4P@P7P3P;P5P7%@6#@RA#BRB/2<%@A#@#@#BRA,3<%B>R>,9<3:%A<RC11;<#83:RDP5P7P4P@P7%B6RE,5<RF,6;P5P7g01XCRG/X7RHPH%VHRIPGP7g01Xa%U6CTR615;ERG,6:DG,F:RJ#E#8%DJ'C11:GRJ%B=R='7PJn010000002000011;F/7=n10110300021010100%B?R?'2PFP<n0100000020000P<n0100000020000n10110300021010100RJP<PJPFPBP<14<A%0CG>P31K;;P;PG1?B;14;A%A;RG#0DQ1J7;3NX;@P3O112B1131A191>3:%A111<1#83:P51J53A<5D3P513:A9HB:19:>%A:RD3:RC119:#8RF'I=<53P5P7P2P5P7P4P@P7159ERJ,68P5P7f8RKPHPHPIP6158ERL,6KRMDG'FRN#E#8%DN'C11KLRN/7=ROPNn0100000020000118J/7=n10110300021010100/2?PJP9n0100000020000P9n0100000020000RNP9PNPJPBP9149A%A9RJ#0G>]0P212B;13;A19;>3:11:;#87:GRG#0AMCF3%0C/LFP0139A9HB9199>;:J#01189#8#0P5P7P4P@P7PMP5P7f9RMPHPHPIP615KER9,6MDG'FRJ#E#8%DJ'C11M9R9/7=P9n0100000020000POn10110300021010100/2?PLP8n0100000020000ROP8POPLPBP8148A%=8G>P313KA9HBK19K>%AK3:#0f:RK/1M#8#012BK13KA19K>3:RM%AKRK;M2%0M/LKP0f;RK,2B13KA19K>3:#0%=KP5P7P4P@P7f=RKf<RM/5ER8'6P5P7f>RLPHPHPIP615KERO,6LDG'FR9#E#8%D9'C11LORO/7=POn010000002000011K8/7=n10110300021010100/2?P8PMn0100000020000ROPMPOP8PBPM14MA%=MG>P312BK13KA19K>3:#0%=Lf?RL13LA5HBRK19L>RM;M2%0K/LMP0f@RM13MA5HB#019M>#0P5P7P4P@P7fBRMfARK/5ER8'6P5P7fCROPHPHPIP615MER9,6ODG'FRJ#E#8%DJ'C11O9R9/7=P9n010000002000011M8/7=n10110300021010100/2?P8PKn0100000020000R9PKP9P8PBPK14KA%=KG>P313MA9HBM#019O>#0fDRO,2BR>13OARO;M2%0>/LOP0fERO,2B#013OA#0P5P7P4P@P7fGROfFR>/5ERM'6P5P7fHRKPHPHPIP615OER8,6KDG'FR9#E#8%D9'C11K8R8/7=P8n010000002000011OM/7=n10110300021010100/2?PMP>n0100000020000R8P>P8PMPBP>14>A%=>G>P312BO#013KA#0P01223#01?12[RK1?231212#0RO[1?<1\O1S23P2n2001000000120000000X17X27PK^17^27P3PBfJRKP1O31?BKP01323#01412[R014231312#0RK[14<1\K1R23P2n2001000000120000000X17X27P0^17^27P3fLR0PAP<O3140AP4P@P7fNR@fMR4/5ER0'6P5P7fORKPHPHPIP615@ER6,6KDG'FRI#E#8%DI'C11K6RI/7=PIn010000002000011@0/7=n10110300021010100/2?R?P5P5P5P7P315KER=PKn0100000020000RIPKPIP=PBPK14KA%=KG>P31K6@1K66RK1?B@R=14@ARI';RH%=@RO';R>';PKP>1J76PHPOP=PIP<P2CPPLCPCP3\1K@@A[@6>1J7@3Nn0110000020000b6P5P7P?P0P4n0100000020000R?P4P?P0PBP4144A%=4G>eb4b5b3b5W4W3P2P3O2n2001000010121000000b0W7W0P2P3O2n2001000010121000000b0W8W0P2P3O2n2001000010121000000b0W9W0P2P3O2n2001000010121000000b0W0g01Y?9<5G1K::P:15:E1?B:14:A%0DDQ1J7:3NW0n0110001020100P3O1b0b6n10110201021010101b<1W12R1P2P1152EPBP2142A%=2G>eW:X=7W>o"). Qed.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End SMALL.

End AC_1.
