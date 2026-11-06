(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
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
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Malloc_fp () := "C35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I35stdpp4gmap4gmap00C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<conc_region'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree;pres_exceptC13~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le2C13~~~C47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_A:pres_writeC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe?enframe_off_memC13~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init9Datatypes3fstK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe@enframe_tail_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapK47Corelib4Init9Datatypes6option01C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6lowbitC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init9Datatypes9andb_propC47Corelib4Init5Logic7and_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3ltbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5clz32C13~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=size_to_classC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval02C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp;grp_hdr_covC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp9unk_agreeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~K47Corelib4Init5Logic2ex01C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C47Corelib7Classes?RelationClasses;reflexivityC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp4mrel01C13~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N;le_preorderi99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp4mrel00C13~~~C47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegI47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing5PExpr06c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp>round_up_pg_eqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_set_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframeEget_meta_rec_upd_sameC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.
(* [comment removed for export] *)
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma conc_b : B = r_base r + snd b.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"; "ENFRAME"] "p;4p;1p;3p;2p-1R0p10000R1p4p710p8P0P1p4p7210R0p8p1000Dp4p70R2p1001Rp4p710R3p8P2p10020R4p4p710R5p8P2P4p4p7210R4p8P2p1002IR6p4p710p8P2P6p4p741110R6p8P2p1002bp4p73110R7p8P2P0p8P2P1p4p73110R1p8p10034p4p70R2P6p8P2P0p8P2P1p8P3P5p8P3P4p8p1004Bp4p710R1P3p8P1P5p8P1P4p8P1P7p8p1004Vp4p7210p10053p4p710p8g005Qj44Tg006kj13Tg008;j30Tg008Xj21Tg0095j32Tp,3st2p,1bR7p,1rR1p,2HrC4g009OR4p,1B%31g009m?047'132eo"). Qed.

Lemma sk_nonneg : 0 <= stride * k.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"; "ENFRAME"] "h07__sat34h14__x1h21Hh32H0h42Hah57__arithh64__ffh77__sat32h87__sat33h98__varmaph:5__with;1ah<5heq_Bh=6heq_P0h>:heq_stridep;1p;2p;3p;4p;7p;8g00:Kj11Tg00;0j15Tg008Xj27Tg00;Nj2<Tg00;kj22Tg0095j34Tg00<Ej2LTg00=Sj1ETg00>gj13Tg00?Lj2BTg00@4j26Tg00@Pj2>Tg00@mj3TTg00AQj2STg00BBj2RTg00B_R0j2OTg00C:j2NTg00C[j1MTg00D;j1KTg00D[j2HTg00E9j1GTg00EWj1DTg00FBj28Tg00Fej2FTg00GHj49Tg00H3j1CTg00HUj2ITg00I7j2JTg00Icj3ATg00JBj4@Tg00K4j2=Tg00KPj4?Tg00L;j7PTg00L_j8QTg00MCR1f0R2'=p=0f1R3g00MaR4g00N@R5P5g00N`R6P2g00O@FPp=:f3R7P4P5P5P6f2R4P3P2GQp=;p,6strideR8p,1kR9g009OR:p,1BR;g00O`R<#1R=#1#1#1R>#5R?'71<89R@'7RA'2p,2P0=4:ARAeRBPAp,3st2p,1b'LRC,2:A4:;CRCeR;PCp,2mr#ERD,2:A4:8DRDeREPD%5=R=%3<#3#3#3#5RF'BRG161=RH%0F1>=FRI,61[RJ[RK%0=RLg00PERMAT=F3UW4RF%0I\M^4LRLp,3off,<?,7@R@/S?RM%0@%0?1R@?#0[[R@p,2K0RI%09RN%1>#5,69R>'OROP0PNP>%08P2f7g00Pa1N1='2PHeO1RHPJg00QGR=#MRP%K=R=1H:3RQ%G:RR%D:RSP:18:?g00R3RT1F:<R<C9,:S%C5R5P:18:1PTP<C9,:SR<C;1IS6R6P2P4g00RZRTg00S:RU'21J24=4TUdAA:13C@R1b6b9b:X1:1=?2%03R?[^1:P2P8p,3S16O2b5b0X3>X2NP3P2O2n2001000000120000000b;b7b8b0b>b<b=PBPAP;PCPEPDPGPKPFPLPMP@PIPOP0PNP>PNP2PHPJPPP=PQPRPSP<P5P<C;P6P1b6b9b:X1:%02P?[^1:P2P9P7O2b5b0X3>X2NP3P2O2n2001000000120000000b;b7b8b0b>b<b=C?o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  pres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  pres_except C m0 (enframe_tail_mem (enframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "p'0h06__sat6h14__x1h24__x2h34__x3h44__x4h57__arithh66__sat5h74__ffh88__varmaph95__with:4__x5h;1xi001xh<7heq_rsvh=1ni011nh>2H0h?4__x6h@2HGhA1whB1bi021bhC1HhD2H1hE2HahF1yhG1BhH1ChI3FIThJ2HChK2HEhL2HFhM2HOhN2HPhO2L2hP2L4hQ2N0hR4OFF0hS2P0hT2P4hU2PShV2R2hW2b0hX1ei031ehY1khZ1mh[2m0h\2m4i042m4h]2mEh^2mFh_2mGh`2mgha2n0hb3offhc1ri051rhd2r2he3rsvhf6stridei061oi071pi082r'i091zp%0p&0p;3p;1p;2p;4p;9p;6p;7p;8p;<p;Bg00SZj39Tg00:Kj1BTg00;0j1ITg00;Nj2HTg008XR0j20Tg00K4R1j22Tg00@Pk20WTg00U4j21Tg00@4R2j25Tg00UQk10CTg00Uok10>Tg00VRj1]Tg00;kj2qTg00W1j1pTg00X:j2DTg0095j3nTg00XZj1vTg00Ycj2mTg00Z@k10XTg00Zbj1ZTg00>gj1lTg00C[k108Tg00?Lk20VTg00@mk30STg00C:k20PTg00D;k10NTg00E9k10JTg00EWk10GTg00Fej2aTg00H3k10DTg00FBk20BTg00HUk20`Tg00I7k20_Tg00Ick30^Tg00JBk40]Tg00\2R3j1FTg00\Rj1~Tg00]0k40\Tg00]Sk20=Tg00^<k30<Tg00^ek20;Tg00_Nk10ZTg00_lk30YTg00`Oj3|Tg00a2l9STg00bLk207Tg00c8j3yTg00BBk206Tg00d\k20UTg00e>S00k20RTg00eak10QTg00f:k10OTg00fXk20MTg00g9k304Tg00gbk60LTg00hFS01k20KTg00hfj2sTg00iCk20ITg00ieS02k30HTg00jIj3hTg008;j3iTg00B_S03j2ATg00jfk402Tg00kAj2dTg00k_j2kTg00l?k60FTg00mdk10:Tg00nlk305Tg0100k10ETg011@j3wTg00D[k20TTg00GHj4bTg00L;j7fTg011`k30iTg00L_j8oTg012Cm<0hTg012hmB0gTg013Nm<0@Tg0143k301Tg014\k200Tg015Hk40fTg015fk30?Tg016Ik40dTg0053k60cTg0174k60aTg017]k40bTg018Dk70ATg018hk40eTg00MCR4f0R5'2p=Uf2R6f1R7'0/25p=61067/15p=71267/A5p=g&0:7>0565p=?&0E7=w65p=E1H75,06p=Gg009OR800T5p=e20B85p=_P6g00MaR9g00N@R:P:g00N`R;P8P7g00R3R<P5Cbg00O@R=Ffp=:B0i875p=4P8P7P<P5Cbp=^f4R>P9P:P:P;f3R?P6P7P9P:P:P;P5P=FfGop=K1175,24p=V1q85p=3g019HR@P8P8P8P3P3f5R3P>P?P6P7P5N<0hp=}P8P8P8P8P8P8P0P5P7P6P0P?P>P3f6R0f7RAf8RBf9RCNB0gp=<P8P8P1PAP1P0P3P>P?P6P7P5N<0@p=R20;85p=\B01875p=Cg00QGR1g019gRD-007;w5p>0[P8P6P7P5H0fp=[B0?875p=;P0P9P:P:P;P3P>P?P9P:P:P;P6P7P5GoGop=8123>12?6P7P5H0dp=PP@P>P?P6P7P5J0cp=c12>?1075,56'Ap=@1075,56,A?p==P8P8P2PAP2P0P3P>P?P6P7P5N<0@p=QP0P3P>15?6%~7P5J0ap=O1A>?P6P7P5H0bp=NP6P9P:P:P;P8P7g01:SP5CbP=Ffp=JP?P9P:P:P;P6P9P:P:P;P7P=FfP5K0Ap={P?P9P:P:P;P6P7P5Gop>09PAP9P:P:P;P0P9P:P:P;P3P9P:P:P;P8P>P<P?CbP=FfP6K0AP7P5Gop=TB01875000Dp=zAw175p=uB01867000D=w15p=MP8B0?867P<P5Cbp=`1167/15p=>1167$0:>05?5p=XAn854p=tAn875p=LP8P7g01;:P5Cbp=jP7P9P:P:P;P5P=Ffp=r1575,A6p=xP6P8P7P5H0ep=Y12461275'Ap=W1275,A6p>03p-0\8g01;aS04Q04A9BA0%U>R=g00O`S05#BR<#BRD#BS06#BR2#IRE/H0S07/03%IDRF;6A12FCf:S08%I<RG%B2#BR2#IRH+0WRI76Cf<RJ/1Ff;RK=7JF,557g5f@RLP7O1[^;8&0C2R2$0>RMg01=3RN#]RO#]RP,q@WAQ06$0C$0>RQ%p5'D=n@P^AM%]PRR#]RS,q@XAM%v5,DQ=n@S^AM1mJ4g00RZRTPTfCRUfBRVPT&0XQ\MRMP5fARW11LGRXf>RY#Z#p5?WQ05#lS09#IRZ,1LS0:Q09#lS0;#B#B#B#B#B#I&08QR[5EQR\3?AGLEYS0</1FS0=AEQ4[R]3?n010000002000039P5PCPVPWf?R^/1GR_f=R`#ZRa#pRb5?LRc11^ZRd;?\AG^E`S0>/1FReP]PVPWPcPdP\PVPWPLP_PbPC20VGHRc154GRf%UH154I[Rg[Rh%UGRig00PERjB0SGH7UWERH%UI\j^EiRiP7g00Pa20P4G'qPfeO1RfPg&081Rj&0N1R1%e7S0?&0J8Rk&0G8Rl%_FRmQ05,a8Rn5:lS0@&0D:RoPl20B84Rp%_GRq,4nRr'^DK20`l;RsP5P6g00S:Rt,qT20_56=nTtdB0^847H0]Rtb7b8b9X1812F5S0A1V7G[^18P5PUPCO2S0Bb5b0b6b0PP%F5S0C=6XIX=@%FPRu,0_RvPI10_GRwPIP5X;8Rx1275#~XF8X;8S0DPvPwPxPxPxP8P8g01=R1075H0\#3XZ8X=8RwP_P_%3_PuPGPxPxQ0C#3X;@S0EPPPG%3GE}S0FM:<PIPI%3IS0GGRPcPhPHPiPfPg%\SS0H%\RS0I%\PRR20=8E%\OS0J60<820;8NRN'CS0K'CS0L'C'CS0M00[jS0NP1%e>S0O&0Z8S0P7[6R_%e?7[7S0QPkPl1a8DRD,;nB0Y8q2R25:lS0RPoPl%_ES0S1a8<Rv5|8S0TQ09,a8Ry';/;m=:lDS0UPoPlA:lpyS0VPoPlA:lpvS0WPo1;rqRz=:l2F8F8PsPtb7b8b9X18X28X38X48A65?IR{1HE6S0X/0??6F>R|11>G?6GI\=\=[[^18^28^38^48P5PVPLPWPUPBQ08PKPJO8S0Yb5b0b6b0EP1DQbS0ZP6PaO1S0[DcPP11WGRaP5P5Pa%F7S0\D@fERbP7O1S0][^;8X=@PXP5P5PXPuD@P3P712a7RX10auR},57R~PXP7PaPGC=S0^PXP~PXP7PxPGO1S0_,0aR~PXPx1575#~XF8X;8S0`P7P7%37S0aP}P~PxPxPxPwPaPa%3aPuQ0_Q0FM:<GQFOP5DNQ0^PcPhPHPiPfPgQ0NP1%e3Q0P7[?S0^9[_7R_PkPlPlPlPrPvAJlvzPoPlQ0S=|8DS0b%l<S0c,a8R<';/;mS0d=:lyPoPlA:lp<S0ePoPlA:lpDS0fPoPlPl14nm/^v1;ny/4mS0g9JlvC{F8S0hH09S0iGTPsPtb7b8b9X18X28X38X48X:8115GRzP7P7PzPGD@1HE>S0j/03?6F?%U0Rz11>FA7>0F,537g3\z[[S0k[^18^28^38^48^:8P5PUfDRrPbP0fFRaP>P`PYP^O9S0lb5b0b6b0b>O2UX;8Q0ZQ0[DcM9SPcPhPHPiPfPgPjP1Q0?PkPlQ0@PoPl%_ZS0?,4nS0[,^pDKPsPtb7b8b9X18Q0A1V7Z[^18Q0Bb5b0b6b0%FOR~,0dS0BPIQ05#IR},0dRXPIPxQ0DQ0BPXPxPxPxPwPdPd%3dP~P}PxPxQ0EPOP}%3}E}ROM:<PIPIQ0GGRPcPhPHPiPfPgQ0NP1Q0QPkPlQ0RPoPlQ0UPoPlQ0VPoPlQ0WPoQ0[%_}RX';S0B=:l2F8F8PsPtb7b8b9X18X28X38X4811>Z?6}I\=\=\|\{^18^28^38^48Q0Yb5b0b6b0EP1DQ\#FS0Y=6dIeQ0:/25S0ZP5Q0:P~C=P3P711WZRd/27S0m10d~S0n,57R\Q0mP7PdP}C=S0oQ0mP\Q0mP7PxP}O1R\,0dS0pQ0mPxQ0`P7P7Q0aQ0nQ0pPxPxPxPwPdPd%3dP~P\POM:<GQFOP5DNQ0oPcPhPHPiPfPgQ0NP1P_PkPlPlPlQ0[PvQ0B9JlvPoQ0iGTPsPtb7b8b9X18X28X38X48X:8115ZRdP7P7PdP}D@Q0k[^18^28^38^48^:8Q0lb5b0b6b0b>O2UX;8Q0ZP5Q0:Q0YC=PrP7O1S0Y[^;8eM9SPcPhPHPiPfPg1CRNS0:1zNR+07/ujS0ZP1%e6Q0P7[7S0BPkPlQ0@PoPlQ0WPoQ0T,;nS0[/4mRd9:lpF8PsPtb7b8b9X18X28Q0A%U6S0o1HE?S0p,06S0n/VF[[^18^28P5PWPUPCPJO4b5b0b6b010e~S0mPI10e}S0qPIPxQ0DQ0mQ0qPxPxPxPwPePe%3eP~P}POM:<PIPIQ0GGRPcPhPHPiPfPgQ0IQ0J/CNS0J,CRS0q;MjS0mP1Q0QPkPlQ0RPoPlQ0UPoPlQ0VPoPlA`dX2DKF8PsPtb7b8b9X18X28X38X48Q0j,0?S0r/1F?6}I\=\|\{^18^28^38^48P5PVPLPWPUPBQ08PKO7b5b0b6b0EP1DQ]#FS0s=6eIeQ0=/25S0tP5Q0=P~C=P3P7AGWE^Re/1FRd/27S0u10d~S0v,57S0wQ0uP7PdP}C=S0xQ0uQ0wQ0uP710d\S0wQ0uPxQ0`P7P7Q0aQ0vQ0wPxPxPxPwPdPd%3dP~P\POM:<GQFOP5DNQ0xPcPhPHPiPfPgQ0H/CNS0x%]SS0w#]S0v#\S0uQ06#I-0=8>0<8R'C,zN+07Q0HQ0IQ0:'C;MjS0:'uP1P_PkPlPlPlQ0b,;nRN/4mRRPv1;RX9JlvPoQ0iGTPsPtb7b8b9X18X28X38X48X:8Q0p,05S0b/1FRRP7P7PRP}D@Q0k[^18^28^38^48^:8Q0lb5b0b6b0b>O2UX;8Q0tP5Q0=Q0sC=Q0Y[^;8eM9Sn0110200020001bBAy^YJ99WLRRePRAyL^`S0YQ0>PGQ0>Q08;>E006ES0=#Z#pCXQ0>PZAEQK[CXS0tPMPUPVAyWLYS0lQ0</1GRRQ0<?>KE006E#ZS06#pS0y3?Q0</1ZRdAEQJ[S0<PUPVQ0lPRQ0yP7PcPhPHPiPfPgQ0ZP1Q0BPkPlQ0@PoPlQ0WPoQ0[/4qS0l9:lpF8PsPtb7b8b9X18X28Q0AQ0oQ0n/VG[[^18^28P5PVPrQ08P`O4S0zb5b0b6b0PP11eGS0{Q0C;6IX=@10RuS0|PI10RGS0}PIPxQ0DQ0|Q0}PxPxPxPwPRPR%3RPuPGQ0FM:<PIPIQ0GGRPcPhPHPiPfPgQ0mP1Q0QPkPlQ0RPoPlQ0UPoPlQ0VPoPlQ0l?`q2DKF8PsPtb7b8b9X18X28X38X48Q0r/1G?6GI\=\|\{^18^28^38^48P5PUPWPVPrPCPKPJO7S0lb5b0b6b0EPQ0y,DQS0yP?Q06O1S06DcPPAGVELS0}/1GRPP5P5PPQ0\D@PaP7O1[^;8X=@Q0{P5P5Q0{PuD@P0P712P7RR10PuS0{,57S0|PRP7PPPGC=S0~PRQ0|PRP7Q0_,0PS0|PRPxQ0`P7P7Q0aQ0{Q0|PxPxPxPwPPPP%3PPuQ0_Q0FM:<GQFOP5DNQ0~PcPhPHPiPfPgQ0w#\S0wQ0KQ0:3MS0:P1P_PkPlPlPl14NqRuPv1;uq9JlvPoQ0iGTPsPtb7b8b9X18X28X38X48X:8Q0b/1GRuP7P7PuPGD@Q0k[^18^28^38^48^:8P5PrPbPaP0fGRGP>PYP^PLO9Rub5b0b6b0b>O2UX;8Q0yQ06DcM9SPcPhPHPiPfPgQ0ZP1Q0BPkPlQ0@PoPlQ0WPoQ0[Q0?'4Rq9:lpF8PsPtb7b8b9X18X28S0[Q0AQ0oQ0n/VZ[[^18^28S0AQ0zb5b0b6b010d~RPPI10d}RRPIPxQ0DPPPRPxPxPxPwPdPd%3dP~P}POM:<PIPIQ0GGRPcPhPHPiPfPgQ0mP1Q0QPkPlQ0RPoPlQ0UPoPlQ0VPoPlA`qX2DKF8PsPtb7b8b9X18X28X38X48S0RQ0r/1Z?6}I\=\|\{^18^28^38^48S0rQ0lb5b0b6b0EPQ0<,DQ#F=6dIe11eZS0</25RdP5Q0<P~C=P0P7Q0}/1ZR{/27R|10{~Rq,57RRP|P7P{P}C=RPP|PRP|P710{\RRP|PxQ0`P7P7Q0aPqPRPxPxPxPwP{P{%3{P~P\POM:<GQFOP5DNPPPcPhPHPiPfPgQ0:P1P_PkPlPlPlQ0?,4NRPPv1;PX9JlvPoQ0iGTPsPtb7b8b9X18X28X38X48X:8S0?Q0b/1ZRPP7P7PPP}D@Q0k[^18^28^38^48^:8S0kPub5b0b6b0b>O2UX;8PdP5Q0<AEQ`[,DQ#FC=Q0][^;8eM9SA9UV5A7WLF?>eYP8PTPM1m54P610VW?>F5=?6]n0100000020000PM20U74%t71m74+0R1m64PTQ00%t?fJRefIRLPTPMP7PAA7GaFRd/13Ru=?A]n010000002000039P7%t>RPP0WXP5O1&0QPPePLPAPuP]P0AGGEb=>drRd#31L3dRdeRPPdPcPhPHPiPfPgQ0NP1P_PkPl1;nvS0N/4mR{/4N/4<,jy,rlS00PoPlQ0@PoPlQ0ePoPlQ0fPo14{yS0e9:lpF8F8PsPtb7b8b9X18X28X38X48X:81057S0]/1FS0:Q0b;>>,L6S0b12F7A7>3F/V0\z\z[[^18^28^38^48^:8P5PLPeQ08fKRRfLRqP>PVPrPbO9b5b0b6b0b<PPPdfHRd/0G?>F0RP/0~R|PI10P}S0aPIPxQ0DP|Q0aPxPxPxPwPPPP%3PP~P}POM:<PIPIQ0GGRPcPhPHPiPfPgQ05$0O-0M8S05Q0I6048S0aQ0q;MjP1P_PkPlQ00PoPlQ0N=:l2S0NPoPlQ0d=:lvPoPlQ0e?`X2DKF8PsPtb7b8b9X18X28X38X48X:8Q0b1076S0e/2I1HE3/00?6F?10?>?>F3?6}I[[[^18^28^38^48^:8P5PLPeQ08PRPqP>PWPUO8b5b0b6b0EPb<Q0s=6uIe12P5S08?x5|P`P7A7LdFS0bAGLEG;>aR|#31LA|R|eS0dP|A7eLFS00/1BRu/26S0q10u~S0},56S0lQ0qP6PuP}C=S0QQ0qQ0lQ0qP610u\S0lQ0qPxQ0`P6P6%36S0qQ0}Q0lPxPxPxPwPuPu%3uP~P\POM:<GQFOP7DNQ0QPcPhPHPiPfPgQ0uQ0xQ0v#]#\Q0wQ0L'C'zRuQ05Q0w6048Q0HQ0I'C;Mj,uu'u3MP1Q0O%e07[6Q0^7[7S0^PkPlPlPlQ0gQ09#B,a8Ru'4S09PvQ09/;X9JlvPoPlQ0g/4N/4<,ju,rlS09PoPlPlP9P:P:P;1jup,rlJ0LPoQ0iF8GTPsPtb7b8b9X18X28X38X48X:8X?8A756FS0i/13R;P7P7P;P}D@A77?FQ0j,07;>3,L0S0j%tAg01>6[Q07/0A?6F3%UBR;110FA70BF,5A7gA\;[[[[[^18^28^38^48^:8^?8P5P`PqfMR;fNR:PAfOR9P>P3PBPaPGPdO<b5b0b6b0b>b<O2UX;8Q08P5PPQ0sC=PqP7O1[^;8eM9SWaP5O1n10210210500021010311101bBbcA9ab5PT20KM8S08Q0c#IRP/s6P7A7rUFRNPF%Z6#vCXPNPPP]CX=YMPAYM76n0100000020000Q0820IP?12P?15?P1sP?40H1sP>PTQ0212P3S02153PPTQ08P7Q0b/1FS0c%ZAS07#vS0O5?0S0xQ0b/1PS0b;?]S0I=YMPS0HAYM0AS05n0100000020000RN9hM899qRAiM8NRN?WNP'AP712P0Q0I99qRAWPPPS0IPqPRQ0xQ0bP]PqPRP0Q0cQ0OP3Q0dP|PcPhPHPiPfPgQ0wQ0M;MjS0wP1P_PkPlQ0S=|8y,;n,4{/4D,j<,rlS0SPoPl%_PRN=:l<S0cPoPlQ0@PoPlQ0fPoPlQ0VPoPl14{mS0x,^pDKF8F8PsPtb7b8b9X18X28X38X48X:8Q0:Q0X,05;>?,L>S0:Q0212F6S0XA730FS0L/VF\z\z[[[^18^28^38^48^:8P5PJPRPqP;P:P>P3PrPaPGO:S0vb5b0b6b0b<PSQ00/1FRrQ0C;6IX=@Q0dP|%FSS0C,0rS0QPI10rFS0lPIPxQ0DQ0QQ0lPxPxPxPwPrPr%3rQ0CPFPxPxQ0EPSPF%3FE}S0EM:<PIPIQ0GGRPcPhPHPiPfPgPjP1Q0BPkPlQ0NPoPlQ0x?`m2DKPsPtb7b8b9X18X28Q0]/2IS0]Q0e/1FS0e/1F?6FI[^18^28P5P;P:PUO3S0xb5b0b6b0EPb<Q0O,DQS0OPKQ07O1S07DcPSA7ReFRS/1FRUP5P5PUQ0\D@P9P7O1[^;8X=@Q0Q,559gr5P^P7AGRELS0Q=>SdRS#31LCSRSeS0\PSA7qRFRC/1FRr/26R@Q0C,0rS0l,56RUP@P6PrPFC=S0}P@PUP@P6PxPFO1S0m,0rRUP@PxQ0`P6P6Q0qQ0lPUPxPxPxPwPrPr%3rQ0CQ0mQ0EM:<GQFOP7DNQ0}PcPhPHPiPfPgQ0uQ0M;MjS0uP1Q0^PkPlPlPlQ0g/4mRrPv1;rm9JlvPoPlQ09PoPlA:lNuPoQ0hF8S0hGTPsPtb7b8b9X18X28X38X48X:8X?8Q0i/1FRuP7P7PuPFD@Q0j12PA%UARu113FA73AF,507g0\u[[[S0j[^18^28^38^48^:8^?8P5P^P:P9fPRrPAfQRUP>P3PBPLPeO;S09b5b0b6b0bDb<O2UX;8Q0OQ07DcM9SQ0dP|PcPhPHPiPfPgQ0wP1P_PkPlQ0SPoPlQ0cPoPlQ0@PoPlQ0fPoPlQ0VPoPl14{NR{,^pDKF8F8PsPtb7b8b9X18X28X38X48X:8Q0:Q02Q0XQ0L/VP\z\z[[[^18^28^38^48^:8Q0vb5b0b6b0b<Q0dP|Q00/1PRz/0~RBPI10z}R@PIPxQ0DPBP@PxPxPxPwPzPz%3zP~P}POM:<PIPIQ0GGRPcPhPHPiPfPgPjP1Q0BPkPlQ0NPoPlA`{X2DKPsPtb7b8b9X18X28Q0]Q0e/1P?6}I[^18^28Q0xb5b0b6b0EPb<Q0bQ0s;6Ie12z5R{?x5BP^P7Q0\PS11CPRC/26RS10C~RB,56R2PSP6PCP}C=R@PSP2PSP610C\R2PSPxQ0`P6P6Q0qPBP2PxPxPxPwPCPC%3CP~P\POM:<GQFOP7DNP@PcPhPHPiPfPgQ0uP1Q0^PkPlPlPlQ0g/4NR@Pv1;@X9JlvPoQ0hGTPsPtb7b8b9X18X28X38X48X:8X?8Q0i/1PRvP7P7PvP}D@Q0j[^18^28^38^48^:8^?8Q09b5b0b6b0bDb<O2UX;8P{P5PzQ0sC=P:P7O1[^;8eM9SQ0dP|PcPhPHPiPfPgPjP1Q0PPkPlPl1^pNA:lNNC{PsPtb7b8b9Q0IP5b5b0b6b0b<H02Q0H9hM899qRQ0H9iM8Rz?WzP'AeWCP5O1150PA9qR0B03uAPP3Q0dP|PcPhPHPiPfPgQ0aQ0J;MjP1P_PkPl1;<D/4mQ0T,;<'4/4y,jn,rlPoPlAJlnNPoPlQ0UPoPlPl1^pnA:lnNC{H09F8PsPtb7b8b9X18X28X38X48X:8A7>?FAG>E7;>6,L5157PQ0p/0>?6F3AW??P[[[^18^28^38^48^:8P5P:P;PRPqPJP>P3PbO8b5b0b6b0b<H02Q059hM899qRQ059iM8Rt?WtP'AeWCP5O1n200210200001021100011000bWbBAhM85Rt99dGAiM85Rs?WsPRs'AQ01PMP8A9eLt/AsQ01PMP8PMP71HEd=7eZQ0;#l#l#IRs,da1k5PRa'0=EQ[5?7n200110000012010410899Re]@P7AYM75Rt9hM899;qAiM8tRt?WtP'AQ03A9:;6AW77P1HEe=7qZ1dds1k6P'0=EQ[5??999:P5A9r9>B03=>PfRR?PUP0AG9E;Rd/1ZRt1dRs1k3P'0=EQ[R3P7A79:F?>dqRd#31L`dRdeRNPdPcPhPHPiPfPgQ0[Q0AP5P?fTRnPeP;O4b5b0b6b0b<PNPd1HE:=7rZRd/0~RNPI10d}RePIPxQ0DPNPePxPxPxPwPdPd%3dP~P}POM:<PIPIQ0GGRPcPhPHPiPfPgQ0RQ0rP5fSPUP?PnPLPRPqO7b5b0b6b0EPb<1DQ3#F=6tIe12d5Rt?x5NPbP7A7UrFAGUE9;>:RU#31L^URUePU1HEr=7?ZR?/26RE10?~RU,56RbPEP6P?P}C=R}PEPbPEP610?\RbPEPxQ0`P6P6Q0qPUPbPxPxPxPwP?P?%3?P~P\POM:<GQFOP7DNP}PcPhPHPiPfPgQ0?Q0kP5PnfUfVPAfWP>P:P9PrO9b5b0b6b0b>b<O2UX;8PtP5Pd1dqs1k0P'0=EQ[,DQ#FC=PnP7O1[^;8eM9SWVW@P7P5O2n2001000000121000000P6Q0QPZ1dGs1k7P'0=EQ[CX99:;eW@Xd8X`MP7P5O2n2001107000121106109P5O1b@b_bLb^bebKb]Q01PMP8PMPTQ08A7^YFR^Q0>;>JRY,sPPTPM1mY4Q0tQ0tP^PYP]CXn0100000020000R4P^PF%ZY#vCXP^PPP]CX=YMPAYM4Yn0100000020101Q0<1d`s/0a=EQ[5?7n200110000012010410899VWeQ0YQ0>P^PJPKQ0=J0F99VWebMbPbOWJWUWTWIXQ=WRWNXG8XY8X=8Xb8Xf8XS8W\W[WHo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma actives_length : forall st, length (actives st) = 48%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h01ih11nh22stp;2p;3p;6p;1p;4g01>Sj2@Tg00X:j23Tg0095j34Tg00;kj2?Tg01>oj2;Tg0053j65Tg00:Kj11Tg00UQj18Tg00Uoj17Tg00\2j16Tg01?Nj29Tg01@^j2:Tg01Anj4>Tg01BJj4=Tg01Bij1<Tg00VRj10Tf0R0#0#0#0#0#0#0#0#0p=2g01D>g019HR1g01=3R2%22#2#2#2#2#2R3'@R4,31R5A4103X11R6P1P3P61?13P51;32E5g00O`#1#1#1#1#1#1#8#7R2P1P2f1R5%60,95':X01R5P4C>'3P1P2P5P4C=E5%<0,32=413eW2o"). Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 -> nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h04__p1h14__x1h21ih31Hh47__arithh54__ffh64__p2h74__p3h88__varmaph95__with:4__x2h;1mh<1nh=1oh>1xh?2H0h@3HschA1bhB2schC2sthD1zhE2z0p;2p;1p;3p;4p;7p;6p;5p;<p;8g00K4j29Tg00>gj1wTg00:Kj12Tg00;0j1XTg00@4R0j27Tg00B_R1j23Tg00UQj1bTg00Uoj1^Tg00Z@j1MTg00\2R2j1LTg01?Nj24Tg01@^j25Tg00VRj10Tg01>Sj2jTg01EPR3j1DTg01F0j3ETg01FNj4?Tg01G2j26Tg0095j31Tg01GTj28Tg01H4j2ITg00H3j1NTg01HKR4j2CTg01Hcj2ZTg01IFj2BTg00;kj2@Tg01Icj2VTg01JEj2KTg00^ej2HTg0143j3JTg014\j2UTg00C[j1RTg011@j3STg00D;j1TTg00D[j2QTg00_Nj1uTg015Hj4tTg00E9j1qTg00EWj1oTg00Fej2PTg00GHj4:Tg00FBj2OTg01J_j7iTg00HUj2hTg00I7j2gTg00Icj3cTg00JBj4dTg016Ij4eTg01KCj4aTg01K_j2fTg0053j6GTg01L=j6`Tg01LYj3kTg01Anj4lTg01M;j5_Tg01Bij1mTg012Cl<nTg013Nl<]Tg01M]j6\Tg00L;j7pTg018Dj7[Tg00L_j8sTf0R5#0#0p=v%05#0#0#0p=r%05#0#0#0#0#0#0#0p=<g00RZR6g00S:R7715p==g009OR8g019HR9P8P8P3f4R3P2f3R:g01NAf2R;f1R<P5M<np=YP9P8P4P2P0g01Nnf5R0P3P:P;P<P5M<]p=WP<g00MaR2g00N@R4P4g00N`R=P5E\p=AP<P2P4P4P=P5g00O@Fpp=;P;P2P4P4P=P<P5F[p=>P:P2P4P4P=P;P<P5Gsp=Fg01D>g00MCR>/95R?g00O`R@#w#2#2#2#2#XRA,75'3%2@RB#2#2#2#2#2#b#^RC#MRDP9PC%L5RE,4:,5:X29RFg01=3RG%0GRH#0RI#v#r#<#<#<#<#<RJ'jRK%D<RL5E9RMC?14:;,5:,6CRN91D5X=D%M9ROP6PO18LJRP1IGL,69%N9RQn0100000020000P9PC143E,53X29RRP5C?=1DNX=OP6PPP7P118<5#=1C;<R1[1C<518;<#=[RS18:;#=\11Z<5P5n2001000000120000000X;9X<9PS^;9^<9P5%D;RSPJ1CSJ1B>;R1/7APSP1P5X>81B>5X>8P;P;1@8;DYPJPA1@8AEW1V>;17>;A181;'319;>A181>'3'K1B>:P8p-0R1g00QGRT1H8I1H8H1H8G5J85J8g019g'U%RTRH3S%TTRTP81Q8;P<%u8Ct%q8RI%o8RUPUP2P4P4P=1AU3P81P8@R@g01;:R21P8BRBC:,;U5>U1AU0P8P@P21O8>R2C:,;U5>UFi%N4R4PUf6,AUP8PBg01:SRB1O8ARVC:,;U5>UP4P8P@PBPVC:,;UCFCF1hU=R=P5P;1@671g5;#=dAc8><CdRVb5b8b9X18X:8X01X61W7A185<,3;A185>,3:'K17;ARB,30PB[[^18^:8^01^61^71P519>0190>17>0P0P<P;P3O7b4bEb?CeO3b3CaA167PP6P7P9PC140E,50X29P6POP5%D:,IG,69PQn0100000020000C?143:,53,6CRQ51DXA6P8P;1435,53,6C=1DQXD81@DN%LSPHPT1Q8<PIPUP8P2g00R3P@C:,;UR@1AU:5>UP4P@CFP=PVb5b8b9X18X0113?<19><[^18^01P517:AP:P;O3b4,f;EGP9PCPR1IGS,69C?=1DNe18SJP5E`b3PMAkGJLEGP9PCPFPKCl=ECLP9PCPFPLPKD_EG%m;=ECL14;<,5;,6C51DeW@XB8WCo"). Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h01Th12Hah26__sat1h34__x1h41Eh51Hh62H0h72Hkh87__arithh94__ffh:6__sat0h;8__varmaph<5__with=1bh>1kh?1vh@1zp;1p;2p;3p;4p;7p;8p;6p;5g01OPj1VTg00:Kj1@Tg00;0j1<Tg00@Pj24Tg0095j36Tg01P`j20Tg00?Lj2>Tg00@4j25Tg00@mj3;Tg00C:j2:Tg00;kj28Tg00C[j1UTg00D;j1TTg00D[j2STg00E9j1KTg00EWj1JTg00FBj2ITg00Fej2CTg00GHj4BTg00L;j7ATg00H3j1?Tg00L_j8DTg00HUj2ETg00I7j2FTg00Icj3GTg00JBj4HTg01QAj2=Tg01Qij13Tg00kAj27Tg0053j6LTg01RFj2MTg01Rdj3NTg01L=j6OTg01SGj3PTg00B_j2QTg01Sjj59Tg00K4j2RTg00MCR0f0R1'Rp=2g00RZR2g00S:R3761p=1g009OR4%21R5f2R6#Vg00O`R7#@#<R8f1R9'4564P41486f3R:,01#1X@41>861508R;%2:f4R<,48,50[[%28R=g00PER>f5R?=;89UW1148?R@#2\>^1=P9g00Pa1:08'8P;eO1%2<150@[g00QGR@#U%T@1S49%K4%J4R@g00MaR;g00N@R8P8g00N`R=P@P;P8P8P=P41I40g00R31C47CBg00O@FAR7%?8P7GD1E@=P1P618231F16#1dAG409CHb9b;b<X34%29\5^34P1f6R5P?O2b8b2b:b2,=6%3:,7:R0P1EL1006#1P2%3<R0,7</0:%11X=2P110<:100:'MR2AN<0:EO%1210?<R2%3?/0<R<;P1%12%1<'Q105?#1R<%35/0?#1P<f7#3/05#1P9W6X5<P1D9b0b0b0W4W7X>4W?o"). Qed.

Lemma size_class_small : forall sc, 0 <= sc < 10 -> size_class sc = sc + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h02H0h11Hh24__x1h32sch41Eh57__arithh64__ffh78__varmaph85__witp;1p;2p;4p;7p;8p;3g00:Kj1>Tg00>gj1@Tg00;0j14Tg00C[j1^Tg00D;j1ZTg00D[j2VTg00E9j1STg00EWj1PTg00FBj2?Tg00Fej2MTg00GHj4<Tg018Dj7]Tg00H3j1[Tg00L_j8TTg00HUj2RTg00;kj2ETg00I7j2QTg0095j32Tg00Icj3OTg00JBj4NTg00K4j2DTg0053j7FTg00@4j2ITg00B_j2GTg00L;j7=Tg01J_j7BTg01JER0j2;Tg01TGj1\Tg008Xj2HTg00MCR1f2R2'Df1R3f0R4'I'Gp=5P3g00MaR5g00N@R6P6g00N`R7P4g00O@R8F=p=Cg009OR9/?4p=JP9P3g01;:R:P4C<p=YP9P3P:1?94C<p=XP2P5P6P6P7P9P3P:P4C<P8F=p=Wf4R;P5P6P6P7f3R<P5P6P6P7P9P2P:1?93C<P8F=P4FBp=:f6R:P5P6P6P7f5R=P5P6P6P7P;P8F=P<P5P6P6P7P2P5P6P6P7P3P8F=P4FBFBp=UA2941p=AA2934p=1A29<2A2934';p=7A29;<A2923/;4';p=01;34,;2p=LA29=;A29<2A2934';';p=9%\21H34529p=31I34,G2p=K1H34,E9p=6P9P=P;P<P2P3P4FFp=8g00O`R8#>R>#@R?#>#4R@9544RAg00QGRB#^%ZB1V93%S9%P9RBP5P6P6P7PBP5P6P6P7P91?91R5g00R31M98RCC<,CBP9PCg01:S%J@C<,CBF]%[6PBPB1YC5PBPB%48R5,XCPBPBPC%4>R6PBPBPC%@8R8#4RDPBPBPC%>>R>#4REPBPBPC%4?R?PBPBPC%>8#4RFPBPBPC%@8#4R8PBPBPC%>>#4RG%@>#4R>#J9WBCD:D:D:D:D:D:D:FUGT1RB7P4P2g00RZRBg00S:R7'E1Q42=2B7dAO913CNb6b7b8X29%A31135P3P6P3PDP3PEP3P?P3PFP3P8P3PGP3P>C7D0D0D03LR7\A^29P4P2P3O2b5P7P0%A2P2P5P2P6P2PDP2PEP2P?P2PFP2P8P2PGP2P>E9D0D0D0A3<<5P4%A<P9P1A3335^1AX39RA1D11?K1@1615W1P;P4P<FFW0P4O1P<P5P<P6P<PDP<PEP<P?P<PFP<P8P<PGP<P>E9D0D0D0P011;5P;P6P;PDP;PEP;P?P;PFP;P8P;PGP;P>C7D0D0D0A3==5P411=5P5PAA555@1655W1P:P4P=E8W0P4O1P=P6P=PDP=PEP=P?P=PFP=P8P=PGP=P>C7D0D0D0P011:6P:PDP:PEP:P?P:PFP:P8P:PGP:P>E9D0D0f7R:?3:5P411:6P6PAA566@1665W1f8R6P4P:E8W0P4O1P:PDP:PEP:P?P:PFP:P8P:PGP:P>E9D0D0P0116DP6PEP6P?P6PFP6P8P6PGP6P>C7D0D0f9R6?365P4116DPDPAA5DD@16D5W1f:RDP4P6E8W0P4O1P6PEP6P?P6PFP6P8P6PGP6P>C7D0D0P011DEPDP?PDPFPDP8PDPGPDP>E9D0f;RD?3D5P411DEPEPAA5EE@16E5W1f<REP4PDE8W0P4O1PDP?PDPFPDP8PDPGPDP>E9D0P011E?PEPFPEP8PEPGPEP>C7D0f=RE?3E5P411E?P?PAA5??@16?5W1f>R?P4PEE8W0P4O1PEPFPEP8PEPGPEP>C7D0P011?FP?P8P?PGP?P>E9f?R??3?5P411?FPFPAA5FF@16F5W1f@RFP4P?E8W0P4O1P?P8P?PGP?P>E9P011F8PFPGPFP>C7fARF?3F5P411F8P8PAA588@1685W1fBR8P4PFE8W0P4O1PFPGPFP>C7P0118G118>fCR8?385P4118GPGPAA5GG@16G5W1fDRGP4P8E8W0P4O1118>P>PAA5>>@16>5W1PGP4P8E8W0P4O1n200100000021000010000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000W0P4O1n200100000021000011000b4W1X39o"). Qed.

Lemma size_to_class_small : forall n, 0 <= n -> Z.shiftr (n + 3) 4 < 10 -> size_to_class n = Z.shiftr (n + 3) 4.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h01Hh11nh24__x1h31mh42Hnh52Hsh67__arithh74__ffh88__varmaph95__with:1bh;1zp;2p;1p;3p;4p;7p;6g00K4j2QTg00>gj1:Tg00;0j13Tg008Xj20Tg00:Kj14Tg01U[j25Tg00@4j29Tg00C[j1ITg00D;j1FTg00D[j2ETg00E9j1DTg00EWj1BTg00Fej2ATg00FBj2;Tg015fj3@Tg011`j3PTg00GHj4OTg00L;j7NTg00HUj2LTg00;kj2=Tg00I7j2JTg00Icj3HTg00JBj4GTg00U4j26Tg0095j32Tg01V;j21Tg01VXj1?Tg00;Nj2<Tg01TGj18Tg01Wgj2KTg01KCj4CTg01L=j6>Tg01XGj1MTg00RZR0f0R1g00S:R232p=7g009OR3g00MCR4/Q1f1R5g00O`R6#:R7#3R8'0%46R9#4R:#3R;'5%:9#4#3R<'9g00QGR=#I%F=1E35%D3%B3R=g00Mag00N@R>P>g00N`R>P31A36R?1;385@3g01;:1;3;9@3?%36R6,;35P3COg00O@FN1L=>P1f2R>1=021J1>#7dAH345CGb7b8b9X231018101;/66523^23P1f3R4O1b610>8R=10>;/66523P31048R?P0P3151;R@/1<P@P0P3P0P3%:7#4#4#3R710@6R@#?'6/<;%4:#3R:'0RA/06#8/1@%39R9,0APAn0100000020000RA#8/1@10A6PAn0100000020000n0100000020001f4/08/5;RA523X;3P015?;/1<R?P2g00B_1151#719>5R@[195111>5#7[RB114>#7\@1K51P1n2001000000120000000X33X13PB^33^13P1PAP<P>O3b0CCA202?P0P2P0P3P1f5/08/5;R8P0P3P0P31086R2#?,67/<;/0:R:/06#8/1210:9P:n0100000020000R:#8/1210:6P:n0100000020000n0100000020001=238X:01=3A11A<P1E>b0104;/66P1E>b0%M>15=;523eW5W4W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grp_hdr_cov (st : mstate) (rid : N) (off : Z) : Prop :=
  exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b <= off < snd b + 12.

(* [comment removed for export] *)
Definition unk_agree (st : mstate) (o m1 : mem) : Prop :=
  forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
    0 <= off < round_up_pg (r_len r) ->
    cell_read (get_shadow st rid) off = Unknown h ->
    ~ grp_hdr_cov st rid off ->
    m1 (wa (r_base r + off)) = o (wa (r_base r + off)).

Lemma unk_agree_refl : forall st m, unk_agree st m m.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h02_Hh13_H0h23_H1h33_H2h43_H3h51hh61mh73offh81rh93ridh:2stp;1p;4p;6p;2p;3g00Z@j12Tg004Bj4ITg002Ij44Tg01Y^j13Tg01[1j6HTg01G2j2<Tg0095j30Tg01[Ej15Tg00K4j26Tg01\Uj17Tg01]dj18Tg00@4j29Tg00B_j2:Tg01_9j2GTg01`Mj2FTg01a`j1?Tg01c3j3=Tg00eaj1>Tg00:Kj11Tg00UQj1;Tg00Uoj1@Tg006kj1ATg008Xj2BTg00mdj1CTg00;kj2DTg01dLj3ETg01D>g01;ag009mR0g01ecR1g009OR2%21P0P1P0g01g5R3g01gNR4P1CIP0P3P4P1C4f3R4f5R3#3EHf2,<130g01gl%54g01i=30g00MC/64f4R1#7#8,94':g01jNf8f6R0'G/F1%?430f9R4f7R1;=3#>g00O`#1#1#1#;#@#2P4%A1/B0#CO1'DW4W3W2W1W0X52W7W8W9f1f0R2;E2eW6W:o"). Qed.
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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expo_cond (st : mstate) (n : Z) : Prop := MMAP_THRESHOLD <= n \/ s_regions st = ∅.

Record slot_ok (st1 : mstate) (g b : aptr) (r : region) (idx n : Z) : Prop := mkSO {
  so_mem : m_mem (get_meta_rec st1 g) = Some b;
  so_reg : (s_regions st1) !! (fst b) = Some r;
  so_kind : r_kind r = RKGroup;
  so_b0 : 0 <= snd b;
  so_b16 : snd b mod 16 = 0;
  so_idx : 0 <= idx <= m_last_idx (get_meta_rec st1 g);
  so_li : m_last_idx (get_meta_rec st1 g) < 32;
  so_span : snd b + 16 + get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1) <= round_up_pg (r_len r);
  so_s16 : 16 <= get_stride (get_meta_rec st1 g);
  so_smod : get_stride (get_meta_rec st1 g) mod 16 = 0;
  so_s31 : get_stride (get_meta_rec st1 g) - 4 - n < 2^31;
  so_n : 0 <= n;
  so_fit : n + 4 <= get_stride (get_meta_rec st1 g);
  (* [comment removed for export] *)
  so_nogrp : forall b' gh, (s_groups st1) !! b' = Some gh -> fst b' = fst b ->
     snd b' + 9 <= snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4
     \/ snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 <= snd b';
  (* [comment removed for export] *)
  so_hdr0 : cell_read (get_shadow st1 (fst b)) (snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4) = Known 0;
  (* [comment removed for export] *)
  so_q16 : forall off, 0 <= off -> 16 * off + n + 4 <= get_stride (get_meta_rec st1 g) ->
     (get_stride (get_meta_rec st1 g) * idx + 16 * off) / 16 < 65536;
  (* [comment removed for export] *)
  so_slot : (s_slots st1) !! (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx) = Some (g, idx);
  so_mslot : meta_slot st1 g;
  so_avail : 0 <= m_avail (get_meta_rec st1 g) < 2^32;
  so_freed : 0 <= m_freed (get_meta_rec st1 g) < 2^32;
  so_freeable : 0 <= m_freeable (get_meta_rec st1 g) < 2;
  so_maplen : 0 <= m_maplen (get_meta_rec st1 g) < 2^40;
  so_sc : 0 <= m_sizeclass (get_meta_rec st1 g) < 48
          \/ (m_sizeclass (get_meta_rec st1 g) = 63 /\ m_last_idx (get_meta_rec st1 g) = 0 /\ 0 < m_maplen (get_meta_rec st1 g))
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_slot_addr (st : mstate) (a : Z) : Prop :=
  exists g b r i, m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= i /\
    (Z.testbit (m_avail (get_meta_rec st g)) i = true \/ Z.testbit (m_freed (get_meta_rec st g)) i = true) /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + sstart_of (get_meta_rec st g) i - IB <= a
      < r_base r + sstart_of (get_meta_rec st g) i + get_stride (get_meta_rec st g) - IB.

(* [comment removed for export] *)
Definition grp_hdr_addr (st : mstate) (a : Z) : Prop :=
  exists b gh r, (s_groups st) !! b = Some gh /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + snd b <= a < r_base r + snd b + 16.

(* [comment removed for export] *)
Definition new_reg_addr (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st') !! rid = Some r /\ (s_regions st) !! rid = None /\
    lr_lo r <= a < r_base r + round_up_pg (r_len r).
(* [comment removed for export] *)

Record mrel (st st' : mstate) : Prop := mkMREL {
  mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
  mrel_next : (s_next_rid st <= s_next_rid st')%N;
  mrel_reserved : s_reserved st' = s_reserved st
}.

Lemma mrel_refl st : mrel st st.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h04__x1h12sth21Hh37__arithh44__ffh58__varmaph65__with71rh82r'h93ridp;1p;4p;2p;3p;7p;5p;6g00Z@j1QTg004Bj4PTg002Ij4ATg01Y^j15Tg01G2j2:Tg0095j30Tg01[Ej18Tg006kj14Tg01\Uj16Tg00K4j23Tg00B_j21Tg00;kj22Tg00C[j1OTg00D;j1;Tg00D[j2NTg00E9j1LTg00EWj1KTg00Fej2HTg00GHj4FTg00L;j7ETg00HUj2BTg00I7j2@Tg00Icj3CTg00JBj4DTg00jfj47Tg01kaj4?Tg01l;j3GTg01m0j1>Tg01nDj4ITg00hFj2JTg01o2j1=Tg020Fj5<Tg01[1j6MTg009mR0g01ecR1f3R2f2R3f1R4f0R5EMp=9g01D>R6P5P5%Q1R7P0g01g5R8g01gNR9P1CPR:P0P8P9P1CAR9P4%53C91:15R830P1P:P9P2f4#5C9=078g01glR8%85%8330g009OR;%45%4330%63R<%65'3'1'1'1X81P4P:P9P3%52C91:14507%84R7=087R2%44R9=0;9R:%64R=/3=R='1R>'1P5P2P>1287P:P=12;9g00QGR9#O%;91N;4%L;%K;R9g00Mag00N@R=P=g00N`R=P;g00O`,H;R:g00R3P:CFg00O@FE1B9=P5P3g00RZR=g00S:R9'21@53=0=9dg00MC=C;4CDb4b5b6X0;1355^0;P5P<O1b3C7C7C7C?W2X71X90P0g021ZR1g02269G01%>5CI1J;;#;%=5'2D<X16P5O1W1o"). Qed.

Lemma mrel_trans st1 st2 st3 : mrel st1 st2 -> mrel st2 st3 -> mrel st1 st3.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "p'0h02r'h12H0h22N0h34__x1h44__x2h54__x3h61Hh71rh83ridh97__arithh:4__ffh;8__varmaph<5__with=4cstrh>5cstr0h?5cstr1h@1ehA3st1hB3st2hC3st3hD2B'hE3B''hF2H'hG3H''hH2K'hI3K''hJ2L'hK3L''hL2N1hM2N2hN2R1hO2R2hP2S1hQ2S2hR3r''i009mrel_nexti01<mrel_regionsi02=mrel_reservedi031xp;2p;1p;4p;3p;6p;5p;<p;7p;8g022[R0j2GTg00Z@j1yTg004Bj4gTg002Ij4aTg01Y^j1:Tg01G2j2ITg01[Ej15Tg006kj14Tg01\Uj12Tg01m0j13Tg021ZR1j2?Tg00hFj2rTg00D;j1\Tg01o2j1BTg0095j31Tg00K4R2j20Tg00B_R3j28Tg023oj6OTg024MR4j16Tg017]j4HTg024kj1ATg00VRj1_Tg00^ej2VTg0143j3^Tg014\j2xTg00C[j1wTg011@j3vTg00D[j2]Tg00_Nj1uTg015Hj4UTg00E9j1qTg00EWj1pTg00:Kj1oTg00>gj1[Tg00Fej2MTg00H3j1mTg00HUj2jTg00;kj2ZTg00I7j2iTg00Icj3kTg00JBj4lTg00jfj4TTg01kaj4hTg016Ij4nTg020Fj5fTg01[1j6LTg025NR5j2eTg013Nl<dTg00GHj4sTg00L;j7tTg00L_j8cTf5R6g009mR7g01ecR8f4R9f3R:f2R;f1R<ELf0R=31p=>%2</0=p==g01glR>%5:719g009OR?%4<71;/8='8p=<f6R@P7P8P6P9P:%:;EL;1</8=p=71e8=p=9P7P8P:P;P<P=ELp=Y%4;91?:%2</0='8p=RA169:A1>;</8='8p=PA1?:;10<='8p=@A1>9:A1?;</8='8p=K%5<91>;/8=p=J%5=91><p=SA1><=p=XA1?<=p=QA1?:;%2</0='8p=bP7P8P:P;P<%:=ELp=`%4=91?<p=W1Z?=p=;P7P?P1P4P2g025hP6P9P:P;P<P=M<dp=Fg00MCR2/0=p=CP?P<g00R3P=Csp=DP<g00MaR4g00N@R1P1g00N`RAP=g00O@Ftp=EP:P4P1P1PAP;P<P=Gcp=Ng01D>R41G;<P0P:P;1G:;1G6:[P=%y8RBP7g01g5RCg01gNRDP8CgREP7PCPDP8CaRDP<f8RC#:1I8=RFE>PBPEPDP:f9RGPF%5=RHP;%4=RIP;%2=RJ,=;D<RKF7X08#9[^78^87f7RL#3%3@'?1r??#\RM%BL%BC311GCLP0PGPCf;R0/GGP=PBPEPDP<f>RN#:PFE>PBPEPDP:f?ROPFPKF7X08#9[^78^87f=RP#3f<RQ#3'?%BP%BNRR51Mf@RSPNPBPEPDP<fBRT#:PFE>PQP;P<P=O3PBPEPDP:fCRUPFPKF7X08#9P5P8PBPEPDP9fDRK#:RVCYPFPH%5:PIP:P:PJCREPX08PBPEPDP6PVCYPFPH%59RVPI%49RW%29RXPJC@EPX08#9P=PBPEPDP@fFRYPFPH%56RZPI%46R[%26R\/0JDKF7P3PBPEPDPLfGR]#:1I8<R^E>%5<R_P@%4<R`P@%2<Ra,=@D<PBPEPDPGfHRbPFPI%4CRc%2CRdPJC@9JHCF7X08#9P=PBPEPDPGfIRC#:1I8:ReE>PW%4GRf%2GRgPXC@9JVGP3f:Rh,SZP[PhPhP\CRPBPEPDPPfLRhPFPH%5QRiPI%4Q%2QRQ/0JDKF7X08#9P=%5LRj/XiPc%4PRi%2PRkPdC@P3%4NRl,Qf%2NRm/0gPBPEPDfARnfPPFPI%4SRoPSPJCb9JHSF7X08#9P=%40R0/Qo%2nRo/0QPYPUPPPGO3PBPEPDPKfSRpPFPIPlPmPJC@9JHNF7X08#9P5P8PBPEPDfER5fTRmPFPHPOPIPO1=OJD<F7X08PBPEPDPYfURlPFPH%55RqPI%45Rr%25Rs/0JDKF7X08#9P=PBPEPDP]fVRtPFPHPnPIPn10oJD<F7P3PBPEPDPbfW#:P^E>P_PTP`PT1=TaD<PBPEPDfJRafYR`C`R_PFPH%5CPI%4CR^%2CRCPJC@EPX08#9P=A1B_ePVPqPWPr10sXDKP31SZYP[PYPYP\CRPBPEPDfNR\f]PFPHfMR[PIP[%2[R[/0JD<F7X08#9P=1SjbPcP^PCPdC@P31Wfa1=agPBPEPDfRfaPFPHfQRaPIPa1=aJD<F7X08#9P=1W0h10[QP8PBPEPDPlfdRlPFPHPmPIPm%2mRI/0JD<F7X08PPPBPEPDPmfcRm#:1I8PE>%5PRP%5pRD'XRE%4pRB,QiRJ1=pkRp'8Rk'8PGPEPkP>PP%5\PDP6PYEOPJPpP?Pi%4\PBP<PTEO%3lRl%3mRm'?%6lRB%6mR\'0RiPlPB%;BPmP\%;\EFPtCHPiff#3Rife#3Rt'?%6iR\%6tRm'0RBPiP\%;\PtPm%;mEFf^CHPB%At%Cmfg#3Rm#A%6m#Cfi#3Rm#A%6m#Cg00QGRmg01=3Rt#_RB#_,V?1V?B1V?t5^?5^?g019g'x%wm3vRt%\mRmP?1]?;RBP<P?1]?:R\P:%u?CUCU%q?Ri%p?Rlg00O`Rp#oRJ#[,M?RD1M?JRJ'D,El%m1R1Pl1M?pRP/DD,ElP11DPJ,ElRDCNCN1jlARAP=P;g00RZR>g00S:Rk'Z1i=;=1>kdAk?2<ClR2b:b;b<X3?X4?X5?10;<10<:10;:Rk[[^3?^4?^5?P=PI%2U%2`P@P]O5b9b?b>b=b2b2CTCTCTChWKWEP<P=O2n2001000000121000000W1WIP<P=O2n2001000000121000000W1WGP<P=O2n2001000000121000000W1XR8P<P=O2n2001000000121103000b@WJWDP<P=O2n2001000000121000000W1WHP<P=O2n2001000000121000000W1WFP<P=O2n2001000000121000000W1X08P<P=O2n2001000000121103000b@W6X78X87%3SR7%3NRN'?%67R8%6NR]'0P7P8%;8R@PNP]%;]R`EF%3ORU/?N%6URI/0]R>PUPI%;IPNP]P`EFP<CHP>%3nRn/?7%6nR>/08R`PnP>%;>P7P8P@EFPGCHP`%A7%C8%3TRT#A%6T#C%3KRK#A%6KRK#CPtPmP?PBP<P\CUPiPl%[p,M?Rp,DP,ElP1Pl1DpJ,ElP1PDCNCNPAP2b:b;b<X3?X4?X5?10=;10:;Pk[[^3?^4?^5?P=%35#6PK%3Y#6P9P6O5b9b?b>b=b2b2CnPMPR%BO%BSP=PLEODfWQWMWOP;P<P=O3n2001000000131101100102W6WPWLWNP;P<P=O3n2001000000131101100102W6XC4XB4XA4P;P<P=O3XC4XB4WAo"). Qed.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h01xh17__arithh24__ffh38__varmaph45__with51zp;1p;2p;3p;4p;7p;6g01Qij18Tg00:Kj11Tg00;0j12Tg00>gj1<Tg00@Pj2FTg026Hj24Tg008Xj23Tg0095j35Tg00;kj26Tg026hj1;Tg00kAj2:Tg00C[j19Tg00D;j1KTg00_Nj1JTg00E9j1ITg00EWj1ETg00FBj27Tg00GHj4CTg00L;j7@Tg00HUj2ATg00I7j2BTg00Icj3?Tg00JBj4>Tg00K4j2DTg027Fj3=Tg0053j6GTg01]dj1HTf0R0#1#1p=0g009OR1P1%80R2g00O`R3#1R4#2%<3#0#2R3'F'4f1R5/30%85%14#0#0#0#0#0#2R4'4,35551X511424,30R4,61%;3,:2g00QGR6#9%K6%J1%I1%E1R6g00Mag00N@R7P7g00N`R7P1g00MCR8,71g00R31713CCg00O@F@1A67P0f2R7g00RZR6g00S:R9'61B07=569dA?185C>b2b3b41D83P0b19=23EG%H0=514eX01P0O1W0o"). Qed.

Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"] "h02H1h12H6h24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h84__x5h94__x6h:1xh;1yh<1zh=1Hh>2H0h?2H2h@2H3hA2H4hB2H5hC2H7hD2H8hE2H9hF7__arithhG4__ffhH8__varmaphI5__withJ1qhK2q0hL1rhM2r0p;2p;1p;3p;4p;6p;7p;8g00K4j24Tg01Qij10Tg00:Kj1@Tg00;0j1sTg026Hj21Tg008Xj22Tg01]dj1OTg027ij2LTg00eaj1aTg00BBj2;Tg00;Nj2BTg028Jj2XTg00@4j23Tg00B_j25Tg0291j2RTg029Xj2QTg02:>j2PTg00C:j2gTg00;kj2NTg00VRj1:Tg00^ej29Tg00f:j1eTg00fXj2dTg00g9j3KTg00]Sj2cTg00^<j3bTg014\j2`Tg00bLj2_Tg00C[j1^Tg011@j3]Tg00D;j1\Tg00D[j2DTg015Hj4CTg00_Nj1[Tg00E9j1ZTg00EWj1rTg00FBj2YTg00Fej2=Tg00H3j1qTg00gbj6pTg00>gj1UTg02:dj2TTg00`Oj3STg015fj3ATg00GHj4GTg00HUj2oTg00I7j2nTg0095j3HTg00Icj3jTg00JBj4iTg02;Gj1MTg0053j6JTg0143j3hTg00L;j7kTg01M]j6lTg018Dj7mTg00L_j8fTf0R0#@#@p=?g009OR1g00MCR27H0p=Ff1R3=H10p=>1420p=<Ah130p=6P1P3g00R3P0CGp=IP3g00MaR4g00N@R5P5g00N`R6P0g00O@Fkp=7P3P4P5P5P6P0Elp=Wf2R7P4P5P5P6P3P0Fmp=VP1P3g01;:P0CGp=Ef3R8P4P5P5P6P7P3P0Gfp=81430P1%07R9g00O`R:#@R;#@R<#?#?#?#?#?#sR='1,27%O7R>,40X<1P1%03/1=,23%08R?/1=R@,28/40X<11L9=%F=R9#aRA1;?=,B=/2@,>?[1X?=132=R?f4R@#0RB/1=RC#<13C='5[1RB=13=2RCf5RD#0RE/1=RF,3=14F2'5[1QE=f6RE#0RF/;=#F\91PF=f7RF#0RG/1=/>G\91;G=P1f8RG#0RH/1=P11LH=f9RH#0RI1;I=,B=11I='2'>\A1XI=f:RI#0RA/1=RJ#<13J='5\?1RA=f;RA#0RJ/1=RK,3=14K2'5\C1QJ=f<#0RJ/;=#F\91PJ=f=RJ#0RC/1=/>C\91;C=P1f>#0/1=P1PDg00Pa1g2='NP?eR?O1%<0130='5PJP?O1%<G13G='5p-0R?g00QGRJg01=3RC#:#:RK#:RL#:RM,91RN%e:,d1RO191KRK5K1191CRC'6'61c1==b1C%:MRM#:,91191M9K1O191L/6K,6N'6'6'6g019g'`'_%^J3]%\JP1P11D1@P71D1ECCP3P11D1DP8%[1CCCC%Z1%r1RJ1Y12RN1=1<R<'I,7J1WJG5VJ%q5RKPJPJPJP4P5P5P61Y1=R5/EN,7JEpRNPK%U:R4,=1RL,T1%@4,=19S15=A1<'E,7JC8PKPJ1WJHP11=1;R4g01:SP5CG,7J5VJPKPJPJPNPK1=1:R:,T1%U;,=19S15=A14'E,7JC8PKPJ1I:L,7JPKAA1:4AA1L<'I,7JC8C8C8C8C81oJ6P0P7g00RZRJg00S:R6'N1n07=HJ6dAj123CibGbHbIX41X51X61X71X81X91X2?W3%<8/5Eg01>6\9R91B=F/2D,>B[138=R2,5H1B=G/2D,>B\914@E12DE12FG'4[[[[[^41^51^61^71^81^91^2?^3?P0%<IP2P@PAP8fBPIfCP7PHP3f@fAO=bFb0b1bMbKbEbDbCb1bBbLbJbAb@b?b0b>%O3%M3EJP>%M7EJW=X;1X:1P3P0O2X;1X:1o"). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
(* [comment removed for export] *)
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma get_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_fp ()) ["CEIL_WRAP_1"; "FASTFACTS"] "h01mp;1p;2p;3p;6g02<cj1<Tg00:Kj1;Tg00;0j14Tg00@Pj23Tg00U4j2:Tg02>4j20Tg02?Jj21j16Tg0095j32Tg00;kj25Tg02@_j37Tg02B1j38Tg0053j69Tg02C[R0p,2mrR1#<g00O`#;#4p,1k'3':R2p,3st1R3p,1gR4'0'1f01121R1520X001501%62R2=743/04A8342E9p,3st2/04=201eo"). Qed.
(* [comment removed for export] *)
End FASTFACTS.
End CEIL_WRAP_1.

