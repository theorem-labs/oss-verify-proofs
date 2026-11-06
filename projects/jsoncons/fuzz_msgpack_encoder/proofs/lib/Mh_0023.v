(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Bool Lia. From LinuxProcessSemantics.LinuxProcessSem Require BvBase State. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0023 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01I46Stdlib9micromega7EnvRing5PExpr00I45stdpp9bitvector;definitions2bv00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega=RingMicromega7Formula00I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib7Mh_0023?PlacementSearch<higher_fit_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib7Mh_0023?PlacementSearch=no_higher_fitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib7Mh_0023?PlacementSearchEhigher_fit_b_completeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_0023?PlacementSearchBhigher_fit_b_soundC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula04C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01".
Module PlacementSearch.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PlacementSearch () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC46Stdlib6ZArith4Zdiv:Z_mod_multC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_0023?PlacementSearch@fold_max_ge_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebc59OSSVerify5KrLib7Mh_0023?PlacementSearch>fit_candidatesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib7Mh_0023?PlacementSearch;fold_max_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearchCfold_max_in_or_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7add_modC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib7Mh_0023?PlacementSearchGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z;le_gt_casesK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0023?PlacementSearchBpage_round_up_Z_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearch>fold_max_ge_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearchBpage_round_up_Z_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z7le_reflC56Stdlib6ZArith6BinInt1Z;add_le_monoC4ELinuxProcessSemantics?LinuxProcessSem5StateAregion_free_introC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib7Mh_0023?PlacementSearch<higher_fit_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C46Stdlib5Lists4List8map_consC46Stdlib4Bool4Bool=andb_true_iffI47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_0023?PlacementSearch5placeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0023?PlacementSearch:place_fitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearchAsearch_candidatesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someC46Stdlib5Lists4List4findC47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_0023?PlacementSearch<existsb_findC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Zminus_modc59OSSVerify5KrLib7Mh_0023?PlacementSearchEhigher_fit_b_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearchEhigher_fit_b_as_placeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearch>place_in_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topc59OSSVerify5KrLib7Mh_0023?PlacementSearch;place_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem5State8mkVmMapsc59OSSVerify5KrLib7Mh_0023?PlacementSearch>place_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearch>witness_ledgerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0023?PlacementSearch8demo_topC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBalloc_top_mkVmMapsI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02c59OSSVerify5KrLib7Mh_0023?PlacementSearch;full_ledgerC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
    : Prop :=
  forall g : Z,
    (g mod page_size = 0)%Z ->
    (aZ + nZ <= g)%Z ->
    (g + nZ <= baseZ)%Z ->
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.

(* [comment removed for export] *)
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
    : list Z :=
  (aZ + nZ)%Z
    :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                      + bv_unsigned (snd p))%Z)
           maps.

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
    : bool :=
  existsb (fun g => (g mod page_size =? 0)%Z
                    && (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
                    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
          (fit_candidates maps aZ nZ).

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01zp;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g003Nj27Tg003kj16Tg004Ij20Tg004fj21Tg005Cj25Tg005cj12Tg006aj23Tg007Aj34Tg007[R1f0R0g0089R2'7g0091#6'0/12/52%20/32g009V541eW0o"). Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h02H0h17__arithh24__ffh38__varmaph45__with52H1h62H2h72H3h82H4h94__p1h:6__sat1h;4__x1h<4__x2h=4__x3h>1qh?1rh@1HhA2H5hB2H6hC6__sat0hD6__sat2hE1zp;1p;2p;4p;6p;3p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00:4j1>Tg003kj1ITg00:Yj1jTg00;9j1\Tg00;Yj1XTg00<7j1UTg00<Uj1TTg00=@j2@Tg00=cj49Tg00>Nj6RTg00?2j2iTg00?Tj2gTg00?nj2`Tg007Aj3BTg00@Zj3ZTg00A9j4YTg00Akj3Vj2KTg004fj24Tg00BLj25Tg006aj22Tg003Nj2:Tg00Bij2GTg00CZj2FTg00DKj1STg00Ddj2Ej3QTg00EKj23Tg00EgR1j28Tg00FBj2DTg00Fij27Tg00GEj2HTg00Gkj2JTg00HQj1NTg00I0j2CTg00IYj3PTg00JBj2hTg00Jnj3fTg00KNj2OTg00Klj4eTg00LJj1_Tg00Llj6^Tg00MPj1]Tg00N5j2?Tg00NXj7[Tg00O<j3LTg00O_j3aTg00PBj3MTg005cj1bTg004Ij2cTg00Pej7dTg00QIj8WTf0R0#>#>p=;f2R2f1R3':/c0p=1P3g00QmR4g00RLR5P5g00RlR6P0g00SLFdp=<g007[R7g009VR87B0p=AAB730p=61780p=0f3R9P4P5P5P6P2P3P0GWp==g0091R:#>R;#>#;#;#;#;#;#IR<%I:R=510R>g00SlR?#jR@%\?RA%X7RB%U7RC%T7RDP4P5P5P6P71@7<REg00TXRF1@78RGC9,<DERRH1iD6RIP0P2g00U?RJg00U_RK'g1`02=BJKdAZ783CYRKb2b3b4%A<RJg00V?[RLP0b17V<14><,5<12><':,6>A13<=R>1G><%0>%0<RMA19<=RN/2<#0[[A12<=RO/F<%0ORPf4RQ?1<=RR/4<RS#0\M[1KN<%SJRT15<S12R<RS':,6R[1ER<138<RUf5RV?1<=RW/2<RX#013X<'8[1DW<13<8RYf6RZ?1<=R[/2<R\,3<17\8'8[1H[<f7?1<=R]/4<#A\J1J]<f8?1<=R^/2</6^\J14^<R_P7f9R`?1<=Ra/2<RbP7P@PAPBPCP7PGg00V\RGPEC9,<DRBPIPKb2b3b4PUP0b1b?b>b8b7b6b5b0bCb:7Q<12><R>#013><'81GO<%0S\M\P1FN<%0N14W<RN#0\M[1KR<15<N/:X,6W\T1EW<%0\13\<'8\U1D[<12]<R[,3<17[8'8\Y1H]<%A_\J1J^<16ba\J14a<P7f:Ra?1<=/2<P7P1%00130<f<152<'7P`%02139<R`p-0R1g00WCRJ#NRb#N,C71C7b1C7J5P75P7g00Wb'h=f?@PAP71O72P31O79CePCPDPDPB%_5RBPDP4P5P5P6PDP4P5P5P6PVE^P7%]:,?7R6PGPEC9,<DF[C=PBPDPDPHPBP71?7:R:=L7E1@7=5a7PF1?7;R;9M7E=L76C9,<DC=PBP7P:g00XNAM7;EC9,<DC=C=PIPKb2b3b4X;7X<7X=7W918Q`\U15<9/:Q,6O\L159<,72[[^;7^<7^=7^91P0%0VPVPZf@Paf;O6b1WBW0P3P0O2n2001000000121000000b?b>bAb8b7b6b5b:bDb0b@%b0,70eXE7o"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh12H0h22H1h32H2h42H3h57__arithh64__ffh76__sat0h88__varmaph95__with:4__x1h;4__x2h<1qh=1rh>6__sat1h?4__x3h@2H4hA2H5hB2H6hC2H7hD2H8hE6__sat2hF2q0hG2r0hH4__x4hI2HbhJ3HbmhK2HqhL3HzbhM1bhN1zp%0p;2p;1p;6p;3p;4p;5p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00Fij2:Tg006aj20Tg00:4j1GTg003kj1WTg00Bij2STg00Akj2>j3ZTg00DKj1aTg004fj21Tg00Ddj2ATg00EKj23Tg00Egj25Tg00FBj2;Tg00GEj2<Tg00Gkj2=Tg00:Yj1fTg00;9j1eTg00;Yj1dTg00<7j1cTg00<Uj1bTg00=@j2QTg00>Nj6`Tg00?2j2_Tg00?Tj2^Tg00?nj2]Tg007Aj3HTg00@Zj3\Tg00A9j4[Tg003Nj2ETg00CZj2PTg00HQj1UTg00I0j2NTg00IYj3DTg00JBj2YTg00Jnj3XTg00KNj2TTg00Klj4FTg00LJj1rTg00MPj1qTg00N5j2MTg00PBj3JTg00O<j3ITg00O_j3pTg00BLj2CTg00Y5j5oTg00Yaj5nTg00ZOj1hTg00Zmj2gTg00[Nj3VTg00\7j5iTg005cj1jTg00=cj4RTg00Pej7kTg004Ij2lTg00QIj8mTg007[R1f0R0g009VR23Hp=7%G0#Gp=B1:20p=4f3R3f2R4f1R5'C/E05H1p=81:02p=@AH150p=?P1P5g00TXP0CRp=KP5g00QmR6g00RLR7P7g00RlR8P0g00SLFkp=61E45/l0p=2P1P5g00V\P0CRp=OP3P6P7P7P8P4P5P0Gmp=9P1P5g00XNP0CRp=L1:50g0089,05#7g0091R9#GR:#GR;#B#B#B#B#B#WR<1S4<%44%4<R=f4R>/0<R?#4[[1>3<%7<R@#aRAP>P<11><RBP?C8[1A><132<R?f5RC/0<RD#4RE13D<'5[1;C<13<2RDf6RF/0<RG,3<%@G'5[1<F<f7RH/1<RI#7\@1=H<f8RJ/0<RK/?J\@11J<S00P1f9RL/0<RMP1g00SlRN#fRO%eNRP%d1RQ%c1RR%b1RSP6P7P7P81Q1<R61Q12RT'K,6SE`RU1_S8R8P0P4g00U?RVg00U_RW'^1]04=HVWdA\125C[R2b6b8b9g00V?\@RWP0b5b=b<b4b3b2b1b0b75Z4P4P<114<104<C8%W9RV92><RXP<113</EVRY1S3<RZ%43PE\=[RE1P><R[%4>R\11F<R]#4\=[R^1>C<R_PFP<P]PGC8\AR]1AF<RF10H<R`#413`<'5\?R`1;H<Ra13<K%@K'5\DRb1<J<Rc11L<#7\@Rd1=L<Ref:Rf/0<Rg/?f\@Rh11f<RiP1f;Rj/0<RkP1POPPPQPR1OT6,6SP8P2b6b8b9P?P0b5b=b<b4b3b2b1b0b7b>PZPEP[P^P_P]PFP`PaPbPcPdPePhPiP1PkP1g00WCRk#URi#URh#U,N11N1hRh1N1iRi1N1kRk5D15D15D1g00WbRe'Y=XNOPPP1P11T1>P4PQCFP51T13S01CFPRPSPSPU%r7R7%q9,M1Rd1M1:R:9J161M1;R;5I1'K,6SC9P7PS1K;T,6SS02P7PS1M19Rc/Ld,6SP7AI1c61Q1VRd5p1AI1:dRd9J16'O,6SC9C9C9P8P2b6b8b9X:1X;1X?1XH1P3P<P4P>C8\W%7>1:4>A23<V1E>V,C<'3[[[^:1^;1^?1^H1P0P5f=RbP4f>RaPHPjf<R`O7b5b=b<b4b3b2b1b0b7b>Do11X</3YA2C<V/1<RY/C<1CB<P>PYPBP<1S><R>%4G\=\\R\1PC<RG%4C%4I\=[RIA2H<VRC/P<RB%4CA2L<VRC/1<RY#4\=[RXA2J<V/><S03PCP<PY10C<C8\AS041AC<RCA2f<VRY/0<RF#413F<'5\?RF1;Y<RYA2j<VR]/0<R_,3<%@_'5\DR_1<]<R]A2`<VR^/1<#7\@R[1=^<R^A2b<VRE/0</?E\@RZ11E<REP1A2a<V/0<RlP11>a<Rmf?RnP<11n<10n<C8\ARo1An<Rpf@Rq/0<Rr#413r<'5\?Rr1;q<RsfARt/0<Ru,3<%@u'5\DRu1<t<RvfBRw/1<#7\@Rx1=w<RyfCRz/0</?z\@R{11z<R|P1fDR}/0<R~P1POPPPQPR1LT6,6SP8P2b6b8b9P=P0b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEP>P\PGPIPBPXQ03Q04PCPFPYP_P]P[P^PZPEP1PlP1PmPoPpPrPsPuPvPxPyP{P|P1P~P1POPPP11T14P5PQCFPRPS1Ocd,6SP71Lc:,6SC9P8P2b6b8b9X:1X;11E5V,301:54[^:1^;1P0P4PLPwO3b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEDnP>P\PGPIPBPX1>H<PJP<Q00PKC8\A1AJ<%4M13M<'5\?1;L<13<g%@g'5\D1<f<11j<#7\@1=j<10`</?`\@11`<P110b<P1A2n<V/><A2q<VRqP<11q<10q<C8\A1Aq<A2t<VRt/0<Rq#413q<'5\?1;t<A2w<VRw/0<Rt,3<%@t'5\D1<w<A2z<VRz/1<#7\@1=z<A2}<VRz/0</?z\@11z<P1fE?2<V/0<P1%h9,g1R9=V1hAV19i=D1k5D1/Ye=XNOPPP1P1Q01P4PQCFP5PQCFPRPSPSPUP7AJ16c=I1;,K:,6SC9P7PSQ02P7AJ1c6/L:,6SC9C9P8P2b6b8b9X:1X;1X?1P4P<P5P3C8\W%731C4</:3[[^:1^;1^?1P0PJfFPLPaP}O5b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEDibKbJ%j3/:4eWIWLXM1XN1o"). Qed.

Lemma fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h04__x1h11lh21sh37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94__x3h:4__x4h;1Hh<2H0h=2IHh>1xh?2z0p;1p;2p;3p;4p;6p;7p;5p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00;9j1FTg00Fij20Tg00:Yj1ATg00KNj2=Tg00<7j1UTg00<Uj1OTg00N5j27Tg00?2j2JTg00?Tj2HTg00?nj2GTg007Aj33Tg00@Zj3XTg00A9j4VTg00\YR1j2<Tg00]6j2TTg00EKj2BTg00Egj25Tg00]Xj2@Tg00ZOj1NTg00Zmj2MTg00HQj1;Tg00I0j24Tg00[Nj3LTg00IYj38Tg00JBj2?Tg00Jnj3:Tg00;Yj1KTg00Klj4>Tg00:4j1ETg00=cj46Tg00MPj1ITg00Llj6PTg00^2j7QTg00LJj1RTg00^Vj5STg00_8j5[Tg00Pej7ZTg00NXj7YTg00QIj8WTg007[R0P0P1f1R1f0R2D[p=2P0P1g00XNP2C6p=9P1g00QmR3g00RLR4P4g00RlR5P2g00SLFZp=1f2R6P3P4P4P5P1P2FYp=Cf3R7P3P4P4P5P6P1P2GWp=D%F0R8P01212,02^20R9X18g00SlR:#AR;%F:R<1=01%U0R=%O0R>g0091R?,70R@/9@'11J>5RAP2P6g00U?RBg00U_RC'H1G26=3BCdg009V=X01CVRCb4b6b7X001022^00P2P1O1b3%A0/22,02eX20P11<27RBO1126B,0Bf4RB,T11B1B1<1BRD=30B'510B1A30D1'5'@f5,<6P0p-0RD%N?,M0g00WCRE#;RF#;RG,405L0140F140E580580REg00WbRF'?%;G,40=80E/?F=::;5::P<P0P01=0BP6%K0C>P11=07C>P=P>P>P3P4P4P5P0P@g00V\%E?R=#E,70R<C6,1>P0%I?,70R?g00TXR:P<C6,1>5C>P>P3P4P4P5f6R5EPP0P?P:P@C6,1>5C>FQ%R4R4P>170=R=,9?,1>P419@=,1>CDCDPAPCb4b6b7X00X80X90X:0W51B27A3067'5A3062,5B'@10761067[[^00^80^90^:0^5DP2f7RD/0BPDP11251PBP6P7O7b3b?b<b;A:076/22,02eX20X=9X18X>0P2DSW1o"). Qed.

Lemma fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h03Hinh11lh21sh31xh41Hh54__p1h64__x1h74__x2h84__x3h94__x4h:1yh;2H0h<2IHh=7__arithh>4__ffh?8__varmaph@5__withA2z0p;1p;3p;2p;4p;6p;7p;5p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00;9j1ETg00_Vj34Tg00Fij20Tg00:Yj1DTg00_mj2XTg00Jnj32Tg00\YR1j29Tg00`Lj2LTg00]6j2KTg00EKj2@Tg00Egj28Tg00]XR0j2GTg00HQj1=Tg00I0j26Tg00ZOj1WTg00Zmj2VTg00[Nj3UTg00IYj3<Tg00JBj2CTg00KNj2BTg00;Yj1RTg00Klj4ATg00<7j1QTg00<Uj1OTg00Llj6NTg00MPj1MTg00N5j27Tg00=cj4;Tg00:4j1?Tg00^2j7JTg00LJj1PTg00?2j2ITg00?Tj2STg00?nj2TTg007Aj3HTg00@Zj3`Tg00A9j4_Tg00aYj6^Tg00^Vj5]Tg00_8j5\Tg00Pej7YTg00NXj7ZTg00QIj8[Tg007[R2P2P1f1R1f0R3D\p=1AH213p=3P1g00QmR4g00RLR5P5g00RlR6P3g00SLFYp=5f2R7P4P5P5P6P1P3FZp=>P2P1g00XNP3C;p=:f3R8P4P5P5P6P7P1P3G[p=F%E2R9P2A42371187,01[^32^22R:X19%D2R;942311;7,01/X3W0X32X22f4R;=2289423P0f5R0/31A421;f6R<=220/18,07P313<7P2P8f7R=9223/10,0;X:219;8R>,L<11<>,0>1K0;1@0;190;R>/3;'810;013>0'8'G19<0P2p-0R>g00SlR?g00WCR@#=RA#=RB#=,62g0091RC#W,V2162B5U2162A162@5<25<2R@5<2g00WbRA'C1C@A%D?52?32%E?P2P21B2;P7%R2CAP11B28CA%Q2%O2R?P?P4P5P5P6P?P4P5P5P6P<ENP2%MC,72R4g00TXRA172CR@C;,5?5>?%?CRC#?,72RB,:@,5?P2P4PAPBC;,5?5>?FJ%P5R5P?172CRC,:4,5?P51:@C,5?CFCF1I?6P3P7g00U?R?g00U_R6'S1T37=H?6dg009V=`21C_b>b?b@X62X72X82X92W51373,8;10381378'8'G10871078[[^62^72^82^92^5>P3f8R>/@=P>P1f:/11P=P7P8O7b=bAb;b4A228</1;,08eP=P3E^W4P3O1A4270P019;=P8P3O3A22=</1;,08eW0P3O1n200100000021100010000W0X32X22X<:X19X:2P3D]W1o"). Qed.

Lemma fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01xh11bh21lh31sh42Hlh52Hsh64__p1h74__p2h84__x1h94__x2h:4__x3h;4__x4h<1Hh=2H0h>2Hxh?2IHh@7__arithhA4__ffhB8__varmaphC5__withD1yhE2z0p;1p;2p;3p;4p;7p;5p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00;9j1JTg00Fij20Tg00:Yj1DTg00Jnj3=Tg00\YR1j2<Tg00?Tj2BTg00b7j3RTg00]6j2NTg00EKj2@Tg00Egj27Tg00]Xj2ITg00HQj1>Tg00I0j26Tg00IYj35Tg00JBj2HTg00KNj2GTg00;Yj1WTg00Klj4ETg00<7j1VTg00<Uj1STg00N5j24Tg00:4j1FTg00=cj4:Tg00MPj1QTg00^2j7PTg00LJj1MTg00?2j2LTg00?nj2OTg007Aj3?Tg00@Zj3KTg00A9j4TTg00bQj3UTg00^Vj5^Tg00_Vj3]Tg00_8j5\Tg00Llj6[Tg00Pej7ZTg00NXj7YTg00QIj8XTg007[R0f1R2f0R33]p=2P0P0P1P2P3D\p=8A?023p=1P2g00QmR1g00RLR4P4g00RlR5P3E[p=CP2P1P4P4P5P3g00SLFZp=3f2R6P1P4P4P5P2P3FYp=AP0P2g00XNP3C:p=;f3R7P1P4P4P5P6P2P3GXp=9%J0R8P01023R9f4R:,231027R;[^0018:7/06[[^10^30R<X28%D0R=,23P;[^00P218=7/06eW4X59X10X30f6R=f5R>5=0R?,23P;[^00P:1<7=P6P3P=11==12=>1B0=3RO210=6f7R;,N:1@:;1<:;R@/1;'710;:11@:'7'If8R@,<>P0p-0RAg00SlRBg00WCRC#>RD#>RE#>,60RF160D160CRC550550g00WbRD'H160E=50C950F/HD%DB5=B3=%JBP0P01G0:P6%W0CEP21G07CE%V0%S0RBPBP1P4P4P51CB=P0g0091R1,40RDg00TXRF%F1RC#F,40REC:,3B5AB1CB;P0PDPF%Q1,40R1C:,3B5ABFP%M4R4PB140CRC,;E,3BP4PB1;1C,3BP41;DC,3BC9C9C91LB5P3P6g00U?RBg00U_R5'B1O36=?B5dg009V=K02CTbAbBbCX80X90X:0X;0X6AW71137,7:1136,7>'I10:610:7107:[[[^80^90^:0^;0^6A^7AP3f:RA/0;1@;APAP;P=P2P6P7P>O9b@bEb=b<123=P6P211@2122;;U3O2W>X00O418?7/06eW4X59X10X30X?<X28XD0P3D^W2o"). Qed.

Lemma fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh11lh21sh32_Hh41oh51zh63Heqh73Hinh82IHh91yp;1p;2p;3p;6p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00;9j1FTg00?Tj2?Tg00b7j3:Tg00:Yj1CTg00\YR1j21Tg00]6j2@Tg00EKj26Tg00EgR0j25Tg00Fij28Tg00]XR2j23Tg00bQj3>Tg00aYj6=Tg00Jnj3DTg00^Vj5BTg00_8j5ATg007Aj3<Tg00_Vj3;Tg007[R3P3P1f1R1f0R4DAp=4f3R5f2R65<3A;314'3p=2A<314p=0A;314p=9A<361/34p=7A;314,36p=E%F3R7P31414R8P4P8P1C2^23R8X171044g00V?1?343:%C3R9/44R:P4P:P9C2eX23P11145R9O11469R:P9P:P6C2P2f4R:,11R9,45R;/0919;5f5R;,16R9,4:R<19<:R=97;<776P410<9P3f6R<,15R9f7R>P4P4P<C2974:X531@5<165<109<'518<51095'5'3P216:>11:>R2/0>'518>:102:'5f8R2,1;R:/0;R?P2P:P:P>C2'3P416;210:2'5P0f9R:,6<11<:R@/0:f:RA,1>RBPAPBPBP:C277>R>P4f;RB,62f<RC,1:RD/0CP3f=REf>P4P4PEC2974BX53RF10EARG10EERH19ECRI'31?3E9:HI3>11AEREP4E=W0W3P1P4O2n2001000000120000000W0P4O1182;/5?P018:<10@<P>P418B210D:P3PAPF10AAAEGAC1?3A3:PEP4E=W0W3P1P4O2n2001000000120000000W0P4O1n200100000021000010000b414;9R9P4E=W6P4O1109510<9R<199;R9'3A><943>X7=P4O1n200100000021100010000b4AD356R6/44R5P4P5P6C2eX23X88X17X93P4DBW1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma higher_fit_b_complete : forall maps aZ nZ baseZ g,
  (0 <= aZ + nZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z ->
  (aZ + nZ <= g)%Z ->
  (g + nZ <= baseZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  higher_fit_b maps aZ nZ baseZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01xi001xh11Hh24__x1h34__x2h44__x3h51zh63Hnoh71yh81Ah97__arithh:4__ffh;8__varmaph<5__with=4__x4h>4__x5h?4__x6h@1fhA1lhB1BhC3HinhD1bhE2b1hF2b2hG6heq_g'hH1mhI1nhJ2H0hK2H1hL3H10hM3H11hN3H12hO3H13hP2H2hQ2H3hR2H4hS2H5hT2H6hU2H7hV2H8hW2H9hX3HeqhY2HxhZ6__sat0h[6__sat1h\6__sat2h]2g'h^1qh_2q0h`2q1ha1rhb2r0hc2r1hd4Hendhe2_Hhf4__p1hg4__x7hh1chi1ghj1ohk1phl3H14hm3H15hn3H16ho3H17hp3H18hq4HaAlhr5HaPoshs5Hbaseht2Hchu5Hcandhv4Hcg'hw4Hclehx3Hcshy4Heq'hz5Hg'Alh{4Hg'Wh|7Hg'baseh}7Hg'freeh~4HgAli013HgWi026Hgfreei034Hghii044Hgloi053Hhii063Hloi074Hmodi084HnAli095HnPosi0:3HnWi0;6Hroundi0<1Si0=6__sat3i0>2aZi0?5baseZi0@2csi0A5heq_Bi0B5heq_Si0C4mapsi0D2nZi0E2q2i0F2r2i0G1si0H2x0p%0p&0p;1p;2p;3p;7p;4p;5p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g002UR1p4p710p8P0g0031R2p4p710p8P0P2p4p7210p8g00:4j1jTg00bkk10\Tg00cIk10QTg00clk20yTg00;9j1hTg003Nj21Tg00EKj2<Tg00Fij23Tg00dLj2=Tg00e2j3lTg00elk10fTg007Aj3>Tg00fUj2zTg00HQj1\Tg00I0k20:Tg00JBj2iTg00:Yk10ZTg00Jnj3gTg00;Yk10VTg00<7k10PTg00<Uk10MTg00MPj1sTg00LJk10GTg00N5k207Tg00=@k20ATg00NXk70rTg00?2k20gTg00?Tj2~Tg00?nk20cTg00@Zk30bTg00A9k40aTg00g;j3|Tg00ggj25Tg00hQj2{Tg00i@j2CTg00i]j3FTg00jhk30`Tg00kCk40_Tg00kak20^Tg00`Lk20]Tg00DKk10[Tg00l:j2yTg00lZk50YTg00mbk20XTg00]XS00j2bTP2j3eTg00o2j3dTg005cj1ETP1j4WTg00b7k308Tg00oOk30WTg00aYj6nTg003kk10UTg00>Nk60OTg00ojk40NTg010Kj6mTg00_Vj38Tg00EgR1j2@Tg010gS01j2cTg011Ak50KTg011`k10JTg0134k405Tg013Tk70ITg014Qk404Tg015Jj2?Tg015gk20HTg016Ik20LTg016nj4xTg017Ik403Tg00bQk309Tg017ck40FTg0192k40RTg01:=k10STg01;Lk20ETg00\7j5}Tg00Llk60xTg01;lk10DTg01<Mk60CTg01=2k40wTg01>2S02k302Tg01>Nk30vTg01?1j2oTg01?Nj2JTg01?lk401Tg01@Gk20qTg01@gk40pTg006ak20oTg00IYk30nTg00KNk20jTg00Klk40iTg00=cj4qTg00Pek700Tg00O<k30hTg00QIj8rTg00_8k50kTg00Bik20lTg00Akk20mTg004fk20?Tg00BLk20@Tg00Ddk20eTg00FBk20dTg00GEk20tTg00Gkk20uTf0R2#j#jp=kg009VR0/32p=7g0089R3-0o2p=0g007[R4?>20p=6f2R5f1R6'1/32p=Ug00U?R7g00U_R87>2p=91~42p=PA>462p=220:42p=[B0n462p=A20j42p=YP4P5P6P2H0ip=O20742p=XP4P6g00TXP2Cqp=uP6g00QmR9g00RLR:P:g00RlR;P2g00SLR<K00p=wB0h462p=_P5P9P:P:P;P4P6g00XNR=P2CqP<K00p=tP4P6g00V\P2Cqp=`P4P6P=P2Cqp=^f4R=P9P:P:P;f3R>P9P:P:P;P5P<K00P6P2Grp=BP>P9P:P:P;P5P6P2Grp>0=f6R<P9P:P:P;f5R?P=P>P9P:P:P;P5P6P2GrGrp>0>1306/@2p>0<P4P=P>P5P6P2Enp=]P4P4g00\YP6P2I0kp=SA8462p=4A84>51C62=>78'@p=D20l23p=T20m23p=L20?63-0@3/129>45p=R20e23p=G13061<23'@p=N20d23p=I1<361320'@p=H20t23p=M20?23p=:20u23p=K1C62=>78p=Z1562,15p=f20@32p>0611629>45p>0;g01B0R@9>72p=;1162,?5,J>=>7@p=Q1162,?5p=V1J62=>7@p=v1<23,@6p>0TA>728,@6p>0B1J56/J2p=aA8456/@2p>0sP7P8P>P5P6P2Enp=pg0091R@#jRA#jRB#k#kS03$0\RC$0QRD00yDRE#h11>5RF#71<0>%0?#6S04Q04g01BPS05,<?Q04f9RGf8RH'1S06/3<f7RI?UGHf<RJ1=CHS07f:RK,=CS083l#9&0fCS09#PQ05Q095>41zCKf;S0:,22X54g00SlRLg00WCRM#\RN#\RO#\RP#\RQ#[S0;%[N20:4MRM'AS0<'Ag00WbRN'i%\QRQ#\S0=#[S0>%[QS0?%[PRP%[O/AM'AS0@'A'A/iN&0ZLRM5gL3g%hLS0A%Y=%Y<7O5S0B%Y?S0C&0V4S0D7O>7O6RO&0P4S0E&0M4RQ%s@S0F#j#XRR%XARS'u,wQS0G&0G:RTPQ2074@R@%XBRB'_%sAS0H#XRA5tQPTPQQ0F#XRU/_BRV=tQ@S0IPTPQPQ1`ARPTPQPQ20A40RW/`BPTPQPQ1^WVPTPQP9P:P:P;AtQW@1`@S,wQK0rRVDBDBDBS0JH0=K0>20gQ;S0KP2P51~78S0L20c25#9dB0b406H0aS0Mb:b;b<X24X34X44X=4X>4X?412?6AU6=?AU=?51<IHS0N1<0I11IH#71<<IRX-0<<RY[[[[[[^24^34^44^=4^>4^?4P2Q05PJf=RZf>R[Q09Q0:P6P>P=P<PGPKO<b99|CKQ08,5CR\1{CKD]12\K1zCZ122[X54Q0>Q0?Q0;Q0<,AP'A'A'A/iN=gLMQ0APOQ0EPQPQ1uASPTPQPQ1_R@/^BPTPQPQ1_U@RO/^RPTPQPQ1`BAPTPQPQ1`W@PTPQPQ1^WOPTPVDBDBDBDBDBDBQ0KQ0Mb:b;b<X24X34X44X=4X>4X?412=6AU<6=AU=5I1<0=11I?#7PY[[\X[[[^24^34^44^=4^>4^?4P2PJQ05PZf?RXQ09P[P5P=P?PIPKQ0:O<b99|CZ1=CZ,5CRY1{CZD]12YZ1C2ZXh4f@RY?FX[60`4%h411YX,S2P4P41C2YXh4P2fCRVfBROfARR3FRPH0_1425P2PPP2PXCD+0^RPeZ0H4PP^0411ORRP-0]513P6RPePPP>11VORPPY1S>PRP#P125PRPePP%TVRP%7V1303R\fER]#0R^#7[[R_%T]%7]fGR`#0Ra#7\\[PPP_fDR_#LA>430RP$0[RbAR]]^[%G]1<03R^fFRc#0Rd/Nd[%Ic1<30Rd1Haa[%M`fHRe#:#6\P%KefIRf#0/2f\P%:fP4fJRg#0S0OP4fNRh#LfORi%0iS0P7Ri\b%GifPRj#0Rk/Nk\^%IjfQRk#0Rl/Hl\d%MkfRRl#:#6\P%KlfSRm#0/2m\P%:mP4fTRn#0S0QP4%LnfURo%0oS0R7Ro\b%GofVRp#0Rq/Nq\^%IpfWRr#0Rs/Hs\d%MrfXRt#:S0S#6\P%KtfYRu#0S0T/2u\P%:uS0UP4fZRv#0S0VP4PMQ0A%Y5%Y>S0W7O6Q0EPQ1_@S=tQURwPTPwH0=Q0KQ0Mb:b;b<X24X34X441126S0X/35AU65>S0Y[^24^34^44P2Pvf\Rwf]RxPmO4b9bcb`bObNbMbLbWbbb_bVbUbTbSbRbab^bQbPbKbJb1bZb[b\bG142=P1142<P6AFe`cRyP6P_CD[RzP2AF`c]R{P2PVCD146IR|[P5AFfe`S0ZP5P]CD\|P=P2O1S0[P6n2001000000120000000X04Pz^04P2P5P6O2P5P{P5PVCDP114>y1Z>_13=]P2AFgfeRy,4?1Z<`P11Z621356S0\[S0]13621Z56Rz[S0^13>5\z1y62S0_P6n2001000000120000000XH4XI4Q0]^H4^I4P2PHPfP6O3b1WYWeP6P2O2n2001000000120000000bYb1WYX04I0Y135YRYePY11_VRY-0X=1S=YRz/2Y14z='bQ0011]_Rz,S?RY/2z14Y?14?{P211c]S0`,S<R{Q0`'2P211`cS0a,2<11e`Rz142yX]412zzPEP4AeDD2,5CAdDD27fC#ER|XkER}PfCW,4z%Pz408PIP2D]byWXP2O114{<P1142HP6PyP6PcCD[S0bP2Q0ZP2P]CD146GR{[P5fKR~?FgfS0cP5P`CD\{P<P2O1P6n2001000000120000000X04Q0b^04P21SHzR{P6O2P{Q0ZP{P]CD11feS0Z,SGS0b/4yQ0b/Zc<0W2bCb1WCP2O1n200100000021000010000bjAF]_V,4>1zC=122?X54%PY12=YRYePYQ0=#\#[Q0?Q0;Q0@'A'A'A/iNQ0>Q0<'A/iN=gLM5gLQ0AQ0BQ0C%YI7O>7O6Q0EPQPQQ0F#s#XRL,^@PTPQQ0IPTPQQ0GPTPQPQ1_LB/^APTQ0JDBK0>DBQ0KQ0Mb:b;b<X24X34X44X=4X>4X?4Xg4132<AU>=612I>AUG<I1<HG1<0H11HG#7Q0N-0<I[[[[[[[^24^34^44^=4^>4^?4^g4P2P_Q05P]PcP`Q09P<P>P=PKPJPXPOPVO>b9bG9|C=1=C=,5CRV1{C=D]12V=Q00Q0`/2?PEP4P}P`CW,4?%0<#6P6Q0a/2<P4Pz%02S0a#6X]4RV%0eRA/1a#0%62X54P4P0112A#0#6X54P4P01102#0#6X541~40PaPREnPAPOEn%0zPeP`P3%P{12I{R{eP{%TeR{%7eQ0O#7\\[R3%Tg%7gfLRz#0RA#7\\[P{P3%LfQ0O9Rgg\b%Gg%0~R3/N3\^%I~1HAA\d%MzfMRA#:#6\P%KA%0hS0O/2h\P%:hP4Q0PP4%LmQ0Q9Rnn\b%GnQ0RQ0R'N\^%Io1Hqq\d%Mp%:r#6\P%Kr%0tS0R/2t\PQ0SP4Q0TP4%Lu%:vS0T$06Q0V60;v\b%Gvf[R3#0S0SQ0S'N\^%I3%0wR{/H{\d%Mw%:xS0Q#6\P%Kxf^Ra#0S0P/2a\P%:aP4f_S0`#0S09P4PMQ0AQ0DQ0EPQP9P:P:P;Q03#k#k#k$0URL-0A4/uW,wQJ0OQ0KQ0Mb:b;b<%6Lg00V?[P2b9bcb`bObNbMbLbWbbb_bVbUbTbSbRbab^bQbPbKbJb1bZb[b\bGPbeH0ND]PIP2EmWXP2O1PEP4P}PeCW,4<g01CIRLp4p710RWPLp4p7210RLP6\6RB%h5R@P1P=P>P5P6CW98>2Q0[=>?5A8<2>'@X0?,c?S0[[S03P>P2O1S05=>=6A8?25'@X0=,c=P?P=P>P5CW98=6RN[S0NP?P2O1=><>A8I2='@X0<,c<\NP=P>P5P6P2I0KS0JP6n2001000000120000000X75WAW@WBW8Q03^75^A@^@B^BL^8WP2PEP4P}PgPHP6O612|GA8E2~'@X0E,cEQ01PE12|KA8E2z'@X0E%0KS01#6S0GP212|JA8E2h'@P1AeDD6,5CAdDD67fC#E/2ZA8E6i%0[#6P2AeDD>,5CAdDD>7fC#E/2XA8E=lP4AeDD?,5CAdDD?7fCRN#EPV&0JNPRP6EmWeWXP6P2O2n2001000000121000000W1XkEP6P2O2n2001000000121100000bCb1WCP2O1n200100000021100011000Q04Pe1=C<S0I1=CcS0FPDPDP6P2H05=8EgP~1=C`RN1=CfRVP5P6P[P2K0IPNPVP5P6H04#;P41=CeS0B,5C15C=RN15C>RY'1S0C,?2PNP21=C~,5CS0>CQX54P2PePZEm15C59VeYPYPe1=CgS0<,5CCQP4Q0>15C?RY=VgNPYPgP2CQX54P2P~PZEmQ0C,?fPNPfP~CQPJ15C<RN/1YRY,?2PNP21=CA,5CCQX54Pz1?ZYPNPZP2CQX54P11v62%;5S0C%;6S0>'bS0?[S0@Q0>%;2'b1v56S0>[S0;Q0>%;>Q0C'b[20H62S0>P6n2001000000120000000XF7XE7Q0@^F7^E7P21?~YRYAVN~ARNP6O3%;Y%;N'b15CIRNP4PNP41162RN00Lh13Nh1<hN'bQ001156RN/3i1<iN1?OFP>POPlCQP213Fj11nm11=>RO#ERN'2PEP4P}PoCW,4NP1Q03Q0NQ0[P<P?P=P>CW98?5[Q0JP2n2001000000120000000X75XA@X@BXBLX8WQ0N^75^A@^@B^BL^8WP2PEP4P}Pp11?=R}#ERWPE11<?#ERL,2|A8E2r'@X0EPDPDPZPJH05RZAeDDZ,5CAdDDZ7fC#E/2WA8EZp%PWQ0:CxH03O6b1409AFonm,4NP}PlP6PzH0F13WlPc11poPLP1142`P6AFutrP6PoCDRW[P2AFtrpRNP2PnCD146e[RZ145f\WP]P2O1P2n2001000000120000000X04PZ^04P211I<R<#ERZ14ZN1ZZnP5P1Q0]Q0^Q0\1Z>5[Q0_P2n2001000000120000000XH4XI4Q0^^H4^I4P211HI#EPoP5O3b1CxO2b1H0R13L]RLePL&0S<13<ZP1Q0@Q0;Q0?1v>5[Q0>P2n2001000000120000000XF7XE7RZQ0;^F7^E7RLP2Q06,?eR]AVGetRN%;]RW%;NREP11?62#;1365R|[RB13261?56#;R@[Ri1?>5#;\|20E62R|P2n2001000000120000000X74X04RhPi^74^04RYP2Pf11KGRAPA%EAPfP5P>D}O3b1408O3b1c0;bvbwbtWdP2O11<jFQ001?kO#;AV=km#;1?_}P?P_PnCQP?1?l}#;P1PBPi135>\@P|P6n2001000000120000000X74X04R|PB^74^04RBP2PnP<P6O313<n15CXRX#P12IXRXePX15CRRR#P12GRRRePR11vu,SgRR#P12fRRRePR%Tv%7v%7{\\[%Tw%7wQ0P#7R{\\[%Tz%7zQ0O#7\\[%T3%73%0xRR#7\\[%LwQ0Q$06>0;xR\b%GxQ0P-0T{\^%IaQ09Q09'H\dQ0`#Mf`Ra#:#6\P%KafaRa#0/2a\P%:aP4fb#0P4%LoARppq\b%Gp1Nss\^%IrQ0RQ0R'H\d%MtQ0U#6\P%KuQ0V/2v\PQ0TP4Q0SP4fm#LfnRv%0v7Rv\b%GvfoRv#0Rs/Ns\^%IvfpRv#0Rs/Hs\d%MvfqRv#:#6\P%KvfrRv#0/2v\P%:vP4fsRv#0P4%LvftRv%0v7Rv\b%GvfuRv#0Rb/Nb\^%IvfvRv#0R^/H^\d%MvfwRv#:#6\P%KvfxRv#0/2v\P%:vP4fyRv#0P4p-0RPPMQ0A%Y6Q0DQ0WQ0D7O>7O57O>Q0EPQPQQ0H#s#XRM1_SURU'`PTPQPQ1^UMPTPQP9P:P:P;P?J0xDBDBQ0KQ0Mb:b;b<X24X34X44WfQ0X,<5Q0YP?[[^24^34^44^fPP2fkRP?Vw3PwPPf{CQPvP3PwPtPnO6b9c0Fc0Ebpbobnbmblbcb`bObNbMbLbWbbb_bVbUbTbSbRbab^bQbPbKbJb1bZb[b\c0=bGc0Ac0Bb6b1W6P2O1AV?ln#;P|PBP2PI11npRpP6O313pIPZPLP2P]PNPhPYP2PK11fuRYPY11ruPKPfPrPuPuPc&0DuJ0CP5D}O3b1:09WEO3b1b6b1W6P2O1n200100000021100011000WdP2O1n200100000021100011000bjc0<bBb6b11=Cz,5CP[D]1=CJ,5CPID]b6b6Q08Q0<P>P5H04#;eb6WCZ0GDXDDH0wQ0IQ0F5le#9Q02p4p710RDP7\2RJ%h6RzP1B02562#9A8=25Q05+0BX0>,c>R1[A8>26P5P2O1+0BX05,c5B02>56#9[REB02=>5#9\1B0v562P2n2001000000120000000WAW@W8PE^Az^@J^8DP2P4Q0a/o011gfRD/C2'J112f/Ce1=C2=l~V3aRJXi4PyP4Q0c%9J60s2X04PH14Hy%0H/o0Q0Z/CH'J11HeRy/C`Q07Q0B5lg3a#9P=Py11ceP`PHPcPePeP?&0DeJ0CP[D}13y`Q01/o0Ry11~gR[/CKR?'J11KgRg/CfRH;a2#9XD71J2??aH8#9XD71J82?aH8#9XD71J88?a28#9XD7Q0L11GfR7/CeR8%9813gf[137e%9H[1y7eP2H01Cp1CDGR2%9213[K[13DG%9?[1yDGPIH01Cp%0GRI/o0RD%9DQ0G[%6I%9y[20qI0P>H01Cp1=CG=l~VP5Cpb|CxH03O4b1PfPeP`PcH0p#9eb}bzb{buc05c06bxb]c0@c0:c01c07Y02Y03Y04W~WsY08WqY09WrXi4Z0?4Z0D4Z0>4Y0Co"). Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_sound : forall maps aZ nZ baseZ,
  higher_fit_b maps aZ nZ baseZ = true ->
  exists g, (g mod page_size = 0)%Z /\ (aZ + nZ <= g)%Z
            /\ (g + nZ <= baseZ)%Z
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01Hh11gh22Hgh31xi001xh41mh51nh61Ah72b1h82b2h91fh:1lh;2H0h<3Halh=5Hfreeh>3Hhih?3Hloh@2_HhA2aZhB5baseZhC4mapshD2nZp;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00:4j1CTg00bkj1YTg00cIj1VTg00clj2TTg00;9j1OTg01@gj4WTg01>2R1j3MTg00_Vj39Tg010gR0j2GTg01>Nj3RTg003Nj22Tg00dLj23Tg00e2j3ITg00i]j3ATg007Aj36Tg00EgR2j28Tg01Cfj2STg00Fij2;Tg00i@j2<Tg01?1j2DTg01@Gj2QTg00l:j2PTg016nj4KTg017Ij4UTg006aj2NTg01?Nj2FTg00U?R3f0R4g00U_R536p=1f1R6A6345'8p=4g0089R7,N4p=Bg009VR8,D4p=Xf2R91<64'Fp=L1296/<4p=01F96/F4p=@g007[R:/G4p==f3R;13647I9p=H1296/;4p=EAI964=635p=51;96/84p=?1864,89p=>1N47/D8p=71F64=635p=:1D68/F4p=Jg0091#C#C#C#C#C#C#YR5#VR7/T7#OP;P9P6P4CW#1P1p4p710R1P3\4R7%O6R<P2AM964#1f4R=?949P;P4O1'4X3;,G;[R>A9;46P9P4O1'4X39,G9AM;96#1R?[f5R@?94;P=P4O1'4X3=,G=\?AR964P6n2001000000120000000W:W9W6P>^:<^97^61P4P:%B4R1#XR712@=;L4A04=;f6R<1354R>135=R?3I3@RAX1:AA@=;P6O4AA<@=99:4/4AX3:#=P0P:f7R0?A<@99:412<@=L74A04@=P0P>P5P@CH3@'4X3:A6:18R1AE0<4124<f8RA135<RB75>7?@3>X1:#=P4f9R@?AA099:412A0=L74A040<1350R79I@>3@'4P2f:RC?A@A99:6%76A0@A6A06A03@PC1356P5PACH':f;RA?EC4124Cf<RD135CRE75>7?@5>1X1:#=P4AADAC99:;%7=A0DA=A0=AC3@f=RCP?P5PACH':P21:64%19RA%16R?'8[R=14?41:96R?[%1;/8A\?1S64P6n2001000000120000000X83X73R?P=^83^73R3P4%7<f>R=?0C<A0<CD3@R<f?RAPBP5PCCHRBP6O3%1</4BP2%B0A0A=0'JA00=C':f@RB135=757fAR7/2BR=/;4124BfBR<135B75>7?A5>1X1:#=P4%B@1<=@'JA0@BA':fCR@135775EP?P3P4%BDfDRE?0@D'JR7A0D@<R=P9O3%17/4=P2%7CfER=?0EC':A0CE@#1fGREfFRC'2R7/;4124CfHRF135C75>7?=5>1X1:#=P4%7A1<7A':A0BEC#1P?P3P4%7<R3fJR?fI;0<R<P9O3%13/4<P2%7@#1fKR<?0?@#1fMR?fLR@;E4124@fNR3135@75>7?<5>1X1:#=P4%7=#1A03?C#1P:fPRCfOR='2R</;4124=fQ135=75>7?35>1X1:PE%BE=6:8AE=3ER1AEE3?R?135E135355CRC'8R5'8P21D64#1A6:96[REA6:641D96#1R>[A6:;9\>1Q64P6n2001000000120000000X4:X5:PE^4:^5:P4%BFP8P9O3b0P1P5P21<64#11;96[R21;641<96#1R5[1;;9\51P64P6n2001000000120000000X4:X5:R5P2^4:^5:R2P4P<PFP6O3b0P?PCP5P2P412F=P3P0O3b0PDCKCKCKCUW?W<P6P4O2n2001000000121000000b2b0W>W2P6P4O2n2001000000121000000b2b0W=W2P6P4O2n2001000000121000000b2b0W2W@P6P4O2n2001000000121000000W0X1:P6P4O2n2001000000121100000b0b;W0XB:XD:XA:WCo"). Qed.

(* [comment removed for export] *)
Lemma no_higher_fit_iff : forall maps aZ nZ baseZ,
  (0 <= aZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (higher_fit_b maps aZ nZ baseZ = false <-> no_higher_fit maps aZ nZ baseZ).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0023 ()) [] "p'0h02Hfh15Hfreeh22H0h31bi001bh41gh51Hh64HgAlh74Hghih84Hgloh94__p1h:4__p2h;4__p3h<4__p4h=4__p5h>4__p6h?4__x1h@5__x10hA4__x2hB4__x3hC4__x4hD4__x5hE4__x6hF4__x7hG4__x8hH4__x9hI1ehJ2H1hK3H10hL3H11hM3H12hN3H13hO2H2hP2H3hQ2H4hR2H5hS2H6hT2H7hU2H8hV2H9hW4HaAlhX5HaPoshY5HbasehZ4HnAlh[5HnPosh\7__arithh]4__ffh^6__sat0h_6__sat1h`6__sat2ha8__varmaphb5__withc2aZhd5baseZhe4mapshf2nZhg1qhh2q0hi2q1hj1rhk2r0hl2r1i011xp&0p;1p;2p;3p;5p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g003Nj1ATg0043k10=Tg004Qj18Tg0050k10:Tg005Yk101Tg0067j2eTg006Xj3MTg007Aj1NTg007fj1kTg008Ij1jTg008lj2hTg009Uk209Tg00:8k106Tg00:ck500Tg00;Gj4zTg00;hj3vTg00<Ij6tTg00<mj2sTg00=Mj1fTg00=mj2LTg00>Sj4HTg00?\j21Tg00@8j4bTg00ABj3QTg00B<j2YTg00BVj3=Tg00C0j2ik30<Tg00Caj2XTg00D=j2aTg00D^k10;Tg00E7j2ITg00ETj2BTg00F1j2`Tg00FXR1j22Tg00G3j2_Tg00GZj2^Tg00H@j2\Tg00Hfk105Tg00IFj2OTg00Idj1~Tg00JBj1}Tg00J`j1{Tg00KBj3ZTg00Kej3TTg00LHj2dTg00Lkj4KTg00MVj2wTg00N8j3xTg00NWj4rTg00OIl>yTg00P[j6STg00Q7j2]Tg00QVj5qTg00ReR2j2|Tg00S?j4pTg00SZj3gTg00TCk202Tg00Toj7VTg00USj2oTg00V3j2nTg00VPj3DTg00W0j4mTg00WNk607Tg00X2j7lTg00XVj8PTf0R3#8#8p=Rg00Y:R4/h3p=<1d43p=?f1R5=g43g00YX+02p=4Ag453p=WP4P5g00ZDR6P3CKp>08f2R7g00ZkR8g00[JR9P9g00[jR:P4P5g00\JP3CKg00]1R;FVp=>P5P8P9P9P:P3P;FVp=[g00]QR<g00^1R=7=3p=Ug00^QR>/X3p=7g00^oR?,o3p=3A=43>p=51B75/X3p=:g00_gR@9=<3p=J1n3?p=@A=453p=;1X3>p=Gg00`GRA?D53p>04ADA539DA7p>03f4RBf3RCADA539DA75DA5DAp=0P4P7P5P3Cmp=CP7P8P9P9P:P4P5P6P3CKP;FVp=9P5P8P9P9P:P3J07p=EP7P8P9P9P:P5P3Flp=FPBP8P9P9P:PCP7P5P8P9P9P:P3P;FVGPp=uf6R;P8P9P9P:f5R6PBPCP8P9P9P:P7P5P3GPGPp=cP;P8P9P9P:P6P8P9P9P:PBPCP7GPP5P3GPp=6g00a3RD#ARE#ARF#ARG#A#A#A$0=g00aXg00b6RH#8RI#8RJ#8RK#8#RRL#8#RRM#<&0:4RN&01D,e4RO%<L5M4PN%8MRM#8RL#<9M4OPN%<MPN%8L#RRL#8RM#8RP#<9M4OPN%<MPN%8P#RRP#<PN%<JPN%8P#<PN%NF#?%k4RP%?FPP%NDRF#A#A#?PP%NERJ#N#?PP%NF#?PP%?GPP%AJ#?PPf@RP#jP0f?R0,4PPAfARJ/40PA140PPAfBRM,4PPA%<LRLfCRQ'4RRPAPRPAfFRS/4MPAPRPAfERRfDRT'4PAfHRU,4TPA14RSPAfIRV,4SPAfKRW,4SPAfGRX/4WPA%<K9M4O1h4HRH,WX'WPN%<I/WH,4UPAfORH,4UPA14VHPA2094>RI-08V&064RNfJRX=>NIPNP8P9P9P:I00RKA>NIWPKfPRY/4;PAP4POPD1e4>Cz9v4G=M4LfTRLf7RG'W'4PAPNP8P9P9P:1[NBEtPK1sUU#ff\/L3PWPBPCP7P3CH#Up-0RU%7B11>B%3;#5RKg00bU,16f;R8f:ROf9RZPGCbR[\6POPZf8R\P;CbR]P;[f<R^ff/L3;QZP<%35#5f=R_?:^7A:C_8PCP<1Y<3R`A=<B3P<A=<;3%U5Ra]1P5%J6A=<@=RbP<PQPMPJP0CH%U3X3<P\P@PQPMPJP0PG1iJ?%7J1X>?Rc%3Q#7[[f>Rd:0<Q?%3T#7\c1iZ?%7Z%38Re#7\c[1aO?A=4?>Rc$0;Rf%@8,I?/Be,;8[1`8?11>?Re%3^Rg#711g?'2[1_^?11?>Rg%3_Rh,1?%Gh'2[1^_?%@d#5\c1\d?%30/;0\c%@0P4%3PP4fLRh/a?fMRi%@i,I?%3i'B';\f1`i?fNRj#3Rk#711k?'2\e1_j?%3HRk,1?%Gk'2\g1^H?%@Y#5\c1\Y?fQRH#3/;H\c%@HP4fRRH#3P41aH?fSRH%@H,I?%3H'B';\f1`H?%3LRf#711f?'2\e1_L?fURe#3Rf,1?%Gf'2\g1^e?fVRg#@#5\c1\g?fWRf#3/;f\c%@fP4fX#3P4p+01DRfp+01CRcp+01BRkp+01ARlp+01@Rmf~RnPcPfPff}Rof|RpPmPlf{RqPoPfPfPoPqPlfzRrfyRsPoPfPfPcfxRtPrPlPkPcPfPfPcPkPlfwRufvRvPcPfPfPop+01Op+01QRw'4PuPlPqPoPfPfPoPqPlPmPpPoPfPfPcPnPmPlPkPcPfPfPcPkPlPmPnPcPfPffnRxPxPmPlPxPxPfPfPxPxPlPuPxPxPfPfPcPvPuPlPkPcPfPfPcPkPlPrPtPcPfPffmRuPuPrPlPuPuPfPfftRvPvPlPmPvPvPfPfPcPnPmPlPkPcPfPfPcPkPlPmPnPcPfPfPvPvPmPlPvPvPfPfPuPuPlPrPuPuPfPfPcPtPrPlPkPcPfPfPcPkPlfsRyfrRzPcPfPfPxPxPyPlPxPxPfPfPxPxPlPmPxPxPfPfPcPnPmPlPkPcPfPfPcPkPlPmPnPcPfPfPoPpPmPlPqPoPfPfPoPqPlPyp+01MR{/4wPoPfPfPcPzPyPlPkPcPfPfPcPkPlPrPtPcPfPfPoPsPrPlPqPoPfPfPoPqPlPmPpPoPfPfPcPnPmPlPkPcPfPuPuPuPuPvPvPvPvPxPxPxPxPxPxPxPxPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPuPuPuPuPuPuPuPuPvPvPvPvPvPvPvPvPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPvPvPvPvPvPvPvPvPuPuPuPuPuPuPuPuPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPuPuPuPuPvPvPvPvPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPuPuPuPuPuPuPuPuPvPvPvPvPvPvPvPvPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPxPvPvPvPvPvPvPvPvPuPuPuPuPuPuPuPuPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPvPuPuPuPuPvPvPvPvPxPxPxPxPxPxPxPxPuPuPuPuPvPvPvPvPxPxPxPxPx&05A-04x:03xxD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0%fA1O4;1O4O7CB1O4\%~4RA7CO7C71O4G?COA1O4Z?C6A7CC7C5%}4PNPN1[NyRy%{9R9%?ERE99N{P9PNPNPyP9p+01LRA=9NIP9PNPNPzP9p+01NRv=>N{1EN^5FNP9PNPNfqRfP91EN_A>N{v5FNP9PNPNPxP9AZ4vA=T4{99NEP9PNPNPyP9%?FRF1d4DRD59NP9PNPNPyP9p+01KRA=9NIP9PNPNPzP9A>NvF1ENd5FNP9PNPNPfP91EN0A>NFv5FNP9PNPNPxP9AZ4vA=T4F99NDP9PNPNPyP9p+01JRAp+01IRc59NP9PNPNPyP9p+01HRy=9NIP9PNPNPzP9A>NvA1ENP5FNP9PNPNPfP91ENJA>NAv5FNP9PNPNPxP9AZ4vy=T4A99NcP9PNA9NAIP9PNA9N{IP9PNA9NFIP9PNA>NIEP9PNP4PIg00cNRFPDCK,[NP9PNP4PIPFAT4DECKDuFcFcF6F6F6F6F6F6F6F6F6F6F6F6F6F6F61wN:P3P71Y<@Ax4>5Crb]babbX?4XA4XB4XC4XD4XE4XF4XG4XH4X@4X9UX:UX;UX<UX=UX>U%5;1;B7[%5G%58RN[11\>11Z;/2_[11>Z11GO,20[%5Og00d5R:[1I8d/B\,;;[1;\;\N%5^%50RN[11_>11dO/2T[11>d1180,2S[P:\N1IPM/B^,;O[%5P1;0P[%5J%5QRN[11M>11QJ/2W[11>QR>11MT,2i[%5TP:[1IRS/BQ,;T[%7Q1BTR#7[\>\N\N\N[[[[[[[[[[[[[[[^?4^A4^B4^C4^D4^E4^F4^G4^H4^@4^9U^:U^;U^<U^=U^>UP3%70%G0%7\%G\%75%G5P7PZPPP?PYP0P5P\fZf[PCPBP6P;PGPOP8P^P_PdPJPMPQPTPRPjPHPLPePgOTb\blbibNbMbLbKbVbkbhbUbTbSbRbQbjbgbPbObJb2b5b^b_b`P^P8POPZP6PBPCP3M>yESPbP<P@P<PUP3g00dRRgP:n0110000020000XI<g00dnReP=P3ESP:1]:3RLb5b0']W1%U61Y<=RHW1n0110000020100P3O1b1b3W7W8W6aX44P[eX06P8POPZPGCHP<P`P^P8POP\CH==<3P<PdP_P^POCH==<3Pa]0P5P_P^P8PZCH#JPdP_P^POP3Dq%33#5RaA:d_3A:3_8fi/L3=Q0^#J'2'2'2X44,|4P2P4A:0d3A:3d^fj/L3=QP_#J'2'2,2aX44P:P3PaPU1Lu5=QQPP<%J3RuPUA:CQJ/23PUA:RTB/23PU12B3P1P6P5P:P3P1A:WXOP;P:P3A:ih^P1A:djhP8P:P3A:PYjP<PPPuX3<P3P=PVPMPZP6P5O4ESA=<=@P<P=P<PUP3P:Pgn0110000020000XI<PeP@P3ESP:PLb2b1X1dW7P5P3O2n2001000000120000000X2ZW8P5P3O2n2001000000120000000X2BX6GP5P3O2n2001000000120000000W2aaaaaX44P5P3O2n2001000000120101000b0,]bW0PHX0\n0110000020000P3O1b0b3X5]CpWYXZKWWW[WXaXd4aXf4Xc4Weaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition search_candidates (maps : list (word * word)) (loZ : Z)
    : list Z :=
  loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                        + bv_unsigned (snd p))%Z)
             maps.

(* [comment removed for export] *)
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
    : bool :=
  (g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
    : option Z :=
  find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

(* [comment removed for export] *)

Lemma place_sound : forall maps loZ hiZ nZ a,
  place maps loZ hiZ nZ = Some a ->
  (a mod page_size = 0)%Z /\ (loZ <= a)%Z /\ (a + nZ <= hiZ)%Z
  /\ region_free maps (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh12Hfh21mh31nh42b1h52b2h63Halh75Hfreeh83Hhih93Hloh:2_Hh;1ah<3hiZh=3loZh>4mapsh?2nZp;1p;2p;4p;3p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g00:4j1;Tg00bkj1RTg00cIj1MTg00clj2ITg00;9j1QTg01DGj1PTg01Dij4OTg01Ekj2LTg007Aj39Tg01FMj4Jj5ETg01GTj2DTg01Hbj5GTg00_Vj3@Tg00Fij23Tg003Nj22Tg00dLj21Tg00e2j38Tg01?Nj2BTg00EgR1j27Tg01Cfj2KTg00i@j25Tg01?1j2ATg01@Gj2HTg00l:j2NTg016nj4CTg006aj2FTf1R0g00U?R2f0R3g00U_R439'7p==A9234p=0g0089R4,F3p=:g007[R5g009VR6793p=<f2R7/30/73p=>1703,77p=?1F34/A6p=61503,B7p=4g0091#;#;#;#;#;#;#RR4#MR8/I8#Q%P5f4R8f3R9P7P0CO1L5339P5f5R:P8P9P7CJ1D:8R;P0P3DGA@50;P:P8P9P7P0DE'=P1f6R;/D:9@57P;P:P8P9P7DE#0%:9#<13;91298f7R<1149114838#07>:3?P3f8R=/D<9@58f9R8P=P<P;P:DE#0P11B03#0%07R:%00R;'7[R>1=;31B70#0R;[%09/7:\;1K03P0n2001000000120000000X52X42R;P>^52^42R2P3%6<f:R>;4<12<=;48R:f;R?114<114=R@38RAP0O3%0:/=AP1%6=?4?=12=8;4>#0f<R=1148RA78@#0%:8#<13=8128>f=R8114>78A#07>?3?P3%6>?48>12>?;4=#0f?R>114?114=38#0P;P2P3%68f@R?;48RAf>R@,28/5>R8P7O3%0A/=8P1%6@fAR8;4@#012@>/5?#0%:>#<fBR@/3>12>?fCRA114>114?38#07>83?P3%6??4A?#0128@/5A#0P;P2P3%6AR2fFR;/5ARAP7O3%02/=AP1fDRA#6#0fGR2/5A#0fERA#:#<fHR@/3A12A;fIR8114A114;38#07>23?P3%6;#0fJR;/52#0%:@#<fKR2/3@RA12@8/3;R?fLR>114@114838#0R4'7R@'7P11A03#0A9570[R:A95031A70#0RB[A9597\B1H03P0n2001000000120000000X25X35P:^25^35P3%:8P6P7O3b0PAP@P11503#01370[R113031570#0R@[1397\@1N03P0n2001000000120000000X25X35R@P1^25^35R1P3P>P8P0O3b0P?P4P@P1P3128;P2P<O3b0P=CCCCCCW9W6P0P3O2n2001000000121000000b1b0W8W1P0P3O2n2001000000121000000b1b0W7W1P0P3O2n2001000000121000000b1b0W1W:P0P3O2n2001000000121000000b0W0X;5X?5X<5X=5W>o"). Qed.

(* [comment removed for export] *)

Lemma existsb_find : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, find f l = Some x.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01xh12Hyh21lh31Ah41Hh52H0h62IHh72_Hh81bi001bh91eh:1fh;1yp;1p;3p;2p;6p;4p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p200R1g00^VR0p4p710p8P1g01>2R2p4p710p8g00;9j17TP2j35Tg01DGj12Tg01I@j36Tg01Ekj21Tg007Aj30Tg010gj24Tg010Kj6>Tg00LJj1=Tg00_mj2<Tg00:Yj19Tg00?Tj2:Tg01IYj28Tg017Ij4@Tg00Jnj3;TP0j5?Tg00U?R0f0R2g00U_R330p=3P0\2f1R4#7f2R5%75f3R6?552#3f4R7f5R8#2R9A68751182R:30X07'4[W2g01B0R;=003P0P;P0p-0P2g00V?R<g01J6n0110000020000X90g01JRP3P2E>P<%=8=09:X07,47/<2b5W4%959554#3%27%979676117230X06,46[e%76A5762#3f6R:#2A6:8511:230X08,48[P7P5O1P01:02P8P6O1=002P0f7R9P8O1=002f9R<f8R=;58,84#3f:R>f;R?#2P0f<#2P611?=A6?>9n010000002000011?230X0>'4[]1P4P:P7O1R?#3A5=97R=,83#3P<%2>R311>911>2R@30X0<P:%2<11<:':C@W7W1A00?;P618;=#3A6><:=03@X0<,4<[eW1n0110000020000P2O1b1b8A;8549587#3%29A;976969:119230X0:,4:[eW6W2X;5P2D?W2W:X31o"). Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_as_place : forall maps loZ hiZ nZ,
  higher_fit_b maps (loZ - nZ) nZ hiZ
  = existsb (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01gh14__x1h24__x2h31Hh47__arithh54__ffh68__varmaph75__with83hiZh93loZh:4mapsh;2nZh<1ph=1zp;1p;2p;4p;3p;7p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g002UR1p4p710p8P0g0031R2p4p710p8P0P2p4p7210p8p101Jnp4p710R0p100^Vp4p710p8P0g01>2R0p4p710p8g00:4j11Tg00bkj1XTg00cIj1ETg00clj2ATg00;9j1>Tg00:Yj1PTg00KNj2JTg00;Yj1DTg00Klj4CTg00<7j1BTg00<Uj1@Tg00N5j2:Tg00O_j3?Tg00O<j3WTg00=cj4UTg00Pej7TTg00?2j2OTg00?Tj29Tg00?nj2NTg007Aj33Tg00@Zj3ITg00A9j4HTg004Ij26Tg003Nj22Tg006aj2FTg01?1j2GTg00i@j24Tg01?Nj20Tg00dLj27Tg00e2j3;TP2j3KTg00ggj2<Tg00o2j3LTg005cj1MTP1j4=Tg00Jnj38TP0j35Tg010Kj6QTg01@gj4RTg01FMj4STg01GTj2VTg0091R0#1R1#1#1#1#1#1#XR2#ER3/A3R4#>g007[R5g00SlR6#P%>6P5f2R6,J5f1R7%D5CC%B5%@5R8g00Qmg00RLR9P9g00RlR9P51:50R0g00TX1:51R19?50=W51CUg00SLFT1O89f0R9P6g00U?R8g00U_R1'91N96=381dg009VR1=I57CHb5b6b7X15X251697/279359^15^25P9P7f3R0O2b41669R:/299356P5P0g0089,F9/G1R11479'01290f4R;'4R<'0f61729R=17203;R>'0X05P4P5AK339,<2AL339,<2'2#MX<4R3f5R?C=R@985955514?9,01/0</0>X05A85;@555538X=514;9,011296/40'017269;?='0X05P4P5P3P;C=9850555,981607/27P9EQb3P0P:P9P7CRP0P6P7P9CS1V06555538eX;5X85W9W:o"). Qed.

(* [comment removed for export] *)
Lemma place_complete : forall maps loZ hiZ nZ g,
  (0 <= loZ)%Z -> (0 < nZ)%Z ->
  (loZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (hiZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z -> (loZ <= g)%Z -> (g + nZ <= hiZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place maps loZ hiZ nZ = Some a.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h04__x1h14__x2h21zh31Hh42H0h52H1h63H10h73H11h83H12h93H13h:2H2h;2H3h<2H4h=2H5h>2H6h?2H7h@2H8hA2H9hB7__arithhC4__ffhD6__sat1hE6__sat2hF6__sat3hG8__varmaphH5__withI4__x3hJ1qhK2q0hL2q1hM1rhN2r0hO2r1hP5HfreehQ4HgAlhR4HghihS4HglohT3HhihU4Hlo0hV5HloalhW2HnhX4HnalhY1bhZ1gh[3hiZh\3loZh]4mapsh^2nZp;1p;2p;3p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8g01JnR1p4p710R0p100^Vp4p710p8P0g01>2R0p4p710p8g00:4j17Tg00bkj1nTg00cIj1VTg00clj2TTg00;9j1MTg00EKj21Tg00Fij23Tg003Nj29Tg00dLj2HTg00e2j3NTg01FMj4kTg01GTj2cTg004Ij2:Tg01@gj4[Tg00Bij2Jj3YTg00Akj2CTg007Aj3<Tg00DKj1UTg00BLj2ATg00Ddj2?Tg00Egj28Tg00FBj2>Tg00GEj2ETg00Gkj2DTg00:Yj1STg00KNj2ITg00;Yj1RTg00Klj4GTg00<7j1OTg00<Uj1PTg00=@j2QTg00N5j2@Tg00LJj1mTg00O_j3lTg00O<j3jTg00?2j2hTg00?Tj2KTg00?nj2bTg00@Zj3^Tg00A9j4]Tg00aYj6BTg01L7j3\Tg00MPj1_Tg01LWl>`TP0j3aTg01Mij4ZTg010Kj6dTP1j4eTg006aj2XTg004fj2fTg00=cj4gTg00Pej7WTg00QIj8iTg009VR1f0R0'3p=2g0089R2,X0p=0g007[R3?<01p=5g00U?R4g00U_R57<0p=F1f02p=4f1R6=<30p=6P3P6g00XNP0Cgp=;P6g00QmR7g00RLR8P8g00RlR9P0g00SLFWp==f3R:P7P8P8P9f2R7P6P0Gip=Lg0091R;#7R<#7#7#7#7#7#nR=#VR>/T>#M%2:1117f5R>#0#5R?f4R@#0#5f6RAg01BP'1f9RB/3Af7RCf8RD'9/3Bf<RE1H=D1H=B3N#FP3f=R=PEf;RDf:RFCkRG1c=ERHP4P=1:EFRIPFPDC[%F0XY4P=PIPFPDPB1JF2RJ%2F1312RK%0ERL#2[[RMAY=2BRBf>RN#0RO#2RP\KRQ1JD2RR%2D%0=RS#2\K[RK1CE2RTA<321RU#URV%4=,A2/9S,6=[RS1?=2RW1112RX11O2,8P[RP1>N2RN1121ROf?RY#0RZ,1213Z1'8[RZ1EY2RYf@R[#4#5\UR\1D[2R[fAR]#0/6]\UR^%4]R]P3fB#0R_P3fF/C2R`fGRa%4a,A2%0a'9'6\VRb1?a2RafHRc#0Rd#211d2'8\XRd1>c2RcfIRe#0Rf,1213f1'8\ORf1Ee2RefJRg#4#5\URh1Dg2RgfKRi#0/6i\URj%4iRkP3fLRl#0RmP31Ci2Rn%4l,A2/9m,6l\VRV1?l2RlfMRo#0Rp#211p2'8\XRX1>o2RofNRp#0Rq,1213q1'8\ORO1Ep2RpfORq#4#5\URr1Dq2RqfPRs#0/6s\URU%4sRsP3fQRt#0RuP3g00SlRv#SRw%MvRvP31I37RxP6%R3CG%O3Ry%P3Rz1Q31R{1@3;R|';,=z%m8R81@3<R<9l3|=j3<R<,;{,=zCL1hz9R9P0P71K451b07#FdA^316C]R5bCbGbHX03X13%201:67/97R4#2[^03^13P0fSR{fUR}PtO3bBbObLb9b8b7b6bAbNbKb@b?b>b=b<bMbJb;b:b5b4b3bDbEbFPCP3%0FRC,:L#0%50X23P3P1%0D,:0#0#5X23P3P11:10#0#5X231K31PCP>EBPLPAEB%0IA\EF2EBP>P@P:PJPMPBPQPRPKPTPSPWPPPNPZPYP\P[P^P]P3P_P3P`PbPaPdPcPfPePhPgPjPkP3PmP3PnPVPlPXPoPOPpPrPqPUPsP3PuP3PwPvP3PxP61I3:CGPyPz%_;,@3R;,;|,=zP81;<;,=zCLP9P5bCbGbHX03X13XI31307134:[^03^13^I3P0fRP{P}PiO4bBbObLb9b8b7b6bAbNbKb@b?b>b=b<bMbJb;b:b5b4b3bDbEbFP6P0M>`Aa3GHP=PEPDPFCZEdCeWPWRWSXQ?WTWXWVWWWUXZ3X^3X[3X\3W]o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

(* [comment removed for export] *)
Lemma place_in_model_admissible : forall h nZ a,
  (0 <= nZ)%Z ->
  place_in_model h nZ = Some a ->
  bv_unsigned (Z_to_bv 64 a) = a
  /\ (bv_unsigned (Z_to_bv 64 a) mod page_size = 0)%Z
  /\ (0 < bv_unsigned (Z_to_bv 64 a))%Z
  /\ (bv_unsigned (Z_to_bv 64 a) + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h02H0h14__x1h22H1h32H2h42H3h52H4h62Hah77__arithh84__ffh94__p1h:4__p2h;6__sat0h<6__sat1h=6__sat2h>8__varmaph?5__with@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1qhF1rhG1zhH1HhI3HalhJ5HfreehK3HhihL3HlohM2HnhN3HrthO4HtophP1ahQ2a0hR1hhS2nZp&0p;1p;2p;3p;6p;4p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g01DGk10DTg01O;k206Tg01Ekj2sTg007Aj3>Tg00:4j1NTg00bkk105Tg00cIj1yTg00clj2uTg01PFj14Tg01Q>j6mTg00Fij26Tg003Nj2=Tg00dLj20Tg00ggj2ITg01RFj1xTg00EKj22Tg00fUj2vTg00Bij2aTg003kj1VTg01SAj2qTg01Sij2hTg01TFj3oTg00Akj2\Tg00DKj1nTg004fj2HTg00BLj2STg00Ddj2[Tg00EgR1j23Tg00FBj2lTg00GEj2kTg00Gkj2iTg00HQj19Tg00ZOk10CTg00Zmk20BTg00[Nk30ATg00IYj3JTg00JBj2YTg00I0j2gTg00:Yk10>Tg00;9k10;Tg00KNj2PTg00Klj4XTg00;Yk10:Tg00<7k109Tg00<Uk108Tg00MPj1cTg00N5j2ETg00=@j2RTg00LJk107Tg00>Nk604Tg00PBk303Tg00O<j3`Tg01Tjj3{Tg00?2j2zTg00?Tj2_Tg00?nj2wTg00@Zj3}Tg00A9j4~Tg01UMk100Tg00elk101Tg00g;j3tTg00hQk202Tg00aYj6jTg016nj4QTg01Ukj1^Tg01Vej1dTg01W[j3]Tg006aj2fTg00e2j3eTg00Jnj3UTg00=cj4WTg00Pek70<Tg00QIj8ZTg00Llj6pTg00NXk70@Tg009VR0f0R2'6p=8%N2#Np=Mf2R3f1R4#^%d23]p=rg007[R5g0089R6,f2;>0p=?g00U?R7Ae342g00U_R83>p>0?1634/32p=A1342,33p=<f4R9f3R:#^%d33]?e42=>78p=7A>542p=51202p=:1=34/62p=@1f26p=;A>520p=D1g52p=Gg00SlR;?U42p>0=AU;429U;3p=BP5P4g00TXP2CWp=LP4g00QmR<g00RLR=P=g00RlR>P2g00SLK0<p=1P:P<P=P=P>P3P4P2GZp=FP5P4g00V\P2CWp=CP4P<P=P=P>P2Epp=bP3P<P=P=P>P4P2K0@p=TP5P4g00XNP2CWp=Of6R?P<P=P=P>f5R@P9P:P<P=P=P>P3P4P2GZGZp=KA>728p=|g01X8%84RA&0D5206:31s543>g0091RB#NRC#NRD#M#MRE$05RF#yRG/uGRG?r99RHP6%49RIP:P3P2Em%?316631=3:10F310F:RJ60?H7AI3<P1%?:1=:9%4@PGP@P@PJ10F9RJD73A9A6:1IFJRI/59%?I%:I%4?9@I@PGP?P?PJ10F@D73<3<P2%?@f7RJ,=?RIf8RH#4PGPHPH10F?10FJRKD73A9A6?P1166J1=JHf9RL#4PGPLPLPK10FHRKD73A1IFKRM/5H%?M%:Mf:RN#49@MLPGPNPNPK10FLD73<3<P2166Lf;RK,=Nf<RM#4PGPMPM10FN10FKROD73AP1f=R1#49@KMPGP1P1PO10FMROD71IFORP/5M%?P%:Pf>RM#49@P1PGPMPMPO10F1D73<3<P2f?RO#49@1MPGf@RPPP10FM10FOD7fARO#x%4Og01BP'2P51vFP152OXG51aP6%8PRM1606RQfBRR#;#8[[%VCRS%VERT'qRU%:S%8T1hSTRV#:[[RW%8SRXg01J6RYAoST4UW6RT%8V\Y^6XRXfCRY/\6A>560RZ#nR[fDR\1H\6,S6%;\'='5[1[\61206R]fER^#;R_#812_6'3[1l^61260R`fFRa#;Rb,2616b0'3[1ka6fGRc/H6#D\Z1ic6fHRd#;/5d\Z1Hd6ReP5fIRf#;RgP5p-0Rhg00WCRi#9Rj#9#9#9Rk#9Rl#9Rm#9#9#9Rn#G&0CB-0B5%Gm60A5Rm5J5g00WbRo'Y%Gl%Gk%Gj1g5i5J55J55J5/YoRi%9n#G=J5m/Yo&0>;Ro-0=i9Bii9Bii9Bii9Bii9Bii5Bi3B&0;;R;P5P51P59P31P5?CXP4P51P5@P:&0:5CXCX&095Ri&085RmPm%cC,E5Rn1R50Rj'L,1mRk&07=Rl%cBRp,E5Rq1E5BRB'L,1mCFPlPmPmPkPl%Np,E5Rp/Lj,1mCFPlPmPm1Cnj,1mPl1Cnq,1m1bmH5TmCFPlPmPm1Cjn,1mPl1bmL1Cqn,1m5TmCFPlPmPmPmP<P=P=P>PkJ04PlB035np=`5q,LB,1mCFPlPm1E5DRD1R5S={5FRp'C,1mPlPm1E5CRC9`5B/OD,1mPlPm%ME#M#M#VRE,R5/OB,1mRDPlPm1Lqj,1mPlPm1OjC,1mPl1OjB,1m1CBp,1m5TmFKFKFKFKFK1zm>R>P2P31_781w23#|dA}504C~R8b8b>b?X15X@5XA5XB5XC5XD5X9hW:%D915:4[%D@%DJ[12?012J@/3L[%:J12?H,3K[%DHg00V?[1SLN/=J,5@[12HV16IL16EJ%DN%8NRL12NV,3L[[[[[[[[[[^15^@5^A5^B5^C5^D5^9h^:hP2PA1640P3P6fM#4P4fLRAfKP:P9P@P?PJPKP1POP^fJR1OBb7bFbEb5b4b3b2b0b;b<b=&00F,hS,2P,3Me&01F,2P,3Me9tFP10FP,IFRM202FPEj15MPP5PO152R%?2%:2%4\9@2YPGP\P\10FRRM10FYD73<3<XG515OO%?ORP%:ORS%4Y9@ORRJPGPYPY10FORGPMD7RM'3R?'3R@'31_5OPPP@PKPSP?1aO6%8O%;Y#8\Q[PUPWPTPX1\\61H^6,S6/=_,5^\[1[^6%8b12b6'3\]1la6%;cRa,2616a0'3\`1kc6%De\Z1id615gf\Z1Hf6P5%;1P5PoP;1P54PiPmPDPl1CjB,1mCFP>P8b8b>b?X1516E2%:4[^15P2PAPRO2b7bFbEb5b4b3b2b0b;b<b=PJPMP:P3CQCQCQCQ1IFGP2EjbNbOWJWKP4P2O2n2001000000121000000W0WLP4P2O2n2001000000121000000W0WIP4P2O2n2001000000121000000bQWHWMXP5XS5WRo"). Qed.

(* [comment removed for export] *)
Example place_accepts_a_negative_length :
  place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;3p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g01DGj1>Tg003kj13Tg01Ekj22Tg00?Tj2=Tg00bkj1;Tg00cIj1:Tg00clj24Tg00:Yj15Tg01Xoj36Tg01YRj57Tg00ZOj18Tg01O;j29Tg007Aj3<Tg00:4j11Tf0#1#1p=0g007[R1#>R0g0091#0#0#0R2#0#0#0R3#3,21R1'=%;2R2#:R4/44#5R4P4g009VR4g01JR562R2P2P4D7%83'9=<01do"). Qed.

Lemma place_in_model_complete : forall h nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (g mod page_size = 0)%Z -> (page_size <= g)%Z ->
  (g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h)
    (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place_in_model h nZ = Some a.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh12H0h22H1h32H2h42H3h52H4h62H5h72H6h82H7h92H8h:5Hfreeh;4HgAlh<4Hghih=4Hgloh>2Hnh?4Hnalh@7__arithhA4__ffhB6__sat0hC6__sat1hD8__varmaphE5__withF1ahG1ghH1hhI2nZhJ1qhK2q0hL1rhM2r0p;2p;1p;3p;4p;7p;>p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g00EKj23Tg00Fij21Tg003Nj28Tg01PFj1CTg00bkj1VTg00cIj1UTg00clj2OTg01Ukj1<Tg01Vej1:Tg01W[j39Tg00dLj2FTg00e2j3^Tg007Aj32Tg00Bij2XTg00Akj2BTg00DKj1WTg00BLj2@Tg00Ddj2ATg00Egj26Tg00FBj2?Tg00GEj2>Tg00Gkj2=Tg00:Yj1TTg00;9j1QTg00;Yj1NTg00<7j1MTg00<Uj1LTg00=@j2DTg003kj1KTg00=cj4JTg00Pej7ITg00?2j2PTg00?Tj2;Tg00?nj2HTg00@Zj3RTg00A9j4STg006aj2GTg01RFj1`Tg01ZIl>_Tg01DGj1]Tg01O;j2\Tg01Ekj2ZTg010gj2YTg00:4j1ETg004fj2[Tf0R1g0089R0'Gp=0g007[R2g009VR3721p=7%E1#Ep=51[10p=4g01X8f1R4,33f2R5#0#7R6f3R7,10f4R8f5R9'8f6R:#C'1g00U?R;g0091#5#5#5R<#VR=#UR>/O>R>f7R?#<%:?391F=91F=:3^g00U_R=32f8R@#<%:@59>P0%C@P?P:1X?0R:113?1130R?f9R>#0RA,13[[RBP:PB1B@0A2203RB#WR:%4>,@0/8A922>[1A>01330RAf:RC#0RD,1313D0'6[1?C01303RCf;RD#0RE,3011E3'6[1>D0f<RD#4#7\B1=D0f=RD#0=22D\B%4DP2f>#0P2f@/B0fARD%4D,@0%0D'8522\:1AD0fBRD#0R:,1313:0'6\A1?D0fCRD#0RA,3011A3'6\C1>D0fDRD#4#7\B1=D0fERD#0=22D\B%4DP2fF#0P2g00SlRD#T%QD%N2%M2%L2RDg00Qmg00RLRBPBg00RlRBP21D23g00XN%5<#5#5#KR<,D2CJg00SLFI1PDBP1P51;;=1H15=2;=dAR234CSbAbDbE113<P1b@bMbKb9b8b7b6b5bLbJb4b3b2b1b0bBbCP?eP91;231G00#7eP8%`@P7P5P4P1M>_%]21\>@1Z2132XF2,Y2eW:W<W=X;6W?W>XG2XI2WHo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition witness_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)].

(* [comment removed for export] *)
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

(* [comment removed for export] *)
Example place_skips_the_occupied_floor :
  place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g01DGj18Tg00MPj17Tg003kj12Tg01Ekj26Tg00?Tj25Tg01Dij44Tg007Aj33Tg00:4j11Tf0#1#1#1#1p=0g007[R1#8R0g0091R2#7#0#0#0#2,61R1'5g01[Tg0089g01\_%02#0#0#2C4=301do"). Qed.

(* [comment removed for export] *)
Example place_complete_premises_are_satisfiable :
  (0 <= page_size)%Z /\ (0 < 4096)%Z
  /\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
  /\ (demo_top < two_pow_64)%Z
  /\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
  /\ (12288 + 4096 <= demo_top)%Z
  /\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h07__arithh14__ffh28__varmaph35__with41zp;1p;2p;3p;4p;5p;6p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g00MPj16Tg00:4j10Tg003kj18Tg00Fij25Tg00EKj2;Tg006aj27Tg01Sij2GTg003Nj2ETg00bkj1DTg00dLj2CTg00e2j3WTg007Aj3@Tg00Egj22Tg00:Yj1BTg00;9j1VTg00;Yj1UTg00<7j1TTg00<Uj1JTg00=@j2<Tg00?2j2ITg00?Tj2>Tg00?nj2HTg00@Zj3KTg00A9j4LTg00O<j3FTg016nj43Tg00cIj1MTg00clj2NTg01Xoj3OTg01YRj5PTg01PFj1QTg01]dj5RTg00aYj6STg00=cj4YTg00Pej7XTf0R1#6#6#6#6p=:%01#0p=A%01#0#0#0p=1g007[R0g009VR27@1p=9f2R3f1R4/21'2p=4P0P4g00XNP1CYp=?P4g00Qmg00RLR5P5g00RlR5P1g00SLFXp==P0g0091R6#6R7#6#:#:#:#0#:#:#0#A#1#1#1#1#1#8R8%06R6#0#1R9#A#1#8R:,52R;1;2:R<17::#9R=%86%89'GR6,;1%17#1#1#8R7/7:#9R>15:7R?1E7:R@/51g00U?RAg01[T%D9R9/C71C9:3Wg00U_RB3@RC343474=34X40P;1;86R615@8RD/2CRE,2?RF,2>RG'2RH,2=RI,2=RJ,2<g00SlRK#BRL%VKRK%U0RM%T0RN%J0RO1<021<0:RP'?'=1IO5R5P1P31>ABRQ1H13=@ABdAK024CLR4b1b2b3P;P1b0P<PJg01^eg01_K'>RJP=PI1>02RIP=PHPIP6PGPJP>PFPIP?PEPLPKPMPN1<07RE,?P,=OP5P4b1b2b3P?P1b0PDPCPLPKPMPNAF0EP1<08'?,=OP5P4b1b2b3PDP1b0PQC3C3C3C3C3C3C3C3%M9RQ/NQ#BRQPQg01JR9O92R9P9P2DP#QPQPQP9P9P2DRESg0089R9,521799#917:9#9g01\_R:g01BP';1779#9159715@:;4C343474<eo"). Qed.

(* [comment removed for export] *)
Definition full_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
  place full_ledger page_size demo_top 4096 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p10031R1p4p710p8P0P1p4p7210p8p101Jnp4p710R1p100^Vp4p710p8P1p101>2p4p710p8g01DGj17Tg00LJj16Tg00?Tj22Tg003kj15Tg01Dij44Tg007Aj33Tg00:4j11Tf0#1#1p=0g007[R1#7R0%61R1'2g01`1g0089g01\_g0091#0#0#0#0#0#0#5C4=301do"). Qed.

End PlacementSearch.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State StackLayout Run. From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall Uapi. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
Module AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.PlacementSearch.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

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
  intros h aZ nZ HaPos HnPos HaAl HnAl. unfold placement_ok_b, placement_ok.
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as [_ Hbase].
  assert (Hb : bv_unsigned (vm_mmap_base h) < two_pow_64) by (unfold two_pow_64; exact Hbase).
  rewrite orb_true_iff, Z.leb_le, negb_true_iff.
  rewrite (no_higher_fit_iff _ _ _ _ HaPos HnPos HaAl HnAl Hb). reflexivity.
Qed.

Lemma placement_ok_b_of_floor : forall h aZ nZ,
  bottomup_floor <= aZ -> placement_ok_b h aZ nZ = true.
Proof. intros h aZ nZ H. unfold placement_ok_b. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_of_floor : forall addr h aZ nZ,
  bottomup_floor <= aZ -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. destruct (w_is0 addr); [now apply placement_ok_b_of_floor|reflexivity]. Qed.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.

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
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.

End AsanCeil.
