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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_alloc_meta () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~K47Corelib4Init5Logic2eq01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta6magreeC13~~~I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree;pres_exceptC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:F_syscalls5asegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B29wview_extC13~~~K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3ivlC13~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03c:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta2A28agree_onC13~~~c:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta2A2>rw_cells_agreeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem>bytes_at_boundC13~~~c:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta2A2>bytes_at_agreeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~c:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta2A2;wr_at_agreeC13~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7am_takeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_A7am_tookC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocIset_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8a_nslotsC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6a_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K8carve_stC13~~~C35stdpp4base6lookupC35stdpp4base6insertI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_F@carve_st_regionsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocAregion_live_rangeC13~~~C35stdpp4gmap9gmap_foldC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;live_rangesC13~~~C35stdpp8fin_maps;map_to_listC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_alloc_meta@live_ranges_sameC13~~~C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree?ranges_free_subC13~~~K46Stdlib9micromega5Tauto8GFormula03".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_refl C m : magree C m m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h01Ch11mh22_Hh33_H0h41ap;2p;1p;3g0000j2<Tg000Lj10Tg0011j11Tg001Oj22Tg001lj2;Tg002Hj2:Tg002cj14Tg003<j13Tg003Zj15Tg004=j16Tg004_j17Tg005gj28Tg006Aj39Tg007XR0p-0[R1g0086R2g009Hf0R3'<g009f#0R4#1%04#0R4#0#0#0#1'2,;3':f3R5f1R6O1#4%34#5#6P5f2#7O1'8W3W2X40A9633eX12X01P6P3O2W1W0o"). Qed.
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h01ah12C1h22C2h32C3h41Xh52m1h62m2h72m3h81Ah91Bh:2Hah;2Hch<2I1h=2I2h>1op;3p;2p;1p;6g006Aj34Tg0000j2=Tg000Lj10Tg0011j12Tg001Oj2<Tg001lj2:Tg002Hj28Tg002cj11Tg003<j16Tg003Zj17Tg004=j15Tg004_j13Tg00:Kj39Tg00:ej6;Tg007XR0p-0[R1g0086R2f5R3f2R4f1R534R6f8R7f0R8O1R9f7R:P5O1[^00P7P5O1\9^00g009H/=8g009f#0R9#2%09#0R9#0#0#0#2'<,:8'8f9P5O1#1%69#7#5R9P7%34R7O1f:f3R;#3O19998X>9f6R9P4P5f<P4O1R<P5P3P;P8O2O1W4%1<eO3P:P7O1P3P4P5f;P4O1R7P5f4R<P;P8O2O1W4%17eO3E;W;W:X00A4:9<eW=W<X96W8X72X62X52X31X21X11P3P<P;P4P5P8O6X72X62W5X31X21W1o"). Qed.
Lemma magree_of_pres C m m' : pres_except C m m' -> magree C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h01Ch11mh22m'h32Hah42Hch51Ph61ap;3p;2p;1g00;Cj3@Tg0000j2?Tg000Lj10Tg0011j14Tg001Oj2>Tg001lj2:Tg002Hj29Tg002cj11Tg003<j18Tg003Zj17Tg004=j16Tg004_j13Tg00:Kj32Tg00<]j35Tg00=Zj1=Tg00><j3;Tg006Aj3<Tg007XR0p-0[R1g0086R2f2R3f1R4f0R53@g009H/?5g009f#0R6#4%06#0R6#0#0#0#4'>,:5'9f5R7P4O1#1%86#7R6#6R8f4%33R9O1P7P9O132g00>WR:?579%=6R6528#1f3R9#395:7=286#1[P9P3P4P5O33;W4W3X60A<934eW5X22X12X01P3P4P5O3X22W1W0o"). Qed.
Lemma pres_of_magree C m m' : magree C m m' -> pres_except C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h01Ch11mh22m'h31Ah41Hh52Hah62Hch71ah81op;3p;2p;1p;4p;6g006Aj3BTg0000j2ATg000Lj10Tg0011j14Tg001Oj2@Tg001lj2:Tg002Hj29Tg002cj11Tg003<j18Tg003Zj17Tg004=j16Tg004_j15Tg00:Kj32Tg00<]j33Tg00=Zj1?Tg00?kj4;Tg00:ej6<Tg00AEj4=Tg00;Cj3>Tg007XR0p-0[R1g0086R2f2R3f1R4f0R53Bg009H/A5g009f#0R6#4%06#0R6#0#0#0#4'@,:5'9f5R7P4O1#1%86#7R6#6R8f4R9%53R:O1P7P:O132g00>WR;?37:R<%?6R6528#1R=f3R>#5R?93;7=286#1[P>P3P4P5O3R@P8P<f6=3;?=286#1A2846#1[X88P5X4=A3;9:P7P9P:P@C;E<C=W6W5X70A>>34eW3X22X12X01P3P4P5O3X22W1W0o"). Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "p'0h03COVh12Hch21Wh32Hah41xh51Ch66__sat1h74__x1h81mh92m'h:2C1h;3Hinh<2IHh=2MUh>7__arithh?4__ffh@6__sat0hA8__varmaphB5__withC1ahD2a0hE2hihF1lhG2lohH1zi001zi011pp;1p;3p;2p;4p;7p;8p;6g00A`j1ATg000Lj16Tg003<j1<Tg003Zj1=Tg004=j1\Tg00B@j3UTg00CMj21Tg0000j20Tg0011j1:Tg001Oj2FTg001lj22Tg002HR0j24Tg002cj13Tg004_j1[Tg00Dhj25Tg00F7j1@Tg00FWj37Tg00AEj4TTg00G7j4>Tg00GWj7OTg00H9j2NTg00Hcj2MTg00IKj3LTg00Ioj2KTg005gj29Tg00JPj2ITg00Jnj1HTg00KLj1GTg00L7j2;Tg00LZj2JTg00M=j4?Tg00Mhj3ETg00NKj7DTg00=Zj1CTg00Noj8PTg00OSj2QTg00P5j2BTg00:Kj3RTg00Paj3STg00Q@j4ZTg00R2j2YTg00:ej6XTg006Aj3VTg00SCj7WTf1R1g00SgR2g00TFR3P3g00TfR4f0R5g00UFFWp=8g007XR6p-0[R7g00UfR8#AR9g009fR:#6R;#6#6R<#6#6#6R=#<R>#=%<<#=#\[R<f2R??U15f4R@f3RA'1g009HRB/05%:;R;%:=R='FRC,25'4RDf7REP1O1#3P@%[?RFP6P?f8RG/55XH6P8f9RH/15f:RIP@O1#3f5RJ,5?]1]0X29g00W1RKPHPAO1#3RLg00WMW1W0%@8RM,1G15M@^1L]0eg00WiP6P6f;RL/15f<RMf6RNO1#315?E]1]0A78?1,1Mf=PEO1#3A78@A/5G]1]0[^F9P5f>/15f?ROPHO1#315?I]1]010@5125A'4fARPP1O1[^4611O1'4f@RQPIO1#3RIP010N5125J'4fCP1O1[^4611PA10NM12MJ'4#315@M'4P110G5125E'4fEP1O1[^46fD/1N10HO12OG'4RG#3RH15EOPJP?PQP5O2O1X;GPHePNP5P@O2CTW0W:P1P5O2n2001000000120000000W1W0P6P6PAP?C>=781,1OP6P6PJP@C>=78A/5L^1I]0eW<X29XE6XG6P1P5O2n2001101000120100100XD8PEPAP5FO1N>F1M;=12B;RF10B=12BC[RE[10B;R8AL;=1VKW310BC\K^38P1g00XI1KB;'9PFeO1PEg00XoRE#@%AE1I61%H6%G6REP2P3P3P4PEP2P3P3P4P61;6Bg00Y[1J6:R:C?,8EP6P:g00ZB1;6;=E6>C?,8EFDR>%C3P>GP1QE4P5P?g00ZiREg00[IR4'91B5?=RE4dAS6B1CZb?bAbBX7610B1121C'4\D^76P5PNPJO2b>b6b@b6,Y?EXO2W1W3XC6AVJA?eW0W=X9<X8<X29X57PAP?P1P5O4X9<W8W2W5o"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_magree C m m' A cs :
  rw_cells asegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells asegs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h02Hah11Ah21Ch36__sat2h44__x1h54__x2h64__x3h71ah82csh91mh:2m'h;2AGh<1Hh=2H0h>2HCh?7__arithh@4__ffhA6__sat1hB8__varmaphC5__withD4cstrp;1p;4p;3p;2p;5p;6p;7p;8g000Lj10Tg003<j1DTg003Zj1BTg004=j1MTg00A`j1ITg00[ij4XTg006Aj3TTg0000j22Tg00]8j17Tg00^Jj16Tg00^jj2;Tg001lj23Tg002Hj21Tg002cj1eTg00_Gj5bTg0011j1ETg001Oj2VTg00`\j1UTg00Hcj2STg00IKj3RTg00Ioj2QTg005gj2CTg00aAj1:Tg00a`j28Tg00bIj39Tg00c2j2FTg00F7j1PTg00FWj3ATg00JPj2@Tg00c^j4OTg00Jnj1LTg00KLj1NTg00LZj2=Tg00d<j1KTg00daj3JTg00M=j4>Tg00=Zj1dTg00L7j2HTg00Mhj3cTg00OSj2aTg00P5j2\Tg00:Kj3YTg00Paj3ZTg00Q@j4[Tg00eDj4WTg00f`j6]Tg00SCj7^Tg00NKj7_Tg00Noj8`Tg009HR0f0R1'2p=5g007XR2f1R3g00Y[P1C>p=<P3g00SgR4g00TFR5P5g00TfR6P1g00UFF^p=4f2R7P4P5P5P6P3P1F_p=?f3R8P4P5P5P6P7P3P1G`p=Gp-0\2R4g009fR9#0R:#0#0R;#0#0#0R<#DR=#B%D;#B#M[R;g0086R>g00hB#IR?g00>WR@P8P3P1CXf5RAf4RB;T812B1%78#6,;BRC,31'1f8P3O1#e[^72P@f6R@PBP8P7Db%5B%E:RD%E<R<'VRE,2C'1f7RCP@PAPBP812@1%7A#6,;@,31'1PBP3%7@RF#U%6F#51SD<130DRF%5<130E[RG[%5DRHg00W1RIARD<3UW0%5E\I^0HP3g00XI1Q0D'CPFeO1PGg00XoRGg00iPRF#:RH#:RI#:R<#:,82182I182FRF592592g00ioRI'F182<182H=92F592/FI%PG5AG3A%IGP21@27P31@28CO%L2%N2RG1=2:R:1=29RI'<,4GP2PIg00ZBRF%K9,=29J2:R9C>,4G5?G%d5R5PG1H20RH/<:,4G1H2D=c2=R=,<9,4G5?GP51<HI,4GP2PIPFP=C>,4G5?GCGCG1aG6P1P7g00ZiRGg00[IR6'C1\17=YG6dAZ203C[b@bBbCX42X52X6212311;37,31'1%57R01;78/2E'1137E,10[[^42^52^62P1f;#7#6f<P@PAPCO5b?b3bAb3bDP8P3P1O2O3W0X72PCP@PA%7B#6CWeE]b=W>W;W<X8?X12X:>X9;X24PBP8P7P3P1O5W8X12W:W9W2o"). Qed.
Lemma bytes_at_magree C m m' A bs :
  bytes_at asegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at asegs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h02Hah11Ah21Ch36__sat2h44__x1h54__x2h64__x3h71ah82bsh91mh:2m'h;2AGh<1Hh=2H0h>2HCh?7__arithh@4__ffhA6__sat1hB8__varmaphC5__withD4cstrp;1p;4p;3p;2p;5p;6p;7p;8g000Lj10Tg003<j1DTg003Zj1BTg004=j1MTg00A`j1ITg00j[j4XTg006Aj3TTg0000j22Tg00kij27Tg00^Jj16Tg00^jj2;Tg001lj23Tg002Hj21Tg002cj1eTg00lIj5bTg0011j1ETg001Oj2VTg00`\j1UTg00Hcj2STg00IKj3RTg00Ioj2QTg005gj2CTg00aAj1:Tg00a`j28Tg00bIj39Tg00c2j2FTg00F7j1PTg00FWj3ATg00JPj2@Tg00c^j4OTg00Jnj1LTg00KLj1NTg00LZj2=Tg00d<j1KTg00daj3JTg00M=j4>Tg00=Zj1dTg00L7j2HTg00Mhj3cTg00OSj2aTg00P5j2\Tg00:Kj3YTg00Paj3ZTg00Q@j4[Tg00eDj4WTg00m]j6]Tg00SCj7^Tg00NKj7_Tg00Noj8`Tg009HR0f0R1'2p=5g007XR2f1R3g00Y[P1C>p=<P3g00SgR4g00TFR5P5g00TfR6P1g00UFF^p=4f2R7P4P5P5P6P3P1F_p=?f3R8P4P5P5P6P7P3P1G`p=Gp-0\2R4g009fR9#0R:#0#0R;#0#0#0R<#DR=#B%D;#BR;#M[R>g0086R?%I;R@g00>WRAP8P3P1CXf5RBf4RC;T812C117;8#6,;CRD,31'1f8P3O1#e[^72PAf6RAPCP8P7Db%5C%E:RE%E<R<'VRF,2D'1f7RDPAPBPCP812A117;B#6,;A,31'1PCP317;ARG#U%6G#51SE<130ERG%5<130F[RH[%5ERIg00W1RJARE<3UW0%5F\J^0IP3g00XI1Q0E'CPGeO1PHg00XoRHg00iPRG#:RI#:RJ#:R<#:,82182J182GRG592592g00ioRJ'F182<182I=92G592/FJ%PH5AH3A%IHP21@27P31@28CO%L2%N2RH1=2:R:1=29RJ'<,4HP2PJg00ZBRG%K9,=29J2:R9C>,4H5?H%d5R5PH1H20RI/<:,4H1H2E=c2=R=,<9,4H5?HP51<IJ,4HP2PJPGP=C>,4H5?HCGCG1aH6P1P7g00ZiRHg00[IR6'C1\17=YH6dAZ203C[b@bBbCX42X52X6212311;37,31'1%57R01;78/2F'1137F,10[[^42^52^62P1f;,7;#6f<PAPBPDO5b?b3bAb3bDP8P3P1O2O3W0X72PDPAPB17;C#6CWeE]b=W>W;W<X8@X12X:?X9>X24PCP8P7P3P1O5W8X12W:W9W2o"). Qed.
Lemma wr_at_magree C m m' A n :
  wr_at asegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at asegs m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"] "h02Hah11Ah21Ch36__sat3h44__x1h54__x2h64__x3h71ah81mh92m'h:1nh;2AGh<1Hh=2H0h>2H1h?2HCh@7__arithhA4__ffhB6__sat2hC8__varmaphD5__witp;1p;4p;3p;2p;6p;7p;8g000Lj13Tg003<j1ETg003Zj1?Tg004=j1ITg00o?j4`Tg006Aj3QTg0000j20Tg00^jj24Tg001lj22Tg002Hj29Tg002cj1HTg0011j1BTg001Oj2FTg00Hcj2_Tg00IKj3UTg00Ioj2TTg005gj2CTg00aAj18Tg00a`j25Tg00bIj37Tg00c2j2@Tg00F7j1PTg00FWj3>Tg00A`j1OTg00JPj2=Tg00c^j4NTg00Jnj1MTg00KLj1JTg00LZj2:Tg00d<j1KTg00daj3LTg00M=j4<Tg00=Zj1GTg00L7j2DTg00Mhj3RTg00OSj2STg00P5j2^Tg00:Kj3]Tg00Paj3\Tg00Q@j4VTg00eDj4WTg010Jj6XTg00SCj7YTg00NKj7ZTg00Noj8[Tg007XR0f1R1g00Y[f0R2C<p=6P1g00SgR3g00TFR4P4g00TfR5P2g00UFFYp=1f2R6P3P4P4P5P1P2FZp=Af3R7P3P4P4P5P6P1P2G[p=;p-0\0R3g009fR8#3R9#3#3R:#3#3#3R;#ER<#?%E:#?#I[R:g0086R=g00>WP7P1P2C`f5R>f4R?;Q710?214?7,22'9f8R@P1O1#H[^70g009HRA/0?14>?%B9RB%B;R;'FRC'0P@f7RDf6REP>P?10D214DE,22'9P>P11_B;12ABRF10A;12AC[RG[10ABRHg00W1RIAUB;1UW010AC\I^0HP1g00XI1TAB'CPFeO1PGg00XoRGg00iPRF#8RH#8RI#8R;,50150I150FRF570570g00ioRI'@%8;,50150H=70F570/@I%PG5>G3>%OGP01=06P11=07CN%M0%J0RG1:09R91:08RI'6,1GP0PIg00ZBRF%K8,:09L09R8C<,1G5AG%G4R4PG1D0B=R0<R<,68,1GP4PG1D0AR8/69,1GP4168I,1GP0PIPFP<C<,1G5AGC;C;C;1SG5P2P6g00ZiRGg00[IR5'C1^26=]G5dA\0A1CVbAbCbDX40X50X6010121416,22'91467/0C10A7RA127C,9A[[[^40^50^60P2f;f<P>P?PEPDO6b@b3bBb3P?P1P2O2O3W0X70P@PDPEP>CWeEXW>W=W?W;W<X:0X10X9=X8:X23P?P7P6P1P2O5X:0X10W9W8W2o"). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
(* [comment removed for export] *)
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ETP : errno_addr tp = 0x1a620 - 164.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h02Hah17__sat13h27__arithh34__ffh47__sat12h58__varmaph65__with72tph81zp;1p;2p;3p;4p;7p;6g000Lj12Tg003<j1DTg003Zj1@Tg00d<j11Tg0011j13Tg011ij2OTg00H9j2<Tg012Oj1BTg00^jj2;Tg012mj2?Tg00:Kj36Tg005gj25Tg00Hcj2TTg001lj28Tg0000j24Tg001Oj2STg00IKj3RTg00Ioj2QTg00F7j1NTg00A`j1HTg013Jj1FTg00Jnj1CTg00KLj1ETg00L7j27Tg00M=j4:Tg00Mhj3GTg00NKj7ATg00OSj2ITg00P5j2JTg00Paj3KTg00Q@j4LTg002Hj2MTg013hj2>Tg00:ej6=Tg00SCj7PTf0R0#2#2p=0f1R1g00SgR2g00TFR3P3g00TfR4P0g00UFFPp=9g009fR5#2R6#2#0#0R7#DR8#@R9%15#2#1#0#1#1#2#0#1#2#0#0#3R5,O8R:g007XR;1<80%16#0#1#0R<#BR=';%3<,?5R<36X79P;P51;0==6;<X8;15;<1<8:%36R6%37R7'Tg009HR:/86R<14:71S67R=,8:[R9[14:6R>g00W1R?AR671UW014:=\?^0>P1g00XI1Q:6'5P<eO1P9g00XoR9#N%H9%F;%C;%E;R9P2P3P3P4P;17;:g00Y[17;5R3C:,99P;P3g00ZB17;6=G;8C:,99FA1I94P0f2R9g00ZiR4g00[IR8'51J09=648dAK;:1CLb3b5b614:5185='MP0b2b1b4b1,>5E=p,2tpp,2TPE=o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X).
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h01Xh11ch21qp;1p;2g015=j12Tg016Jj11Tg005gj20Tg017YR0g018kR1g007XR2g01:9f2R3#2#1'0X12X21X00P3f1f0O3W1W2W0o"). Qed.
(* [comment removed for export] *)
Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h02RRh13Xsth22blh32kkh42ppp;1p;2p;3p200R0g01;MR1p4p710p8P0p101<Xp4p710p8P1j12Tg01=ij27Tg00d<j11Tg000Lj10Tg0011j16Tg01?7j35Tg01@Ij24Tg005gj23Tg017YR1g018kR2g01@kf4R3#2R4[\1R5f3R6#2R7f1R8f2R9g01B9'7R:g009f#1#0#0#1#0#0#6556142:O2,34X27X35X42X11X00P3P6P9P8f0O5W2W3W4W1X00o"). Qed.
Lemma conc_am_took X q c y : conc (am_took X q c) y = conc X y.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h01Xh11ch21qh31yp;2g01CKj21Tg005gj20Tg017YR0g018kR1g007XR2f3R3f0R4'1,02X31X12X21X00P3f2f1P4O4X31W1W2W0o"). Qed.
Lemma brk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "p'0h01ch11ph23stYh31ai001ah42o0i011oi022tli031xp;1p;4p;6p;2p;3p;5p;7g01DYj1DTg01Ehj1GTg01GBj4NTg01G`j6ITg01HAj4YTg01HUj4TTg01I5j4QTg01IQj4MTg0011j1ATg01=ij28Tg01Ijj1HTg012mj2XTg01KKj2UTg01Lnj27Tg01NLj22Tg01O]j19Tg01Pnj1PTg01R?j1OTg01SQj35Tg01Taj2;Tg01V4j1CTg01WPj2Lj1BTg01Xlj1@Tg01Z>j1KTg00=Zj1JTg01ZZj5>Tg01[5j1ETg015=j11Tg016Jj13Tg00:Kj3=Tg005gj2?Tg01\Ej2RTg01@Ij2STg000Lj1FTg01]Xj6WTg01]lj7VTg018kR0f0R1'Sp=0%F1#Fp=4P0g01^@R2f3R3f2R4f1R5P1EWp=6g009HR6?516p=<P0P2f4R6P3P4P5P1FVp=:g017YR7%D5#Gg01@kg004=R8P0g01:9R9P0g01_PR:g01_nR;g007XR<g01`GR=CNR>P:P;g01``P<P=g01a>EIR=P2CYR<P0P2P<P0P>P=P2CTCQR;P4%04R:P8P0P7P1P<P;P1P8P2P2P<P0P>P=P2CMR=P1g01a\R>g009fR?#4#4#4#4#4#4#AR@,86#0%H1%A?'X/U1R?'7W0/26RA#9RBC6%P1RC%06%O1RD35%03#<n10110300021010000PBD:/;A%C:183@#0/7?X0>/23'2n10110300021010200RA#D'L#@P2P2%K2RB%J0#<REP<P=P4%B:/2ARA#9RFC6D>#Eg01blRG35PFD:/;A#1#3%13#33=P1%16#3,?9X30P1O1%14#3,?9n10110101021010000b4P<P;P1%01R6#BP8P0P7185@#0/7?X0>/25R3#1#GP<P;P1P8P2P2P<P=P1184@#0/7?X0>/24R4#9R>C6A5C:D%05#<n10110300021010000P>D:/;4%C6/23n10110300021010200'2R3#1#@P2P2PBPEP<P=P1%93R=C6D>#E;5GP=D:/;3#1#3%15#3R35=9e1R51#1#3==93eX10X27P5P1O2X10W2o"). Qed.
Lemma conc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "p'0h01ph13stYh21yh31gi001ri011xp;4p;1p;3p;2p;6g01HAj4>Tg01d<j11Tg01IQj4;Tg01eOj34Tg01elj1<Tg01g<j35Tg00^jj23Tg00:Kj32Tg005gj2:Tg01\Ej27Tg01gYj28Tg00:ej69Tg01CKj26Tg01]Xj6=Tg01_PR0g01i4R1f3R2f2R3f1R4f0R5E=p=0g017YR6g018kR7P0g01_nR8g01``R9P1C>R:%13R;g007XR<g004=R=P1P<P:P0P8P9P1C;R9A40<4R8P5C0%<5R>A50<3'3R?g009HR@n10110100021010000P=P1P<P:P9P8%12C0P?P@n1011010002101000032X3:P=P1P<P:P9A40<5P;C0A50<4,3>P@n10110100021010000,:<1734R@#11834E916@5163552<eX27X07X16P3P4P5O3X27W0W1o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h03stAh13stBh22E1h32E2h41gh52krh61lp;4p;1p;3p;2p;6p;5g01HAj4?Tg01d<j11Tg00:Kj30Tg00Wij26Tg00A`j1>Tg01jFj13Tg01g<j3<Tg01kZj1;Tg01m5j4:Tg01mLj44Tg01mhj32Tg005gj29Tg00:ej68Tg01nEj17Tg01oZj5=Tg01_PR0g01i4R1f2R2f1R3f0R4D=p=5g017YR5P0g01_nR6g01``R7P1C?R8%14%1330g007XR9/69R9#>R:%33%32R;30P8f3R<#1R=%3<R>1601R?P9A<014#;X5?R@P0P6P7P1C:R1=584C4529f4R7#3P?P9P@%179581C4R7529R650:X48P:P>A2947=0:6X6:P?P9P@A581=C4929>,9:P;P4E8%12P3E8%72%7<50:eW3W2X15X05P3P4O2X15W0o"). Qed.

Lemma fresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CEIL_WRAP_1"; "ASM"] "h04__p1h14__x1h24__x2h37__arithh44__ffh58__varmaph65__with74__x3h81Lh92RFh:4__x4h;1ah<3stYh=1xh>2E1h?2E2h@2HahA2XChB1lp;4p;1p;3p;2p;6p;9p;7p;8g01HAj4cTg01d<j1ETg00:Kj3?Tg00Wij2OTg00A`j1KTg01jFj1JTg01nEj1@Tg0207j39Tg00^jj21Tg021Lj1NTg0000j20Tg001lj23Tg002Hj27Tg0011j1^Tg00aAj1FTg00a`j2BTg00bIj3GTg00c2j2WTg00F7j1VTg00FWj3UTg013Jj1TTg00JPj2ATg00c^j45Tg00Jnj1QTg00KLj1PTg00LZj26Tg00d<j1DTg000Lj1CTg00daj3;Tg00=Zj1MTg00OSj2LTg005gj2RTg00P5j2STg00Paj3bTg00Q@j4aTg022`j4`Tg024Aj6]Tg00L7j2ITg024]l9\Tg00AEj4ZTg026;j6[Tg00M=j4HTg00SCj7YTg00NKj7XTg00Noj8_Tg00ZiR0f0R1g00[IR23?p=4f1R3g00SgR4g00TFR5P5g00TfR6P1E[p=>g007XR7P3g00ZBP1CHp==P3P4P5P5P6P1g00UFFYp=2f2R8P4P5P5P6P3P1FXp=<P7P3g00Y[P1CHp=:f3R9P4P5P5P6P8P3P1G_p=8g017YR4g01_Pg01_ng01``g01i4Cc%E9p,2stR:#E3?1O77#KR;f4R<#J%J:3?f5R=#@?9<9#411=<p,4RUNp#NR>'0f6R?/0<11?=,3<'713=>%@:R@g009fRA#^RB79=#4p-0RCg00XoRDg00iPRE#FRF#F,B71B7F1B7E5G75G7g00io'W%VDRE3U%KDRDP7P7%T7RFP81A79RGC5P3P7PFP<1A7<C5C5%Q7RH%P7RI1>I?167ARJ%DARK#C,67%DK,675;7RL'=,2I5<I%M5R5PI%CA,67RA,:L,2IP51=JA,2IC8C81LI6R6P1P81R021S18#4dg009HR2=b73CaR0b4b5b6X17X27X77X:7W01189RL,31,7<119</081389[[^17^27^77^:7^0CP1f8RM/0?f7RNPMP>P?P3P8O7b3P;%@MA91MN#4XB;P8P@P:PMP<P9C`E]A9@N?#4P@PMPNP?PBP1PEPDP71A78R?P3PFC5PHPI1:JA,2IR@1>I<5<IP5P@C8P6P0b4b5b6X17X27X0C1013/781038[^17^27^0CP1f9R@/1M,3NPNP@P8O4b3PEPDP7P?P3PGC5PHPI1>I=167K9;7ARA,=J,2I5<IP51I7BR59;7J/:A,2IC8P6P0b4b5b6X17X27X77X0C1138,31,79113B/0L[^17^27^77^0CP110@NPMP@PNP8O5b3PEPDPFPH1I72/:5,2IP6P0b4b5b6102BP1b3M9\b9CZW@WAW9W?W>X;7X87X=7X<4P9P8P3P1O4X;7X87X=7W<o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ASM.
End CEIL_WRAP_1.

(* [comment removed for export] *)
