(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmBIosDtorP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBIosDtor () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw'"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "4Model"; "4event"]; ["5bvmap"; "0M"; "0M'"; "0R"; "0R'"; "6credit"; "6regs_preserved"; "7aheap_pres"; "7astack_ok"; "7fframe"; "7hl_tp"; "7model_rt"; "7ri_inv"; "7vml_of"; "9ra_ok"; "8SCFG"]; [":cfg"; ";ios_dtor_spec"; ";locale_dtor_spec"; "<FPState"; "<getr"; "=srealizes"; ">amodel_ok"; "?loaded_segments"; "0SCFG_P"; "@incl"; "Aof_nat"; "0ar"; "0cr"; "0fx"; "0model"; "0model'"]; ["0r"; "0sp"; "BZ_to_bv"; "Bbv"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBID.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Let LYa := PMB.ly_as0 L C LY.
Lemma free_null_atA : ltac2:(TCodec.tc2 tcn__PmBIosDtor "TE'Q3&@y5'QCyR0%211%5241'4y8%611%311p061'>'2'?%211!pS:21'5'7%2211%811&I%:11&E&Lv9r7r6r5r4r3r:&Mr9%211%;8:9876541&Q6%1286'6&Q4r=&QB&Q:u:%211%42Q<1%7261z%72Q=1%;3Q=31r>u1%:11%<2QD1%?241%>2QDJ%B3QD21&N%11Nr@u4%C11%E2QM1%H241&Jv;%211%J2R01%N3R051rAu2%M11%O2R71%Q2241r8%Q22R81%Q63R831&HvQ;+TP0%35?2;1Q?(3%11R5%H11&FrH%221QI&GrErD%38I<21O;5QM&K%127QO&Q9rC%23R<1R2%QL2R4R5rIrGrF%R41R:%R=8R<4@32R:K1'Q5&Q7&OvQ8%211&Q0rO%2661R>DR<Q3rK%948521p0;1p0A1p0C1p0G1p0J1p0O1p4S21pS0S<1pQ6S>1pQ:SD1+_T\<%@6DHQ31Q2MrB%G4FC21p051p0Q<1p0Q@1p0QE1p0QN1p0R91p0R<1p0RD1p0S11p0S41pS2SF1pS4SG1p2SF1pRJSD1pLSF1pBSG1pJSJ1pFSO1pRNT51pQ4T71pQ8T=1pRLTD1").
Proof. intros fx R M model K LB FF LK cr Aw sp r.
intros HH [Mh MI] A10 A1 RA A4 A2 AST K0 KONT. pose proof (HAJ.aex_free_null _ _ _ _ _ EXT) as FN. unfold afree_null_spec in FN.
rewrite (L5A.aly_segs L C LYa), (L5A.aly_free L C LYa), (L5A.aly_scr_free L C LYa) in FN. unfold PMSPA.cfg.
assert (SP : bv_unsigned (getr R 2%bv) = sp).
{ rewrite <- L5K.rl2 in A2. rewrite A2. apply L5.unsigned_lit. pose proof AST as (_ & X1 & X2 & X3 & _). lia. }
apply (FN fx R M model LB FF LK cr Aw K HH Mh MI); [rewrite <- L5K.rl10 in A10; exact A10| rewrite <- L5K.rl4 in A4; exact A4
| rewrite <- L5K.rl1 in A1; rewrite A1; apply L5K.ret_ok_lit; exact RA| rewrite SP; exact AST| exact K0|].
intros R' M' model' Aw' RP AP MR INC MI' HH'. rewrite <- L5K.rl1 in A1. rewrite A1. rewrite SP in AP.
apply (KONT R' M' model' Aw' RP AP MR INC); [split; [rewrite (L5LZ.model_rt_halted model model' MR); exact Mh| exact MI']| exact HH'].
Qed.
Theorem ios_dtor_ok : ltac2:(TCodec.tc2 tcn__PmBIosDtor "9&Q2vQ8v;vQ;v9%544321&Q1%146543p031").
Proof.
intros LDT. unfold PMB.ios_dtor_spec, PMSPA.ios_dtor_spec.
intros fx R M model K LB FF LK Aw cr o vp rdb st sp r HH AM K0 ENT FRM FRS A10 AO O8 IOS BASE KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
destruct IOS as (I0 & I32 & I36 & I40 & I48 & ZB & ID & IC & ST). change (pa_classic_imp PMB.AD) with 0x66f900 in I48.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 152 sp 14336 HH (PMKB.aobj_of_aobjA FF o 152 AO O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as Hs19. change (bv_modulus 64) with (2 ^ 64) in *.
assert (V3 : L5.writable RSEGS MV (sp - 48) 48).
{ apply (proj2 (L5A.writable_vis H M (sp - 48) 48 (VIS (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]. lia. lia. }
assert (VO8 : L5.writable RSEGS MV o 8).
{ apply (proj2 (L5A.writable_vis H M o 8 ltac:(eapply L5A.avis_sub; [exact OVIS|lia|lia]) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M o 152); [exact ODEF| lia| lia]. lia. lia. }
assert (V48 : L5.u64_at RSEGS MV (o + 48) 0x66f900).
{ apply (proj2 (L5A.u64_at_vis H M (o + 48) 0x66f900 ltac:(eapply L5A.avis_sub; [exact OVIS|lia|lia]) ltac:(lia) ltac:(lia))). exact I48. }
assert (VZB : L5KA.zeros_at MV (o + 56) 80) by (apply (proj2 (L5A.zeros_at_vis H M (o + 56) 80 ltac:(eapply L5A.avis_sub; [exact OVIS|lia|lia]))); exact ZB).
pose proof (PMBIDP.aidA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => 0x66f900 | _ => 0 end)) as P. cbn beta iota in P. rewrite HO in P.
L5SAR.feed P ltac:(first [assumption | exact Rsp | unfold PMBIDP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ0 & MS1 & KS1 & A1 & A2 & A8 & A9 & B10 & B11 & C0 & C40 & C32 & C24 & C16 & C8).
assert (FRZ1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 40 <= a < sp - 40 + 40) \/ (o + 0 <= a < o + 0 + 8)) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
unfold PMSPA.cfg. cbn [pa_ios_dtor PMB.AD ADDR_B].
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xd7640 R1 0xfbe24 M1v (fun a => (sp - 40 <= a < sp - 40 + 40) \/ (o + 0 <= a < o + 0 + 8)) K HH AM MS1 MG1 FRZ1).
{ intros a Ha Wa. split; [|intros X; destruct Wa; lia]. unfold aclientw, aclient_g. destruct Wa as [Wa|Wa].
- right; left. split; [lia| intros X; lia].
- do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (AG01 : forall a n, o + 8 <= a -> a + n <= o + 152 -> L5C.agree_on M M1 a n).
{ intros a n X Y i Hi. apply FR1; [lia|]. intros [Q|Q]; lia. }
assert (ASTK1 : L5CA.astk ar M1 sp 14336) by (apply (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1)).
assert (SV1 : forall k v, 1 <= k <= 5 -> L5.u64_at RSEGS M1v (sp - 8 * k) v -> L5.u64_at RSEGS M1 (sp - 8 * k) v).
{ intros k v Hk SV. rewrite <- VIS1 in SV. exact (proj1 (L5A.u64_at_vis H M1 (sp - 8 * k) v (VIS (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) SV). }
unfold PMB.locale_dtor_spec, PMSPA.locale_dtor_spec in LDT. cbn [pa_locale_dtor PMB.AD ADDR_B] in LDT.
apply (LDT fx1 R1 M1 model1 K LB FF LK Aw cr (o + 48) (sp - 48) 0xd7118 HH1 AM1 K0).
{ split; [rewrite L5K.rl1; exact A1|]. split; [split; [lia|reflexivity]|]. split; [rewrite L5K.rl2; exact A2|].
split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 0) with 12288. split.
{ apply (L5SAR.astk_sub ar M1 M1 sp 14336 48 12288 ASTK1 (fun _ X => X)); [lia|lia|lia|].
replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
change (12288 / 8) with 1536. intros j Hj. unfold byte_at.
assert (SJ : S (sp - 48 - 12288) + j = S (sp - 48 - 12288 + 8 * j)).
{ unfold S. replace (sp - 48 - 12288 + 8 * j) with (j * 8 + (sp - 48 - 12288)) by lia. rewrite Z.div_add_l by lia. lia. }
pose proof (PMKB.S_in_shadow (sp - 48 - 12288 + 8 * j) ltac:(lia)) as SXB. unfold BIGSHADOW_LO, BIGSHADOW_HI in SXB.
assert (SZ1 : shadow_zero M (sp - 48 - 12288) 1536).
{ apply (PMKB.shadow_zero_sub M (sp - 14336) 1792); [| |lia|lia|lia| exact STKSH].
- apply PMKB.mod16_8'. replace (sp - 14336) with (sp + (-896) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
- apply PMKB.mod16_8'. replace (sp - 48 - 12288) with (sp + (-771) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
rewrite FR1; [exact (SZ1 j Hj)| lia| rewrite SJ; intros [X|X]; lia]. }
{ intros k Hk. specialize (FRM k Hk). lia. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ rewrite L5K.rl10. exact B10. }
{ destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia. }
{ apply (L5C.u64_at_agree RSEGS M M1); [apply AG01; lia|lia|lia|exact I48]. }
intros fx2 R2 model2 RP2 MRT12 AM2 HH2.
assert (ZB1 : L5KA.zeros_at M1 (o + 56) 80) by (apply (PMF.zeros_at_agree M M1); [apply AG01; lia| exact ZB]).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model2 HH2) as (_ & VISB & _ & _ & _ & _ & _ & _).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M1 model2 o 152 sp 14336 HH2 (PMKB.aobj_of_aobjA FF o 152 AO O8) ltac:(lia) ltac:(reflexivity))
as (_ & _ & _ & OVISB & _ & _ & _).
set (MVB := mrestrict (ahid Aw model2) M1) in *.
assert (RB2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact A2).
assert (RB8 : getr R2 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; rewrite A8; exact A10).
assert (WB3 : L5.writable RSEGS MVB (sp - 48) 48).
{ pose proof ASTK1 as (_ & _ & _ & _ & SDB & _).
apply (proj2 (L5A.writable_vis (ahid Aw model2) M1 (sp - 48) 48 (VISB (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M1 (sp - 14336) 14336); [exact SDB| lia| lia]. lia. lia. }
assert (WBZ : L5KA.zeros_at MVB (o + 56) 80) by (apply (proj2 (L5A.zeros_at_vis (ahid Aw model2) M1 (o + 56) 80 ltac:(eapply L5A.avis_sub; [exact OVISB|lia|lia]))); exact ZB1).
cfeed PB (PMBIDP.aidB_conc fx2 R2 MVB (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMBIDP.aligned; lia | lia]).
destruct PB as (fxB1 & RB1 & MBv & MGB & _ & FZB & MSB & KSB & XB1 & XB10).
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M1 model2 fx2 fxB1 R2 0xd7118 RB1 0x7918c MBv K HH2 AM2 MSB MGB FZB).
intros MB1 modelB1 HHB1 AMB1 MRTB1 HIDB1 VISB1 MGMB1 FRB1.
assert (RBtp : getr RB1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KSB 4%nat) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 4 RP2) by inl; rewrite (KS1 4%nat) by inl; exact Rtp).
apply (free_null_atA fxB1 RB1 MB1 modelB1 K LB FF LK cr Aw (sp - 48) 880928 HHB1 AMB1); [exact XB10| exact XB1
| split; [lia| reflexivity]| exact RBtp| rewrite (KSB 2%nat) by inl; exact RB2| |exact K0|].
{ rewrite <- (Z.sub_0_r (sp - 48)). apply (L5SAR.astack_ok_of_astk L ar C LYa M1 MB1 (sp - 48) 12288 0 4096).
- apply (L5SAR.astk_sub ar M1 M1 sp 14336 48 12288 ASTK1 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
- exact MGMB1. - lia. - lia. - lia. - rewrite Z.sub_0_r. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
intros R4 M4 model4 Aw4 RP4 AP4 MR4 INC4 AM4 HH4.
assert (EB1 : forall a, 0 <= a < 2 ^ 64 -> MB1 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by exact FRB1.
assert (AGRB : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 48) 4096 a -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha Hc. destruct AP4 as (PP & _). rewrite (PP a Ha Hc). apply EB1. exact Ha. }
assert (ASTK4 : L5CA.astk ar M4 sp 14336).
{ apply (L5SAR.astk_after_rt L ar C HI HIok LB FF LK cr Aw M1 MB1 M4 _ sp 14336 (sp - 48) 4096 HH2 ASTK1 MGMB1 AP4); lia. }
assert (ZB4 : L5KA.zeros_at M4 (o + 56) 80).
{ intros i Hi. rewrite AGRB; [apply ZB1; exact Hi| lia|]. unfold aclient, aclient_g. do 3 right. left.
destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw4 M4 model4 HH4) as (_ & VISC & _ & _ & _ & _ & _ & _).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw4 M4 model4 o 152 sp 14336 HH4 (PMKB.aobj_of_aobjA FF o 152 AO O8) ltac:(lia) ltac:(reflexivity))
as (_ & _ & _ & OVISC & _ & _ & _).
set (MVC := mrestrict (ahid Aw4 model4) M4) in *.
assert (RC2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved RB1 R4 2 RP4) by inl; rewrite (KSB 2%nat) by inl; exact RB2).
assert (RC8 : getr R4 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved RB1 R4 8 RP4) by inl; rewrite (KSB 8%nat) by inl; exact RB8).
assert (WC3 : L5.writable RSEGS MVC (sp - 48) 48).
{ pose proof ASTK4 as (_ & _ & _ & _ & SDC & _).
apply (proj2 (L5A.writable_vis (ahid Aw4 model4) M4 (sp - 48) 48 (VISC (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M4 (sp - 14336) 14336); [exact SDC| lia| lia]. lia. lia. }
assert (WCZ : L5KA.zeros_at MVC (o + 56) 80) by (apply (proj2 (L5A.zeros_at_vis (ahid Aw4 model4) M4 (o + 56) 80 ltac:(eapply L5A.avis_sub; [exact OVISC|lia|lia]))); exact ZB4).
cfeed PC (PMBIDP.aidC_conc fxB1 R4 MVC (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMBIDP.aligned; lia | lia]).
destruct PC as (fxC1 & RC1 & MCv & MGC & _ & FZC & MSC & KSC & XC1 & XC10).
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw4 M4 model4 fxB1 fxC1 R4 0xd7120 RC1 0x7918c MCv K HH4 AM4 MSC MGC FZC).
intros MC1 modelC1 HHC1 AMC1 MRTC1 HIDC1 VISC1 MGMC1 FRC1.
assert (RCtp : getr RC1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KSC 4%nat) by inl; rewrite (L5SAR.cs_of_preserved RB1 R4 4 RP4) by inl; exact RBtp).
apply (free_null_atA fxC1 RC1 MC1 modelC1 K LB FF LK cr Aw4 (sp - 48) 880936 HHC1 AMC1); [exact XC10| exact XC1
| split; [lia| reflexivity]| exact RCtp| rewrite (KSC 2%nat) by inl; exact RC2| |exact K0|].
{ rewrite <- (Z.sub_0_r (sp - 48)). apply (L5SAR.astack_ok_of_astk L ar C LYa M4 MC1 (sp - 48) 12288 0 4096).
- apply (L5SAR.astk_sub ar M4 M4 sp 14336 48 12288 ASTK4 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
- exact MGMC1. - lia. - lia. - lia. - rewrite Z.sub_0_r. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
intros R6 M6 model6 Aw6 RP6 AP6 MR6 INC6 AM6 HH6.
assert (EC1 : forall a, 0 <= a < 2 ^ 64 -> MC1 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by exact FRC1.
assert (AGRC : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 48) 4096 a -> M6 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
{ intros a Ha Hc. destruct AP6 as (PP & _). rewrite (PP a Ha Hc). apply EC1. exact Ha. }
assert (ASTK6 : L5CA.astk ar M6 sp 14336).
{ apply (L5SAR.astk_after_rt L ar C HI HIok LB FF LK cr Aw4 M4 MC1 M6 _ sp 14336 (sp - 48) 4096 HH4 ASTK4 MGMC1 AP6); lia. }
assert (ZB6 : L5KA.zeros_at M6 (o + 56) 80).
{ intros i Hi. rewrite AGRC; [apply ZB4; exact Hi| lia|]. unfold aclient, aclient_g. do 3 right. left.
destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw6 M6 model6 HH6) as (_ & VISD & _ & _ & _ & _ & _ & _).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw6 M6 model6 o 152 sp 14336 HH6 (PMKB.aobj_of_aobjA FF o 152 AO O8) ltac:(lia) ltac:(reflexivity))
as (_ & _ & _ & OVISD & _ & _ & _).
set (MVD := mrestrict (ahid Aw6 model6) M6) in *.
assert (RD2 : getr R6 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved RC1 R6 2 RP6) by inl; rewrite (KSC 2%nat) by inl; exact RC2).
assert (RD8 : getr R6 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved RC1 R6 8 RP6) by inl; rewrite (KSC 8%nat) by inl; exact RC8).
assert (WD3 : L5.writable RSEGS MVD (sp - 48) 48).
{ pose proof ASTK6 as (_ & _ & _ & _ & SDD & _).
apply (proj2 (L5A.writable_vis (ahid Aw6 model6) M6 (sp - 48) 48 (VISD (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M6 (sp - 14336) 14336); [exact SDD| lia| lia]. lia. lia. }
assert (WDZ : L5KA.zeros_at MVD (o + 56) 80) by (apply (proj2 (L5A.zeros_at_vis (ahid Aw6 model6) M6 (o + 56) 80 ltac:(eapply L5A.avis_sub; [exact OVISD|lia|lia]))); exact ZB6).
cfeed PD (PMBIDP.aidD_conc fxC1 R6 MVD (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMBIDP.aligned; lia | lia]).
destruct PD as (fxD1 & RD1 & MDv & MGD & _ & FZD & MSD & KSD & XD1 & XD10).
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw6 M6 model6 fxC1 fxD1 R6 0xd7128 RD1 0x7918c MDv K HH6 AM6 MSD MGD FZD).
intros MD1 modelD1 HHD1 AMD1 MRTD1 HIDD1 VISD1 MGMD1 FRD1.
assert (RDtp : getr RD1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KSD 4%nat) by inl; rewrite (L5SAR.cs_of_preserved RC1 R6 4 RP6) by inl; exact RCtp).
apply (free_null_atA fxD1 RD1 MD1 modelD1 K LB FF LK cr Aw6 (sp - 48) 880944 HHD1 AMD1); [exact XD10| exact XD1
| split; [lia| reflexivity]| exact RDtp| rewrite (KSD 2%nat) by inl; exact RD2| |exact K0|].
{ rewrite <- (Z.sub_0_r (sp - 48)). apply (L5SAR.astack_ok_of_astk L ar C LYa M6 MD1 (sp - 48) 12288 0 4096).
- apply (L5SAR.astk_sub ar M6 M6 sp 14336 48 12288 ASTK6 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
- exact MGMD1. - lia. - lia. - lia. - rewrite Z.sub_0_r. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
intros R8 M8 model8 Aw8 RP8 AP8 MR8 INC8 AM8 HH8.
assert (ED1 : forall a, 0 <= a < 2 ^ 64 -> MD1 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)) by exact FRD1.
assert (AGRD : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 48) 4096 a -> M8 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
{ intros a Ha Hc. destruct AP8 as (PP & _). rewrite (PP a Ha Hc). apply ED1. exact Ha. }
assert (ASTK8 : L5CA.astk ar M8 sp 14336).
{ apply (L5SAR.astk_after_rt L ar C HI HIok LB FF LK cr Aw6 M6 MD1 M8 _ sp 14336 (sp - 48) 4096 HH6 ASTK6 MGMD1 AP8); lia. }
assert (ZB8 : L5KA.zeros_at M8 (o + 56) 80).
{ intros i Hi. rewrite AGRD; [apply ZB6; exact Hi| lia|]. unfold aclient, aclient_g. do 3 right. left.
destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
assert (FRM1 : forall a, sp - 48 <= a < sp -> aclient L ar LB FF (sp - 48) 4096 a).
{ intros a Ha. unfold aclient, aclient_g. right; left. split; [lia| intros X; lia]. }
assert (SV8 : forall k v, 1 <= k <= 5 -> L5.u64_at RSEGS M1 (sp - 8 * k) v -> L5.u64_at RSEGS M8 (sp - 8 * k) v).
{ intros k v Hk SV. apply (L5C.u64_at_agree RSEGS M1 M8); [|lia|lia| exact SV].
intros i Hi. rewrite AGRD by (try apply FRM1; lia). rewrite AGRC by (try apply FRM1; lia). rewrite AGRB by (try apply FRM1; lia). reflexivity. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw8 M8 model8 HH8) as (_ & VISE & _ & _ & _ & _ & _ & _).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw8 M8 model8 o 152 sp 14336 HH8 (PMKB.aobj_of_aobjA FF o 152 AO O8) ltac:(lia) ltac:(reflexivity))
as (_ & _ & _ & OVISE & _ & _ & _).
set (MVE := mrestrict (ahid Aw8 model8) M8) in *.
assert (SVE : forall k v, 1 <= k <= 5 -> L5.u64_at RSEGS M1v (sp - 8 * k) v -> L5.u64_at RSEGS MVE (sp - 8 * k) v).
{ intros k v Hk SV. apply (proj2 (L5A.u64_at_vis (ahid Aw8 model8) M8 (sp - 8 * k) v (VISE (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply SV8; [exact Hk|]. apply SV1; assumption. }
assert (RE2 : getr R8 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved RD1 R8 2 RP8) by inl; rewrite (KSD 2%nat) by inl; exact RD2).
assert (RE8 : getr R8 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved RD1 R8 8 RP8) by inl; rewrite (KSD 8%nat) by inl; exact RD8).
assert (WE3 : L5.writable RSEGS MVE (sp - 48) 48).
{ pose proof ASTK8 as (_ & _ & _ & _ & SDE & _).
apply (proj2 (L5A.writable_vis (ahid Aw8 model8) M8 (sp - 48) 48 (VISE (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M8 (sp - 14336) 14336); [exact SDE| lia| lia]. lia. lia. }
assert (WEZ : L5KA.zeros_at MVE (o + 56) 80) by (apply (proj2 (L5A.zeros_at_vis (ahid Aw8 model8) M8 (o + 56) 80 ltac:(eapply L5A.avis_sub; [exact OVISE|lia|lia]))); exact ZB8).
rewrite Rra, L5.unsigned_lit in C8 by lia.
assert (Y8 : L5.u64_at RSEGS MVE (sp - 8) r) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SVE; [lia| exact C8]).
assert (Y16 : L5.u64_at RSEGS MVE (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SVE; [lia| exact C16]).
assert (Y24 : L5.u64_at RSEGS MVE (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SVE; [lia| exact C24]).
assert (Y32 : L5.u64_at RSEGS MVE (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SVE; [lia| exact C32]).
assert (Y40 : L5.u64_at RSEGS MVE (sp - 40) (bv_unsigned (getr R (reg 19)))) by (replace (sp - 40) with (sp - 8 * 5) by lia; apply SVE; [lia| exact C40]).
cfeed PE (PMBIDP.aidE_conc fxD1 R8 MVE (fun j => match j with 2%nat => sp | 36%nat => bv_unsigned (getr R (reg 18)) | 37%nat => bv_unsigned (getr R (reg 9))
| 38%nat => r | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => o | 41%nat => bv_unsigned (getr R (reg 19)) | _ => 0 end)) ltac:(first [assumption | unfold PMBIDP.aligned; lia | lia]).
destruct PE as (fxE1 & R9 & M9v & MG9 & _ & FZ9 & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E18 & E19).
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw8 M8 model8 fxD1 fxE1 R8 0xd7130 R9 0x7918c M9v K HH8 AM8 MS9 MG9 FZ9).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (R9tp : getr R9 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS9 4%nat) by inl; rewrite (L5SAR.cs_of_preserved RD1 R8 4 RP8) by inl; exact RDtp).
assert (ASTK9 : L5CA.astk ar M9 sp 14336) by (apply (L5SAR.astk_grows ar M8 M9 sp 14336 ASTK8 MGM9)).
apply (free_null_atA fxE1 R9 M9 model9 K LB FF LK cr Aw8 sp r HH9 AM9); [exact E10| exact E1| exact RAok| exact R9tp| exact E2| |exact K0|].
{ rewrite <- (Z.sub_0_r sp). apply (L5SAR.astack_ok_of_astk L ar C LYa M9 M9 sp 14336 0 4096 ASTK9 (fun _ X => X)); [lia|lia|lia| rewrite Z.sub_0_r; exact A16]. }
intros R10 M10 model10 Aw10 RP10 AP10 MR10 INC10 AM10 HH10.
assert (CS9 : forall k, In k L5SAR.cs_all -> getr R9 (reg k) = getr R (reg k)).
{ intros k Hk. unfold L5SAR.cs_all in Hk.
repeat (destruct Hk as [<-|Hk];
[ first [ rewrite E2; exact (eq_sym Rsp)
| rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned
| rewrite (KS9 _) by inl; rewrite (L5SAR.cs_of_preserved RD1 R8 _ RP8) by inl; rewrite (KSD _) by inl;
rewrite (L5SAR.cs_of_preserved RC1 R6 _ RP6) by inl; rewrite (KSC _) by inl;
rewrite (L5SAR.cs_of_preserved RB1 R4 _ RP4) by inl; rewrite (KSB _) by inl;
rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
destruct Hk. }
apply (KONT fxE1 R10 M10 model10 LK Aw10).
- apply (L5SAR.regs_preserved_trans R R9 R10); [apply L5SAR.preserved_by_index; intros k Hk; exact (CS9 k Hk)| exact RP10].
- assert (EKA : L5SAR.ek L ar LB FF sp 14336 [(o, 152)] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 14336 [(o, 152)] M M1 _ FR1). intros a Ha Hc O X.
destruct X as [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
- apply (O (o, 152)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (EKR : forall Ma Mb Mc, (forall a, 0 <= a < 2 ^ 64 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
aheap_pres L ar LB FF (sp - 48) 4096 Mb Mc -> L5SAR.ek L ar LB FF sp 14336 [(o, 152)] Ma Mc).
{ intros Ma Mb Mc EQ AP. intros a Hk. pose proof (L5SAR.ek_rt L ar LB FF [] sp 14336 (sp - 48) 4096 [(o, 152)] Mb Mc AP ltac:(lia) ltac:(lia) a Hk) as X.
rewrite X. apply EQ. destruct Hk as (Ha & _). exact Ha. }
assert (DKR : forall Ma Mb Mc, (forall a, 0 <= a < 2 ^ 64 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
aheap_pres L ar LB FF (sp - 48) 4096 Mb Mc -> L5SAR.dk L ar LB FF sp 14336 Ma Mc).
{ intros Ma Mb Mc EQ AP a Ha Hc HM. apply (L5SAR.dk_rt L ar LB FF [] sp 14336 (sp - 48) 4096 Mb Mc AP ltac:(lia) ltac:(lia) a Ha Hc). rewrite EQ by exact Ha. exact HM. }
apply (L5SAR.ahpres_of L ar LB FF sp 14336 [(o, 152)] M M10).
+ apply (L5SAR.ek_trans L ar LB FF sp 14336 [(o, 152)] M M8 M10).
* apply (L5SAR.ek_trans L ar LB FF sp 14336 [(o, 152)] M M6 M8); [| exact (EKR M6 MD1 M8 ED1 AP8)].
apply (L5SAR.ek_trans L ar LB FF sp 14336 [(o, 152)] M M4 M6); [| exact (EKR M4 MC1 M6 EC1 AP6)].
apply (L5SAR.ek_trans L ar LB FF sp 14336 [(o, 152)] M M1 M4); [exact EKA| exact (EKR M1 MB1 M4 EB1 AP4)].
* intros a Hk. pose proof (L5SAR.ek_rt L ar LB FF [] sp 14336 sp 4096 [(o, 152)] M9 M10 AP10 ltac:(lia) ltac:(lia) a Hk) as X.
rewrite X. apply FR9. destruct Hk as (Ha & _). exact Ha.
+ pose proof (L5SAR.astk_after_rt L ar C HI HIok LB FF LK cr Aw8 M9 M9 M10 _ sp 14336 sp 4096 HH9 ASTK9 (fun _ X => X) AP10 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & D10 & _).
exact D10.
+ apply (L5SAR.dk_trans L ar LB FF sp 14336 M M8 M10).
* apply (L5SAR.dk_trans L ar LB FF sp 14336 M M6 M8); [| exact (DKR M6 MD1 M8 ED1 AP8)].
apply (L5SAR.dk_trans L ar LB FF sp 14336 M M4 M6); [| exact (DKR M4 MC1 M6 EC1 AP6)].
apply (L5SAR.dk_trans L ar LB FF sp 14336 M M1 M4); [apply (L5SAR.dk_grows L ar LB FF sp 14336 M M1 MGM1)| exact (DKR M1 MB1 M4 EB1 AP4)].
* intros a Ha Hc HM. apply (L5SAR.dk_rt L ar LB FF [] sp 14336 sp 4096 M9 M10 AP10 ltac:(lia) ltac:(lia) a Ha Hc). rewrite FR9 by exact Ha. exact HM.
- apply (L5LZ.model_rt_trans model model9 model10); [|exact MR10].
apply (L5LZ.model_rt_trans model model8 model9); [|exact MRT9].
apply (L5LZ.model_rt_trans model modelD1 model8); [|exact MR8].
apply (L5LZ.model_rt_trans model model6 modelD1); [|exact MRTD1].
apply (L5LZ.model_rt_trans model modelC1 model6); [|exact MR6].
apply (L5LZ.model_rt_trans model model4 modelC1); [|exact MRTC1].
apply (L5LZ.model_rt_trans model modelB1 model4); [|exact MR4].
apply (L5LZ.model_rt_trans model model2 modelB1); [exact (L5LZ.model_rt_trans model model1 model2 MRT1 MRT12)| exact MRTB1].
- intros x Hx. exact Hx.
- intros x Hx. apply INC10. apply INC8. apply INC6. apply INC4. exact Hx.
- exact AM10.
- exact HH10.
Qed.
End WithHeap.
End PMBID.
