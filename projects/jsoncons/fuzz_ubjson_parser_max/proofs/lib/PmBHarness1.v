(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmBHarnessStmts PmBHarnessKit PmBHarnessP1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKRB0.L5AFKR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1list"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LB"]; ["0LK"; "0LK2"; "4Model"; "4event"; "5bvmap"; "0M"; "0M2"; "0M3"; "0R"; "0R3"; "6credit"; "7ff_room"; "7ff_rs"; "7fframe"; "7hl_tp"; "7ri_inv"]; ["7shadow_zero"; "7vml_of"; "9ra_ok"; "9range"; "8SCFG"; ":cfg"; ";STK"; ";rinvH"; ";tfrk"; ";tocell"; "<AADDR_B"; "<ADDR_B"; "=st"; ">ls_okA"; "?FPState"; "?getr"]; ["@TSet"; "Asrealizes"; "Bbinv"; "Bgctx"; "Camodel_ok"; "Castk"; "Dloaded_segments"; "0SCFG_P"; "EIn"; "Fadd"; "Fle"; "Flt"; "Fmodulo"; "Fof_nat"; "Fpow"; "Fsub"]; ["0V2"; "0W"; "0ar"; "0cls"; "0cr"; "0data"; "0f"; "0fl"; "0fx"; "0fx3"; "0g"; "0model"; "0model2"; "0model3"; "0n"; "0r"]; ["0sp"; "GBV"; "GZ_to_bv"; "Gbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA1.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma entry : ltac2:(TCodec.tc2 tcn__PmBHarness1 "YK'1&Q3%211'Q>&Dy5'RCyR0%211%5241'3y8%611%311p061'B&Q@'4'9%2211%D11&M%F11&J'Q<&Ov<r:r9r8r7r6r=&Q1r<%211%;8:9876541&QD%1286(2'C%211%:11'7&Q?rA(RA+:(5%33Q<21%6251&RB%12Q=G%:3Q=31rB+;%:3QC18%=231%?3QB16'6&QJz%221Q2&QK&QN+2+J%3221%52Q81%:271r;%;2:1+R0%9281%;241%@241rE+1%Q03R91N%Q3231%M2R9QD%Q63R921&Q2%11QHrG%Q73R@DQ5%Q:221%Q42R@QE%Q=3R@21&QL+@%22QK1%QA3R:1OrI+4%QA3RJ1Q?%QD231&Nv>%211%QA2RM1%QJ3RM51&QEvR2r?&Q6%443=21&KrF%23?1Q1&QHr1rH%33RL21&QIrC+Q0%3221&Lr2%211%QM241p091pT>S61&Q=&QF&Q;&Q:r@rL%6554321'QCrQ5rQ4rQ3rQ1%F2R2S=&QO+T0%22R51&Q9%115&Q8rQ9%2281r5rQ2%@EQAQ<SI?>=<;Q:88;63SGSFQESESD21rO%Q32SCR?%S;3T421'8%S=3T6SFRK%S>3T7SGQO%3221r>%R321Q8%SB3T;1S0+SoomohPTV0%S321QG+TPPPPPPPP0%S52QI1%S7231%QA2Q3QK%S8214&QBrQ>rQ=rQ;rQ:rQ7%QI2SNQ;%Q32SOQ2rQ?%Q0231rQA%T91TMrQ8%=FR@R;TH<;:9Q387R964R:RD32TETDTB18&Q7rQ@%251TJSOT8QE&QMu1%211%T62UD1%T>2SD1+doPD%T92UE1%TB3UE31u:%911%T=2UK1%TE2TO1%R@2T<R>%T@2UL1%TI3UL31u;%@11%TD2V21%TL2U81%TF2V2Q0%TO3V221u<%F11%TJ2V81%U22QC1%U43V716uE%K11%TO2V=1%U72S;1+S0%S32T91%U32V?1%U<3V?41uF%Q311%U72VE1%U?2RK1rQ<%U:2VF1%UC3VF31uG%Q:11%U>2VL1%UF2UE1%U@2VLQM%UI3VL21&Q0%SD2SFSB+3%33UK21+QP0%TA2T=1%V03VI1U>%S@5S?S>S=R5SI'QA&Q4vQG%211&Q5+ePi<rD%35T8U821T1rQH%94SI621p0;1p0=1p0A1p0F1p0M1p0Q51p0Q>1p0QD1p0QK1p0R31p0R<1p0R@1p0RO1p0S21p0S81p0S<1p0SA1p0SE1pTLWJ1pQ@WL1pQDX21pTDX91pTJWN1pQ>X01pQ4WI1pT@WN1pFWO1pT8X01pT2X11rQ0+dnXLrNrM%Q754T4321%Q<4TLQ91THp071p0TI1p0U11p0U@1p0UD1p0UJ1p0V41p0V91p0V?1p0VB1p0VI1p0W01p0W<1p0WB1p0WN1p0X31p0X61pTFXC1pU0XJ1pU2XK1pTNXL1pT<XM1p2XL1pT:XJ1pQ2XL1pHXM1pQ0Y01pLY51pTHY71pQ<Y91pQBY?1pTBYF1pT4YH1").
Proof. intros W fx R M model K LB FF LK cr A data n sp r g.
intros HH AM HK G10 G11 NR DRG G1 RA G2 A16 G4 STKh FFR4 FFRS LS KONT.
pose proof STKh as (_ & SLO & SHI & SPT & DSCR & DUP).
assert (CLSX : exists cls, (cls = 0 \/ cls = 16) /\ (sp - cls) mod 32 = 0).
{ clear - A16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (X : sp mod 32 = 0 \/ sp mod 32 = 16) by lia. destruct X as [X|X]; [exists 0 | exists 16]; split; [left; reflexivity | lia | right; reflexivity | lia]. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct CLSX as (cls & CLS & V2A0). set (V2 := sp - cls) in *.
assert (SE : sp = V2 + cls) by (subst V2; clear; lia).
unfold STK in *.
assert (V2R : 140735332487360 <= V2 <= 140737488355328 /\ 0 <= V2 < 2 ^ 64 /\ V2 + cls <= 140737488355328) by (subst V2; clear - SLO SHI SPT CLS; lia).
destruct V2R as (V2R & V2RG & V2S).
pose proof (vis_pack L ar C HI LYa HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
pose proof (L5ADHR.statics_vis L ar C HI LYa HIok LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
assert (WSv : L5.writable RSEGS MV (V2 - 128) (128 + cls)).
{ apply (proj2 (writable_vis H M (V2 - 128) (128 + cls) (VIS (V2 - 128) (128 + cls) ltac:(subst V2; clear - SLO CLS; lia) ltac:(clear - V2R CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - V2R CLS; lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 36864) 36864); [exact DSCR| subst V2; clear - CLS; lia| subst V2; clear - CLS; lia]| clear - V2R; lia| clear - V2R CLS; lia]. }
assert (EXA : exists (fx1 : FPState) R1 M1v, msteps RSEGS (st fx R 0xa791c MV) (st fx1 R1 0x5db48 M1v) /\ mem_grows MV M1v
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (V2 - 128 <= i < V2 + cls) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
/\ getr R1 (reg 1) = Z_to_bv 64 0xa798c /\ getr R1 (reg 2) = Z_to_bv 64 (V2 - 128) /\ getr R1 (reg 8) = Z_to_bv 64 (V2 + cls)
/\ getr R1 (reg 9) = Z_to_bv 64 (V2 - 128) /\ getr R1 (reg 10) = Z_to_bv 64 1024 /\ getr R1 (reg 25) = Z_to_bv 64 2147450880
/\ getr R1 (reg 22) = Z_to_bv 64 n /\ getr R1 (reg 23) = Z_to_bv 64 data
/\ getr R1 (reg 3) = getr R (reg 3) /\ getr R1 (reg 4) = getr R (reg 4) /\ getr R1 (reg 27) = getr R (reg 27) /\ tfrk (V2 + cls) R M1v).
{ assert (G2' : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- L5K.rl2, G2, SE; reflexivity).
assert (G10' : getr R (reg 10) = Z_to_bv 64 data) by (rewrite <- L5K.rl10; exact G10).
assert (G11' : getr R (reg 11) = Z_to_bv 64 n) by (rewrite <- L5K.rl11; exact G11).
assert (NRG : 0 <= n < 2 ^ 64) by (clear - NR; lia).
destruct CLS as [E|E]; rewrite E in *.
- assert (W0 : L5.writable RSEGS MV (V2 - 128) 128) by (eapply L5.writable_sub; [exact WSv | clear; lia | clear; lia]).
pose proof (PMBHP1.haA0_conc fx R MV (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
feed P ltac:(first [ exact W0 | hsc | (rewrite Z.add_0_r in G2'; exact G2') ]).
destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR22 & aR23 & aR25 & aCS)).
exists fx1, R1, M1v. split. exact aMS. split. exact MG1. split. { intros i Hi Hn. apply aFZ. exact Hi. clear - Hn; lia. }
split. exact aR1. split. exact aR2. split. { rewrite aR8. f_equal. clear; lia. } split. exact aR9. split. exact aR10. split. exact aR25.
split. exact aR22. split. exact aR23.
split. apply aKS; inl. split. apply aKS; inl. split. apply aKS; inl. unfold tfrk, U. decompose [and] aCS. repeat split; gmem.
- assert (W0 : L5.writable RSEGS MV (V2 - 128) 144) by (eapply L5.writable_sub; [exact WSv | clear; lia | clear; lia]).
pose proof (PMBHP1.haA16_conc fx R MV (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
feed P ltac:(first [ exact W0 | hsc ]).
destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR22 & aR23 & aR25 & aCS)).
exists fx1, R1, M1v. split. exact aMS. split. exact MG1. split. { intros i Hi Hn. apply aFZ. exact Hi. clear - Hn; lia. }
split. exact aR1. split. exact aR2. split. exact aR8. split. exact aR9. split. exact aR10. split. exact aR25.
split. exact aR22. split. exact aR23.
split. apply aKS; inl. split. apply aKS; inl. split. apply aKS; inl. unfold tfrk, U. decompose [and] aCS. repeat split; gmem. }
destruct EXA as (fx1 & R1 & M1v & aMS & MG1 & aFZ & aR1 & aR2 & aR8 & aR9 & aR10 & aR25 & aR22 & aR23 & aR3 & aR4 & aR27 & FRK1v).
set (W1 := fun a => V2 - 128 <= a < V2 + cls).
apply (apiece L ar C HI LYa HIok LB FF LK cr A M model fx fx1 R 0xa791c R1 0x5db48 M1v W1 K HH AM aMS MG1).
{ intros a Ha Hna. apply aFZ. exact Ha. exact Hna. }
{ intros a Ha Wa. subst W1; cbn beta in Wa. split. apply stack_client. subst V2; clear - Wa SLO SHI SPT CLS; lia. clear; lia. clear - Wa V2R; lia. }
intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
assert (LS1 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M1) by (apply (PMHAK.ls_piece g M M1 W1 FRM1); [intros a Wa; subst W1; cbn beta in Wa; clear - Wa V2R; lia| exact LS]).
pose proof (HAJ.aior_stack_malloc _ _ _ _ _ HIok 4 ltac:(right; right; right; right; left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
rewrite (aly_segs L C LYa), (PMB.ly_sm L C LY 4 ltac:(right; right; right; right; left; reflexivity)), (aly_scr_sm L C LYa) in SM. cbn [PMB.SM_PC nth Z.to_nat Pos.to_nat] in SM.
assert (U2 : bv_unsigned (getr R1 2%bv) = V2 - 128). { rewrite L5K.rl2, aR2. apply L5.unsigned_lit. clear - V2R; lia. }
assert (SA16 : (V2 - 128) mod 16 = 0 /\ (V2 - 128) mod 32 = 0). { clear - V2A0. subst V2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
- rewrite L5K.rl4, aR4, <- L5K.rl4. exact G4.
- rewrite L5K.rl1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
- rewrite U2. replace (V2 - 128) with (sp - (128 + cls)) by (subst V2; clear; lia).
apply (astack_ok_of_astk L ar C LYa M M1 sp 36864 (128 + cls) 512 STKh MGM1). clear - CLS; lia. clear; lia. clear - CLS; lia.
replace (sp - (128 + cls)) with (V2 - 128) by (subst V2; clear; lia). exact (proj1 SA16).
- exact FFR4.
- intros f Hf. rewrite U2. specialize (FFRS f Hf). subst V2; clear - FFRS CLS. lia.
- exact HK.
- intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite L5K.rl1, aR1.
assert (LS2 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M2).
{ apply (PMHAK.ls_agree g M1 M2); [| exact LS1]. intros a Ha X. apply (proj1 PRES2 a Ha). exact (PMHAK.stat_client L C LY ar LB FF (V2 - 128) 512 a (fun x X => X) X). }
pose proof (sm_facts L ar C HI LYa HIok LB FF LK2 cr A M2 model2 F 4 (V2 - 128 + 32) fl HH2 ltac:(right; right; right; right; left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
assert (ASTK2 : astk ar M2 sp 36864).
{ apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (V2 - 128) 512 HH STKh MGM1 PRES2). subst V2; clear - CLS; lia. subst V2; clear - CLS; lia. clear; lia. }
pose proof (vis_pack L ar C HI LYa HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
pose proof (L5ADHR.statics_vis L ar C HI LYa HIok LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
assert (SVIS : forall a, V2 - 128 <= a < V2 + cls -> H (Z_to_bv 64 a) = false).
{ intros a Ha. replace a with ((V2 - 128) + (a - (V2 - 128))) by (clear; lia). apply (VIS (V2 - 128) (128 + cls)). subst V2; clear - SLO CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
assert (AG2 : forall a, V2 - 128 <= a < V2 + cls -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
{ intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((V2 - 128) + (a - (V2 - 128))) by (clear; lia). apply (VIS2 (V2 - 128) (128 + cls)). subst V2; clear - SLO CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
rewrite (proj1 PRES2 a). 2:{ clear - Ha V2R CLS; lia. } 2:{ apply stack_client. subst V2; clear - Ha SLO SHI SPT CLS; lia. clear - Ha; lia. }
rewrite <- VIS1. symmetry. apply mrestrict_visible. apply SVIS. exact Ha. }
assert (W128b : L5.writable RSEGS MV2 (V2 - 128) 128).
{ eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj CLS; lia. clear - V2R; lia. clear - V2R; lia. eapply L5.writable_grows. exact MG1. eapply L5.writable_sub. exact WSv. clear; lia. clear - CLS; lia. }
pose proof (sm_apart L ar C HI LYa HIok LB FF LK2 cr A M2 _ F 4 _ fl sp 0 (V2 - 128) (128 + cls) HH2 SPT ltac:(right; right; right; right; left; reflexivity)
ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
ltac:(intros i Hi; apply stack_client; subst V2; clear - Hi SLO SHI SPT CLS; lia) ltac:(clear - CLS; lia)) as (SF & SFSH & SFL).
change (ff_bytes 4) with 1024 in SF. change (ff_bytes 4 / 8) with 128 in SFSH.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (FQ : (F + 1024 - 1) / 8 = F / 8 + 128 - 1 /\ F mod 8 = 0 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0) by (clear - F8; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (NCF : forall a, (F <= a < F + 1024 \/ HeapIfaceA.S F <= a <= HeapIfaceA.S (F + 1024 - 1)) -> ~ aclient L ar LB FF sp 36864 a).
{ intros a Ha. apply (fresh_frame_not_client L ar C HI LYa HIok LB FF LK cr A M _ sp 36864 F 1024 a HH SPT).
clear - FR; lia. exact FCEIL. exact FAPP. exact (proj1 (proj2 FQ)). clear; lia. reflexivity.
eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
assert (NCS : forall a, V2 - 128 <= a < sp -> ~ aclient L ar LB FF sp 36864 a).
{ intros a X Hc. destruct (aclient_cases L ar C HI LYa HIok LB FF LK cr A M _ sp 36864 a HH SPT Hc) as [Y|Y]. subst V2; clear - X Y CLS; lia. subst V2; clear - X Y SLO CLS; lia. }
assert (EK2 : ek L ar LB FF sp 36864 W M M2).
{ eapply ek_trans. { apply (ek_piece L ar LB FF sp 36864 W M M1 W1 FRM1). intros a Ha Hc _ X. subst W1; cbn beta in X. apply (NCS a). rewrite SE. exact X. exact Hc. }
apply (ek_rt L ar LB FF [] sp 36864 (V2 - 128) 512 W M1 M2 PRES2). subst V2; clear - CLS; lia. subst V2; clear - CLS; lia. }
assert (DK2 : dk L ar LB FF sp 36864 M M2).
{ eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_rt L ar LB FF [] sp 36864 (V2 - 128) 512 M1 M2 PRES2). subst V2; clear - CLS; lia. subst V2; clear - CLS; lia. }
assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 4096 <= F <= 140737488354304 /\ 4096 <= fl <= 140737488355327) by (clear - FR FLR; lia). destruct FRG as (FRG & FLRG & FRP & FLRP).
assert (ALF : PMBHP1.aligned F 32) by exact F32.
assert (SFA : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; subst V2; lia).
assert (SFLA : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; subst V2; lia).
assert (FIMG' : 65536 + 6828032 <= F \/ F + 1024 <= 65536) by (clear - FR; lia).
assert (FLIMG' : 65536 + 6828032 <= fl \/ fl + 1 <= 65536) by (clear - FLR; lia).
assert (FLCv' : L5.u64_at RSEGS MV2 (F + 1016) fl). { replace (F + 1016) with (F + 1024 - 8) by (clear; lia). exact FLCv. }
assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (V2 - 128)) by rk.
assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 (V2 - 128)) by rk.
assert (R2_22 : getr R2 (reg 22) = Z_to_bv 64 n) by rk.
assert (R2_23 : getr R2 (reg 23) = Z_to_bv 64 data) by rk.
assert (R2_25 : getr R2 (reg 25) = Z_to_bv 64 2147450880) by rk.
assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact B10).
pose proof (PMBHP1.haB_conc fx1 R2 MV2 (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R2 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - NR; lia) | (clear - V2R; lia) | exact FSHZ | exact FSHW | exact FWv | exact FDEFv | exact W128b | hsc ]).
destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & _ & _ & bR18 & bR19 & bR20 & bR21 & bR24 & BQ)).
set (W3 := fun a => V2 - 112 <= a < V2 - 112 + 8 \/ F <= a < F + 24 \/ F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 128).
apply (apiece L ar C HI LYa HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0xa798c R3 0xa832c M3v W3 K HH2 (conj Hh2 MI2) bMS MG3).
{ intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
{ intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
- split. apply stack_client. subst V2; clear - Wa SLO SHI SPT CLS; lia. clear; lia. clear - Wa V2R; lia.
- split. apply (fframe_client L ar LB _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. clear - Wa; lia. clear - Wa FR; lia.
- split. apply (fframe_shadow_client L ar LB _ 0 0 F 4 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 4) with 1024. unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 FQ). clear - Wa. unfold SB in *. lia.
clear - Wa FR; lia. }
intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
assert (LS3 : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD g M3).
{ apply (PMHAK.ls_piece g M2 M3 W3 FRM3); [| exact LS2]. intros a Wa. subst W3; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa V2R FR. lia. }
decompose [and] BQ. clear BQ.
assert (G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 4 LK2 M2 model2 cr).
{ rewrite <- SE. refine (L5AFKR.GCTX L ar HI LB FF LK A sp 36864 (V2 - 128) (V2 - 128) sp (tocell sp) (tfrk sp R) F fl 4 LK2 M2 model2 cr
ltac:(right; right; right; right; left; reflexivity) SPT SLO SHI _ _ _ FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF _).
- subst V2; clear - SLO SHI SPT CLS; lia.
- intros a Ha. unfold tocell in Ha. subst V2; clear - Ha CLS; lia.
- intros Ma Mb OW AG. apply (tfrk_agree sp R Ma Mb ltac:(subst V2; clear - V2R CLS; lia) ltac:(clear - SHI SPT; lia) OW AG).
- change (ff_bytes 4) with 1024. clear - FR; lia.
- change (ff_bytes 4) with 1024. change (1024 / 8) with 128. split. exact F8. split. exact (proj1 FQ). reflexivity.
- exact NCS. }
assert (SV2 : forall a, V2 - 128 <= a < V2 + cls -> ahid A model2 (Z_to_bv 64 a) = false).
{ intros a Ha. replace a with ((V2 - 128) + (a - (V2 - 128))) by (clear; lia). apply (VIS2 (V2 - 128) (128 + cls)). subst V2; clear - SLO CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
assert (OWN3 : tfrk (V2 + cls) R M3).
{ apply (tfrk_agree (V2 + cls) R M1v M3 ltac:(clear - V2R CLS; lia) ltac:(clear - V2S; lia) FRK1v). intros a Ha. unfold tocell in Ha.
rewrite FRM3. 2: clear - Ha V2R CLS; lia. 2:{ subst W3; cbn beta. clear - Ha SF SFSH CLS. unfold HeapIfaceA.SB in *. lia. }
rewrite (L5ADHR.stack_rt L ar LB FF (V2 - 128) 512 M1 M2 a PRES2 ltac:(clear - Ha V2R CLS; lia) ltac:(subst V2; clear - Ha SLO SHI SPT CLS; lia) ltac:(clear - Ha CLS; lia)).
apply EQ1. apply SVIS. clear - Ha CLS; lia. }
assert (BI3 : L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4 W [] M3 model3 LK2 cr A).
{ rewrite <- SE. unfold L5AFKR.binv. split. exact HH3. split. exact AM3.
split. { eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3. }
split. apply incl_refl. split. exact LKI2. split. { eapply astk_grows. exact ASTK2. exact MGM3. }
split. { eapply ek_trans. exact EK2. apply (ek_piece L ar LB FF sp 36864 W M2 M3 W3 FRM3). intros a Ha Hc _ X. subst W3; cbn beta in X. destruct X as [X|[X|X]].
- apply (NCS a). subst V2; clear - X CLS; lia. exact Hc.
- apply (NCF a). left; clear - X; lia. exact Hc.
- apply (NCF a). right. unfold HeapIfaceA.S. rewrite (proj1 FQ). clear - X. unfold HeapIfaceA.SB in *. lia. exact Hc. }
split. { eapply dk_trans. exact DK2. apply dk_grows. exact MGM3. }
split. rewrite SE; exact OWN3.
change (ff_bytes 4 / 8) with 128. eapply L5.defined_grows. exact MGM3. intros i Hi. unfold shadow_zero, byte_at, HeapIfaceA.S in FSH. rewrite (FSH i Hi). discriminate. }
assert (RI3 : rinvH R R3 V2 cls F).
{ unfold rinvH. split. rk. split. rk. split. rk. split. exact bR18. split. exact bR19. split. exact bR20. split. exact bR24. split. rk.
split. { rewrite (bKS 3%nat) by inl. rewrite (cs_of_preserved R1 R2 3 RP2) by inl. exact aR3. }
split. { rewrite (bKS 4%nat) by inl. rewrite (cs_of_preserved R1 R2 4 RP2) by inl. exact aR4. }
rewrite (bKS 27%nat) by inl. rewrite (cs_of_preserved R1 R2 27 RP2) by inl. exact aR27. }
assert (SHV3 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 128 -> ahid A model2 (Z_to_bv 64 a) = false).
{ intros a Ha. replace a with ((F / 8 + HeapIfaceA.SB) + (a - (F / 8 + HeapIfaceA.SB))) by (unfold HeapIfaceA.SB; clear; lia). apply VSH. unfold HeapIfaceA.SB; clear - Ha; lia. }
assert (SZS3 : shadow_zero M3 (F + 32) 3).
{ intros j Hj. unfold byte_at, HeapIfaceA.S. rewrite (proj1 (proj2 (proj2 FQ))).
assert (X : L5.u8_at RSEGS M3v (F / 8 + 4 + HeapIfaceA.SB + j) 0).
{ assert (J : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia). unfold HeapIfaceA.SB. destruct J as [J|[J|J]]; subst j; gmem. }
rewrite EQ3. apply (L5ADHR.byte_of_u8 M3v _ 0 X). right. clear - Hj FR F8; unfold HeapIfaceA.SB; lia. clear - Hj FR F8; unfold HeapIfaceA.SB; lia.
apply SHV3. unfold HeapIfaceA.SB; clear - Hj; lia. }
apply (KONT V2 cls F fl LK2 M2 model2 fx3 R3 M3 model3 G SE CLS V2A0 ltac:(clear - V2R; lia) V2S BI3 RI3).
+ exact bR1.
+ exact bR10.
+ exact bR11.
+ exact bR12.
+ exact bR21.
+ rk.
+ rk.
+ exact SZS3.
+ exact FAL.
+ exact LS3.
Qed.
End WithIface.
End SCFG_1.
End PMHA1.
