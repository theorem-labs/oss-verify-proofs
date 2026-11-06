(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA AsanAcct BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR HeapIfaceAJx PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecsA PmSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAOpdel () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreSpecsA.L5CSA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1option"; "1pair"; "1prod"; "2I"; "2eq"; "3Z"; "0HI"; "0L"; "4fetch_word"; "4is_ecall"; "5decode_any"; "6Jal"; "6instr"]; ["7bvmap"; "0M"; "0R"; "8msteps"; "9opdel_spec_at"; ":opdel_sized_spec"; ":opdel_spec"; ";FPState"; ";btgt"; ";mkst"; ";seg_rom"; "<opdel_sized_spec"; "<opdel_spec"; "<opdel_spec_at"; "=loaded_segments"; "0SCFG_P"]; ["0W"; "0ar"; "0fx"; "0imm"; "0pc"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_signed"; "0tgt"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMAOPD.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Lemma j_to : ltac2:(TCodec.tc2 tcn__PmAOpdel "RD'G&@y5'Q7yR0%211%5241'3y8%611%311p061'8yQ0%;11yE%=11'7%;14&;&N&Q6r4%22C1%5241(0r2%22=1%;3:41'1&<r3%211(2%A3521'5'?%221I%O11&=%11B(4(>(Q5z(6%33Q<21%521@+4%84=Q521%I2=1%Q23=;1&Hr7%Q12QB1&Q8%12Q9Q2%5231r6%Q62QG1%Q;3QG31'C&Ir;r:r8%Q=2QN1r9&J%11QA%8576431%9587A42%;3QD21p0=1p0G1p0Q91p0Q@1pR8QM1pR2R01pRDR31pR:R41pQ4R61pQ6R<1pR6RC1").
Proof. intros fx R M pc tgt W imm.
intros HF HEC HD HT. eapply mst_step; [reflexivity | | apply mst_refl].
rewrite (step_jal_x0 RSEGS R _ M (seg_rom RSEGS) _ imm HF HEC HD). rewrite HT. reflexivity.
Qed.
Lemma j_cea54 : ltac2:(TCodec.tc2 tcn__PmAOpdel "O'G&@y5'Q7yR0%211%5241'3y8%611%311p061'C&N&Ir3r2&Q6+ijbD%22?1r1&J%119%9587431+_SeL%82E1%<5;:164%?3>41pQ4A1pQ6G1pR6N1").
Proof. intros fx R M. apply (j_to fx R M 0xcea54 0x78ebc _ _ (ltac:(oF' 0xcea54%Z)) eq_refl (ltac:(oD' 0xcea54%Z))). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma j_cea58 : ltac2:(TCodec.tc2 tcn__PmAOpdel "O'G&@y5'Q7yR0%211%5241'3y8%611%311p061'C&N&Ir3r2&Q6+ijbH%22?1r1&J%119%9587431+ijbD%82E1%<5;:164%?3>41pQ4A1pQ6G1pR6N1").
Proof. intros fx R M. apply (j_to fx R M 0xcea58 0xcea54 _ _ (ltac:(oF' 0xcea58%Z)) eq_refl (ltac:(oD' 0xcea58%Z))). apply bv_eq; vm_compute; reflexivity. Qed.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma opdel_at : ltac2:(TCodec.tc2 tcn__PmAOpdel "Q8'8'G&@y5'Q7yR0%211%5241'3y8%611%311p061'C&N&Ir3r2&Q6r4%22?1r1&J%119%9587431+_SeL%82E1%<5;:164%?3>41pQ4A1pQ6G1pR6N1&MvOv:vQ1v9%554D321p071pR:Q71").
Proof. intros pc.
intros JMP fx R M model K LB FF LK cr A q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPDEL_SCR, MALLOC_SCR in SLO, DSCR.
apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx R pc R 0x78ebc (mrestrict (ahid A model) M) K HH AM (JMP fx R _) (mem_grows_refl _)).
{ intros a Ha. reflexivity. }
intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
assert (E1 : M1 = M) by (apply mem_eq_of_agree; exact FRM1). subst M1.
pose proof (HAJ.aior_free _ _ _ _ _ HIok) as HF. unfold afree_spec in HF. rewrite (aly_segs L C LY), (aly_free L C LY), (aly_scr_free L C LY) in HF.
assert (U2 : bv_unsigned (getr R 2%bv) = sp). { rewrite G2. apply L5.unsigned_lit. clear - SLO SHI SPT; lia. }
eapply (HF fx R M model1 LB FF LK cr A q n K HH1 (proj1 AM1) (proj2 AM1) INQ G10 G4); clear HF.
- rewrite G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
- rewrite U2. pose proof (astack_ok_of_astk L ar C LY M M sp OPDEL_SCR 0 4096 STK (mem_grows_refl M)) as X.
replace (sp - 0) with sp in X by (clear; lia). apply X. clear; lia. clear; lia. unfold OPDEL_SCR, MALLOC_SCR; clear; lia. exact A16.
- exact HK.
- intros R' M' model' A' RP PRES RT2 IA MI2 HH2. rewrite U2 in PRES. rewrite G1.
apply (KONT fx R' M' model' A' RP).
+ split. { intros a (Ha & Hc & _). apply (proj1 PRES). exact Ha. exact Hc. }
split. { intros i Hi. apply (proj2 PRES). unfold OPDEL_SCR, MALLOC_SCR in *. clear - Hi; lia. }
intros a Ha Hc HM. destruct (rng_dec a (sp - 4096) sp) as [I|O]. apply (proj2 PRES). exact I.
rewrite (proj1 PRES a Ha). exact HM. exact Hc.
+ eapply L5LZ.model_rt_trans. exact RT1. exact RT2.
+ exact IA.
+ split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). exact MI2.
+ exact HH2.
Qed.
Theorem opdel_ok0 : ltac2:(TCodec.tc2 tcn__PmAOpdel "6&LvOv:vQ1v9%544321").
Proof. apply opdel_at. intros fx R M. apply j_cea54. Qed.
Theorem opdel_sized_ok0 : ltac2:(TCodec.tc2 tcn__PmAOpdel "6&KvOv:vQ1v9%544321").
Proof. apply opdel_at. intros fx R M. eapply msteps_trans. apply j_cea58. apply j_cea54. Qed.
End WithIface.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Lemma opdel_pma_at : ltac2:(TCodec.tc2 tcn__PmAOpdel ">'8&MvOr1v:vQ1v9%6554321&D&Nr2%36927651p051pR:=1").
Proof. intros pc.
intros OK fx R M model K LB FF LK Aw cr q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT.
exact (OK fx R M model K LB FF LK cr Aw q n sp r HH AM HK INQ G10 G1 RA G2 G4 STK KONT).
Qed.
Theorem opdel_ok : ltac2:(TCodec.tc2 tcn__PmAOpdel "6&FvOv:vQ1v9%544321").
Proof.
apply opdel_pma_at. change (pa_opdel PMA.AD) with 0xcea58.
apply (opdel_at L ar C HI (PMA.ly_as0 L C LY) HIok). intros fx R M. eapply msteps_trans. apply j_cea58. apply j_cea54.
Qed.
Theorem opdel_sized_ok : ltac2:(TCodec.tc2 tcn__PmAOpdel "6&EvOv:vQ1v9%544321").
Proof.
apply opdel_pma_at. change (pa_opdel_sized PMA.AD) with 0xcea54.
apply (opdel_at L ar C HI (PMA.ly_as0 L C LY) HIok). intros fx R M. apply j_cea54.
Qed.
End WithHeap.
End SCFG_1.
End PMAOPD.
