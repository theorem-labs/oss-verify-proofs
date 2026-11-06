(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4IcptLayout Pm4L5DefsA Pm4ArtFsInv Pm4ArtIfaceInst Pm4ArtIfaceInstX PmLibAssemblyXA PmInfraXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4IslandA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISAI4.
Abbreviation IC := PMLA.C_xasan.
Section Inst.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Variable ANNOTATE : Prop.
Hypothesis ILok : as0_icpt_layout IL.
Hypothesis ILXok : pm_icpt_layout_x ILX.
Hypothesis HIok : pm_asan_iface_ok art_L art_LX ar art_C scfg HI.
Hypothesis ICok : pm_aicpt_ok art_L ar IL ILX scfg HI ANNOTATE.

Lemma art_guardc : forall a, ISA4.GUARD <= a < ISA4.GUARD + 8 -> ~ hl_rt_static art_L a.
Proof. intros a Ha. cbn [art_L hl_rt_static]. unfold art_static. unfold ISA4.GUARD in Ha. lia. Qed.
Lemma art_memset_libc : CRC.amemset_spec_at art_L ar HI ISA4.PC_MEMSET.
Proof.
  replace ISA4.PC_MEMSET with (iclx_memset ILX) by (rewrite (aiclx_memset ILX ILXok); reflexivity).
  intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt).
Qed.
Lemma art_memcmp_libc : CRC.amemcmp_spec_at art_L ar HI ISA4.PC_MEMCMP ISA4.MC_SCR.
Proof.
  replace ISA4.PC_MEMCMP with (iclx_memcmp2 ILX) by (rewrite (aiclx_memcmp2 ILX ILXok); reflexivity).
  replace ISA4.MC_SCR with (iclx_scr_memcmp ILX) by (rewrite (aiclx_scr_memcmp ILX ILXok); reflexivity).
  intros fx R M model LB FF LK cr A p q n b1 b2 Kt. exact (pic_memcmp2 _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A p q n b1 b2 Kt).
Qed.
Lemma art_poi_ms : Forall (fun r : Z * Z => 0x69cf28 <= fst r \/ snd r <= 0x69ce38) (icl_poison IL).
Proof. rewrite (aicl_poison IL ILok). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.
Lemma art_poi_ro : Forall (fun r : Z * Z => 0x306a8 <= fst r \/ snd r <= 0x30678) (icl_poison IL).
Proof. rewrite (aicl_poison IL ILok). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Theorem locale_ctor_first_art : PMSA.locale_ctor_first_specA art_L ar HI IC ISA4.PC.
Proof.
  exact (ISA4.locale_ctor_first_ok art_L ar art_C HI IL (pio_base _ _ _ _ _ _ HIok) ASMXA.art_lay ASMXA.art_tp ASMXA.art_footc2 art_guardc
           art_memset_libc art_memcmp_libc (pic_img_shadow _ _ _ _ _ _ _ ICok) art_poi_ms art_poi_ro).
Qed.
End Inst.
End ISAI4.
