(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9IcptLayout Pm9L5DefsA Pm9ArtFsInv Pm9ArtIfaceInst Pm9ArtIfaceInstX PmLibAssemblyCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9IslandA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import IslCgCB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISAI9.
Abbreviation IC := PMLA.C_cboth.
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

Lemma art_footc2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.
Proof.
  intros a (iv & Hin & Hr). cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro.
  cbn [PMLA.FOOT PMLA.C_cboth In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma art_guardc : forall a, ISA9.GUARD <= a < ISA9.GUARD + 8 -> ~ hl_rt_static art_L a.
Proof. intros a Ha. cbn [art_L hl_rt_static]. unfold art_static. unfold ISA9.GUARD in Ha. lia. Qed.
Lemma art_memset_libc : CRC.amemset_spec_at art_L ar HI ISA9.PC_MEMSET.
Proof.
  replace ISA9.PC_MEMSET with (iclx_memset ILX) by (rewrite (aiclx_memset ILX ILXok); reflexivity).
  intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt).
Qed.
Lemma art_memcmp_libc : CRC.amemcmp_spec_at art_L ar HI ISA9.PC_MEMCMP ISA9.MC_SCR.
Proof.
  replace ISA9.PC_MEMCMP with (iclx_memcmp2 ILX) by (rewrite (aiclx_memcmp2 ILX ILXok); reflexivity).
  replace ISA9.MC_SCR with (iclx_scr_memcmp ILX) by (rewrite (aiclx_scr_memcmp ILX ILXok); reflexivity).
  intros fx R M model LB FF LK cr A p q n b1 b2 Kt. exact (pic_memcmp2 _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A p q n b1 b2 Kt).
Qed.
Lemma art_poi_ms : Forall (fun r : Z * Z => 0x690ce8 <= fst r \/ snd r <= 0x690bf8) (icl_poison IL).
Proof. rewrite (aicl_poison IL ILok). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.
Lemma art_poi_ro : Forall (fun r : Z * Z => 0x30808 <= fst r \/ snd r <= 0x307d8) (icl_poison IL).
Proof. rewrite (aicl_poison IL ILok). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Theorem locale_ctor_first_art_cg : ICG.locale_ctor_first_specA_cg art_L ar HI IC ISA9.PC.
Proof.
  exact (ISA9.locale_ctor_first_ok art_L ar art_C HI IL (pio_base _ _ _ _ _ _ HIok) ASMCB.art_lay ASMCB.art_tp art_footc2 art_guardc
           art_memset_libc art_memcmp_libc (pic_img_shadow _ _ _ _ _ _ _ ICok) art_poi_ms art_poi_ro).
Qed.
Theorem locale_ctor_first_art : PMSA.locale_ctor_first_specA art_L ar HI IC ISA9.PC.
Proof. exact (ICG.cg_weaken art_L ar HI IC _ locale_ctor_first_art_cg). Qed.
End Inst.
End ISAI9.
