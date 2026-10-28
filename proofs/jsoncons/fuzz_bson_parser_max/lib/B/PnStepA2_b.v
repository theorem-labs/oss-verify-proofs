(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx
     AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b
     L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b PmSpecsA_b PnSpecsAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMKA2.
Import L5A. Import L5CA.
Section WithIface.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma apiece_img LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> aclientw L ar LB FF 0 0 a /\ ~ hl_rt_ro L a) ->
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid A model a = false -> M1 a = M1v a) ->
      srealizes RSEGS SCFG (L5A.cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH [Hh MI] MS MG FZ WC KONT.
  pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (L5SAR.vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & _).
  set (H := ahid A model) in *.
  unfold L5A.cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
  assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
  apply (KONT M1 model1).
  - rewrite VML. apply (HAJ.aior_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
    + intros a Ha Hp. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
      * exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * exact (C2 Hp).
      * exact (L5SAR.aclientw_not_bshadow L ar C HI LY HIok LB FF LK cr A M _ 0 0 a HH C1 Hp).
    + exact MGM1.
  - split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
  - apply L5LZ.sbm_model_rt. exact SBM1.
  - apply L5LZ.sbm_ahid. exact SBM1.
  - exact M1vis.
  - exact MGM1.
  - exact FRM1.
  - intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.
End WithIface.

(* [comment removed for export] *)
Lemma rt_ro_bss (L : asan_layout) (C : asan_statics_cells) a : PMA.layout L C -> 0x139000 <= a -> ~ hl_rt_ro L a.
Proof. intros LYJ Ha X. pose proof (PMA.ly_ro L C LYJ a X). lia. Qed.

End PMKA2.
