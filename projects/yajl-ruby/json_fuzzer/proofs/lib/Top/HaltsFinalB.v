(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr Nodes NodesCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import
  B_base B_alloc_iface B_iface B_iface5x BF_unwind BF_fakestack_rep B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_init5 B_instD5 B_inst5 BDrv_ctx BDrv_A BDrv_E
  BF_alloc_iface BF_free_iface BF_mallocT2 BF_reallocT BF_freeT2 BF_dput_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg RunInitCfg R_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopB Require B_MainMS B_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BF_deallocT2 BF_deallocT3 BF_deallocT5 BF_deallocT7 BF_dputT BF_qrep BF_caframe BF_allocT5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require B_MainReach5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import HaltsGen HaltsSpec HaltsGlue HaltsGlueLim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section BHyps.
  Context {RC__ : RunCeiling}.
  Lemma B_ALLOC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_allocT5.allocate_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK).
  Qed.
  Lemma B_R3 : forall E0, env0_ok5 E0 -> BF_deallocT3.R3_stmt E0.
  Proof.
    intros E0 ENV0. pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC0 & _).
    exact (BF_qrep.R3_holds E0 IC0).
  Qed.
  Lemma B_RECYC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    BF_deallocT5.recycle_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_deallocT7.recycle_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK).
  Qed.
  Lemma B_DEALLOC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_deallocT5.dealloc_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK
             (B_R3 E0 ENV0)
             (B_RECYC E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK)).
  Qed.
End BHyps.


(* [comment removed for export] *)
Lemma B_realizes_init : forall en inp,
  valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input inp ->
  realizes_cfg acfg bsegs
    (init_config bsegs b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
       target_alloc_limit inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros en inp VE VI.
  apply (B_MainReach5.b_main_reach en inp (spec (in_argv inp) (in_fs inp)) VE VI (R_TopCfg.spec_nil _ _)).
  intros E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM.
  (* [comment removed for export] *)
  exact (B_TopCfg.b_main_rz (@B_ALLOC) (@B_DEALLOC) en inp VE VI E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM).
Qed.

Theorem halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [Z_to_bv 64 0; Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  apply (halts_allowed_of_realizes_init_big acfg bsegs b_init_pc b_phdrs target_alloc_limit source_alloc_limit
           halts_codes (fun inp => spec (in_argv inp) (in_fs inp))).
  - unfold source_alloc_limit, target_alloc_limit. lia.
  - exact B_realizes_init.
  - intros inp _. apply spec_exits_in.
Qed.
