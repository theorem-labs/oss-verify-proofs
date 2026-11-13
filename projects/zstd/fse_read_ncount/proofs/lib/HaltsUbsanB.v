(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: made from this harness's proofs/lib/HaltsPlainB.v at commit f92feaf8b7 for the UBSan build: its image, names and limit lemma are changed from the plain build's to the UBSan build's, its imports leave out PlainTree and images.Plain and add ModelInv, ModelOK, Ubsan.UImgX and Ubsan.PlainClosed, and its two comments are left out; ubsan_tree_ok_L is ubsan_tree_ok from proofs/lib/UbsanMain.v, lines 20-27, restated for any limit of at least 2^31 after the form of proofs/lib/PlainTree.v, lines 12-19, with the UBSan build's facts in place of the plain build's from proofs/lib/Spec/ModelOK.v, lines 39-43. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel TopLevelHaltsB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prog ProgExits ModelInv ModelOK ImgFacts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Require OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan.PlainClosed.

Lemma lim31_sourceU : (2^31 <= ShippedBudgets.lim_source)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem ubsan_tree_ok_L : forall L, (2^31 <= L)%Z ->
  tree_ok usegs u_init_pc u_phdrs L
    (Prog.prog usegs UREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
  intros L HL en inp Hen Hinp. split.
  - exact (Ubsan.PlainClosed.plain_impl_closed en inp Hen Hinp).
  - exact (prog_model_ok usegs UREAD_STAGE u_init_pc u_phdrs L en inp
             top_pos_ubsan ceil_ubsan floor_ubsan resv_ubsan HL Hen Hinp).
Qed.

Theorem halts_ubsanB : forall cfg, cfg_le cfg ACFG ->
  halts_allowed_T_scfg_budgets cfg ShippedBudgets.lim_source EXITS02
    (mkImage usegs u_init_pc u_phdrs).
Proof.
  intros cfg Hle.
  exact (haltsB_from_tree_gen usegs u_init_pc u_phdrs ShippedBudgets.lim_source EXITS02 (Prog.prog usegs UREAD_STAGE)
           (epost (fun (_ : unit) (_ : machine_state) => True)) cfg Hle
           (ubsan_tree_ok_L ShippedBudgets.lim_source lim31_sourceU) (fun inp en => prog_texits usegs UREAD_STAGE inp en)).
Qed.

Theorem halts_ubsanB_fo :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02
    (mkImage usegs u_init_pc u_phdrs).
Proof. exact (halts_ubsanB forced_only_cfg (forced_only_cfg_least ACFG)). Qed.
