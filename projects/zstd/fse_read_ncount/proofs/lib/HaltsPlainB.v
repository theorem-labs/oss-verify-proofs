(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel TopLevelHaltsB PlainTree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prog ProgExits ImgFacts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
From OSSVerify.zstd.fse_read_ncount.images Require Import Plain.

Lemma lim31_sourceB : (2^31 <= ShippedBudgets.lim_source)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem halts_plainB : forall cfg, cfg_le cfg ACFG ->
  halts_allowed_T_scfg_budgets cfg ShippedBudgets.lim_source EXITS02
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
             Plain.M.phdrs).
Proof.
  intros cfg Hle.
  exact (haltsB_from_tree_gen psegs p_init_pc p_phdrs ShippedBudgets.lim_source EXITS02 (Prog.prog psegs PREAD_STAGE)
           (epost (fun (_ : unit) (_ : machine_state) => True)) cfg Hle
           (plain_tree_ok_L ShippedBudgets.lim_source lim31_sourceB) (fun inp en => prog_texits psegs PREAD_STAGE inp en)).
Qed.

(* [comment removed for export] *)
Theorem halts_plainB_fo :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
             Plain.M.phdrs).
Proof. exact (halts_plainB forced_only_cfg (forced_only_cfg_least ACFG)). Qed.
