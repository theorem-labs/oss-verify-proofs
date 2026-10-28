From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import TopLevel TopLevelSB.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import TopLevelGen.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog ModelInv ModelOK ImgFacts EquivPU.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Require OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.PlainTree.
Require OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan.PlainClosed.
Open Scope Z_scope.

Definition TPS : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs source_alloc_limit en inp).
Definition TU : tfam := fun inp en => tree_traces (prog usegs UREAD_STAGE inp en) (mo0 usegs target_alloc_limit en inp).

Theorem ubsan_tree_ok :
  tree_ok usegs u_init_pc u_phdrs target_alloc_limit
          (Prog.prog usegs UREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
  intros en inp Hen Hinp. split.
  - exact (Ubsan.PlainClosed.plain_impl_closed en inp Hen Hinp).
  - exact (prog_model_ok_ubsan UREAD_STAGE en inp Hen Hinp).
Qed.

Theorem base_ubsan :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage usegs u_init_pc u_phdrs).
Proof.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply (side_ok_equiv_budgets_L source_alloc_limit _ _ _ _ _ _ TPS TU).
  - exact (side_ok_of_tree_ok _ _ _ _ _ _ (PlainTree.plain_tree_ok_L source_alloc_limit lim_p)).
  - exact (side_ok_of_tree_ok _ _ _ _ _ _ ubsan_tree_ok).
  - intros enS enT inp HvS HvT Hi. unfold TPS, TU. apply equiv_PU; assumption.
Qed.
