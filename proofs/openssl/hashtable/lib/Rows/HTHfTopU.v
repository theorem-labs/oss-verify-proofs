From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OssFuzzTheorems.openssl.hashtable.images Require Import Plain.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec SpecGen HTHgTop.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ShapeCfg ConeCfg HULim HTSpec H0FiTail HtHaltsLib HTHfTopA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition hu_full_stmt : Prop :=
  forall lim, (HULim.LIM <= lim)%Z -> HtHaltsLib.full_stmt ConeCfg.CFG U0 lim HTSpec.t_target_ht.

Lemma u_lim_shp : (HULim.LIM <= ShippedBudgets.lim_target)%Z.
Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.

Theorem hu_combine : forall KT,
  HtHaltsLib.full_stmt ConeCfg.CFG P0 ShippedBudgets.lim_source KT ->
  HtHaltsLib.full_stmt ConeCfg.CFG U0 ShippedBudgets.lim_target KT ->
  strong_universal_error_free_T_scfg_budgets ConeCfg.CFG ShippedBudgets.lim_source ShippedBudgets.lim_target P0 U0.
Proof.
  intros KT HP HU. apply ShapeCfg.shape_cfg_universal. intros en_s en_t inp Hs Ht Hv _.
  exists (spec_g KT (in_argv inp) (in_fs inp)). split.
  - exact (HtHaltsLib.full_stmt_init_cfg _ _ _ _ en_s inp HP Hs Hv).
  - exact (HtHaltsLib.full_stmt_init_cfg _ _ _ _ en_t inp HU Ht Hv).
Qed.

Theorem hu_base : H0FiTail.leaf_tail_stmt HTSpec.t_target_ht -> hu_full_stmt ->
  strong_universal_error_free_T_scfg_budgets ConeCfg.CFG ShippedBudgets.lim_source ShippedBudgets.lim_target P0 U0.
Proof.
  intros LP FU.
  exact (hu_combine HTSpec.t_target_ht (HTHfTopA.full_p16 HTSpec.t_target_ht LP) (FU ShippedBudgets.lim_target u_lim_shp)).
Qed.
