(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel BothMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import HaltsTrace HaltsTraceB HaltsShape.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import ShapeAlg SpinAlg MainExport MainFactsBoth MainEntryBoth MainEntryBothH.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prog AsanInv ProgExits.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
Import ListNotations.
Open Scope Z_scope.
Section H.
Variable rsA : Z.
Hypothesis both_impl : both_impl_stmt rsA.
#[using="Type"] Lemma lim34_source : LIMIT34 <= source_alloc_limit.
Proof. rewrite LIMIT34_eq. lia. Qed.
#[using="Type"] Lemma lim31_source : 2^31 <= source_alloc_limit.
Proof. rewrite <- LIMIT34_eq. vm_compute. discriminate. Qed.
#[using="rsA both_impl"] Theorem halts_bothB_of_impl : forall cfg, cfg_le cfg ACFG -> halts_allowed_T_scfg_budgets cfg ShippedBudgets.lim_source EXITS02 (mkImage bsegs b_init_pc b_phdrs).
Proof.
intros cfg Hle. apply (haltsB_of_must_exit_may_fail cfg _ _ _ Hle). unfold ShippedBudgets.lim_source. intros en inp Hv Hi. pose proof (valid_input_either_of_valid_input _ Hi) as Hei.
set (T := fun tr : list event => tr = [] \/ TB source_alloc_limit inp en tr).
assert (HR : ShapeAlg.realizes bsegs
(init_config bsegs b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T).
{ apply (both_boot_R_valid en inp T Hv Hi); [left; reflexivity|].
intros ms mo HM.
assert (HS : SpinAlg.srealizes bsegs (mkCfg ms mo) (TB source_alloc_limit inp en)).
{ apply (both_main_srealizes rsA both_impl source_alloc_limit lim31_source en inp Hv Hei ms mo).
exact (bmain_atL_open source_alloc_limit en inp ms mo lim34_source HM). }
apply (SpinAlg.srz_conseq bsegs _ _ _ HS). intros tr. subst T. cbv beta. split; [intros H; right; exact H|].
intros [->|H]; [| exact H]. exact (SpinAlg.srealizes_star_only bsegs _ _ HS [] _ (star_cfg_refl _ _ _)). }
destruct en as [sp brk0 mbase rdraw]. cbn [en_sp en_brk en_mmap_base en_draw] in HR. unfold must_exit_in_scfg.
apply (realizes_must_exit_cfg bsegs EXITS02 _ T HR).
- reflexivity.
- intros tr sig fs [E|H]; [destruct tr; discriminate E|]. exact (tree_traces_no_killev _ _ tr sig fs H).
- intros tr code fs [E|H]; [destruct tr; discriminate E|]. exact (tree_traces_exit_S EXITS02 _ _ tr code fs (prog_texits _ _ _ _) H).
Qed.
End H.
