(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBArmsBase BBCut BBMCharge BBFit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma map_remove_In : forall l lo x, In x (map_remove l lo) -> In x l.
Proof. intros l lo x H. unfold map_remove in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma region_free_sub : forall l l' lo n, region_free l lo n = true -> (forall x, In x l' -> In x l) ->
  region_free l' lo n = true.
Proof. intros l l' lo n H Hs. apply region_free_intro. intros a sz Hin. exact (region_free_In l lo n a sz H (Hs _ Hin)). Qed.

Lemma rf_app_r : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  induction l1 as [|[b s] r IH]; intros l2 lo n H; [exact H|].
  cbn in H. apply andb_true_iff in H as [_ H]. exact (IH l2 lo n H).
Qed.

Lemma pru_mod : forall n, page_round_up_Z n mod page_size = 0.
Proof. intros n. unfold page_round_up_Z. apply Z.mod_mul. unfold page_size. lia. Qed.

Lemma mr_src_relim : forall L m old old_n z,
  mremap_source_b (m_vmmaps (relim L m)) old old_n z = mremap_source_b (m_vmmaps m) old old_n z.
Proof. reflexivity. Qed.
Lemma mr_unif_relim : forall L m old old_n,
  mremap_backing_uniform_b (relim L m) old old_n = mremap_backing_uniform_b m old old_n.
Proof. reflexivity. Qed.
Lemma mr_next_relim : forall L m old old_n dst new_n,
  mremap_model_next (relim L m) old old_n dst new_n = relim L (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.
Lemma mr_final_eq : forall m old old_n dst new_n,
  mremap_final_budget_b m old old_n dst new_n
  = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? vm_limit (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma mr_final_relim : forall L m old old_n dst new_n,
  mremap_final_budget_b (relim L m) old old_n dst new_n
  = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? L).
Proof. reflexivity. Qed.

Definition fresh_core (m : Model) (new_nZ : Z) (old dst new_n : word) : bool :=
  let h := m_vmmaps m in
  negb (bv_eqb dst old) && (bv_unsigned dst mod page_size =? 0) && (0 <? bv_unsigned dst)
  && (bv_unsigned dst + new_nZ <=? alloc_top h) && region_free (vm_reserved h ++ vm_maps h) dst new_n.
Lemma mr_fresh_eq : forall m oz nz old old_n dst new_n,
  mremap_fresh_b m oz nz old old_n dst new_n = fresh_core m nz old dst new_n && mremap_final_budget_b m old old_n dst new_n.
Proof. reflexivity. Qed.
Lemma mr_fresh_core_relim : forall L m nz old dst new_n,
  fresh_core (relim L m) nz old dst new_n = fresh_core m nz old dst new_n.
Proof. reflexivity. Qed.

Definition inplace_core (m : Model) (old new_n : word) (new_nZ : Z) : bool :=
  let h := m_vmmaps m in
  (bv_unsigned old + new_nZ <=? alloc_top h) && region_free (vm_reserved h ++ map_remove (vm_maps h) old) old new_n.
Lemma mr_inplace_eq : forall m old old_n new_n oz nz,
  mremap_inplace_grow_b m old old_n new_n oz nz = inplace_core m old new_n nz && mremap_final_budget_b m old old_n old new_n.
Proof. reflexivity. Qed.
Lemma mr_inplace_core_relim : forall L m old new_n nz,
  inplace_core (relim L m) old new_n nz = inplace_core m old new_n nz.
Proof. reflexivity. Qed.

Lemma cro_relim : forall L eff r m evs,
  check_ret_only eff r (relim L m) evs = map_cr (relim L) (check_ret_only eff r m evs).
Proof.
  intros L [ret ws zs us cs ci] r m evs. unfold check_ret_only.
  destruct ws, zs, us, cs, ci; try reflexivity. destruct (bv_eqb ret r); reflexivity.
Qed.

Lemma arm_mremap_relim_fit : forall L i eff m, vm_limit (m_vmmaps m) <= L ->
  mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m = false ->
  vm_fit (m_vmmaps m) ->
  ca_check arm_mremap i eff (relim L m) = map_cr (relim L) (ca_check arm_mremap i eff m).
Proof.
  intros L i eff m HL HB Hfit. autorewrite with arm_unfold.
  generalize (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) HB. clear HB.
  intros old os ns fl HB. revert HB.
  unfold check_mremap, mremap_budget_refused_b. cbv zeta.
  set (oZ := page_round_up_Z (bv_unsigned os)). set (nZ := page_round_up_Z (bv_unsigned ns)).
  set (on := Z_to_bv 64 oZ). set (nn := Z_to_bv 64 nZ).
  rewrite !mr_src_relim, !mr_unif_relim.
  destruct (negb (Z.eqb (bv_unsigned fl) MREMAP_MAYMOVE)); [reflexivity|].
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)); [intros; apply cro_relim|].
  destruct (page_align_is0_b ns) eqn:Ens; [intros; apply cro_relim|].
  destruct (page_align_is0_b os); [reflexivity|].
  destruct (negb (mremap_source_b (m_vmmaps m) old on oZ && mremap_backing_uniform_b m old on)); [reflexivity|].
  destruct (oZ =? nZ) eqn:Eeq; [intros; apply cro_relim|].
  apply Z.eqb_neq in Eeq.

  unfold page_align_is0_b in Ens. apply orb_false_iff in Ens as [Ens0 EnsB]. apply Z.leb_gt in EnsB.
  assert (Hns0 : bv_unsigned ns <> 0).
  { intros Hc. unfold w_is0 in Ens0. assert (ns = Z_to_bv 64 0) as -> by (apply bv_eq; rewrite Hc; reflexivity).
    rewrite bv_eqb_refl in Ens0. discriminate. }
  pose proof (mremap_word_range ns) as Hnsr.
  assert (HnZp : page_size <= nZ) by (apply page_round_up_Z_pos; lia).
  assert (Hnn : bv_unsigned nn = nZ) by (apply mremap_u64; unfold page_size in HnZp; lia).
  intros HB.
  destruct eff as [r ws zs us cs ci].
  destruct ws as [|? ?]; [|reflexivity]. destruct ci as [|? ?]; [|reflexivity].
  destruct (errno_ret_in mremap_errnos r); [destruct zs, us, cs; reflexivity|].
  destruct (bv_eqb r old) eqn:Er.
  - destruct (nZ <? oZ) eqn:Esh.
    + cbn [andb]; match goal with |- (if ?b then _ else _) = _ => destruct b; [rewrite mr_next_relim; reflexivity | reflexivity] end.
    + apply Z.ltb_ge in Esh.
      rewrite (proj2 (Z.leb_gt nZ oZ) ltac:(lia)) in HB.
      apply negb_false_iff, andb_true_iff in HB as [Hfi _].
      rewrite !mr_inplace_eq, mr_inplace_core_relim, mr_final_relim, Hfi.
      rewrite mr_final_eq in Hfi. apply Z.leb_le in Hfi.
      rewrite (proj2 (Z.leb_le (vm_backing_used (mremap_model_next m old on old nn)) L) ltac:(lia)).
      destruct (inplace_core m old nn nZ && true); [|reflexivity].
      cbn [andb]; match goal with |- (if ?b then _ else _) = _ => destruct b; [rewrite mr_next_relim; reflexivity | reflexivity] end.
  - destruct (oZ <? nZ) eqn:Eg; [|reflexivity]. apply Z.ltb_lt in Eg.
    rewrite (proj2 (Z.leb_gt nZ oZ) ltac:(lia)) in HB.
    apply negb_false_iff, andb_true_iff in HB as [_ Hmv]. unfold mremap_move_budget_b in Hmv. apply Z.leb_le in Hmv.
    rewrite !mr_fresh_eq, mr_fresh_core_relim, mr_final_relim, mr_final_eq.
    destruct (fresh_core m nZ old r nn) eqn:Ecore; [|reflexivity].
    unfold fresh_core in Ecore. cbv zeta in Ecore.
    apply andb_true_iff in Ecore as [Ecore Hfree]. apply andb_true_iff in Ecore as [Ecore Hceil].
    apply andb_true_iff in Ecore as [Ecore Hpos]. apply andb_true_iff in Ecore as [_ Halign].
    apply Z.leb_le in Hceil. apply Z.eqb_eq in Halign.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hac.
    assert (Hch : vm_backing_used (mremap_model_next m old on r nn) <= mremap_move_charge m old on nn).
    { apply charge_dst_le.
      - exact Halign.
      - rewrite Hnn. apply pru_mod.
      - rewrite Hnn. unfold page_size in HnZp. lia.
      - rewrite Hnn. lia.
      - intros a sz Hin. exact (Hfit a sz (map_remove_In _ _ _ Hin)).
      - apply (region_free_sub (vm_maps (m_vmmaps m))); [exact (rf_app_r _ _ _ _ Hfree) | apply map_remove_In]. }
    rewrite (proj2 (Z.leb_le (vm_backing_used (mremap_model_next m old on r nn)) L) ltac:(lia)),
      (proj2 (Z.leb_le (vm_backing_used (mremap_model_next m old on r nn)) (vm_limit (m_vmmaps m))) ltac:(lia)).
    cbn [andb]; match goal with |- (if ?b then _ else _) = _ => destruct b; [rewrite mr_next_relim; reflexivity | reflexivity] end.
Qed.
