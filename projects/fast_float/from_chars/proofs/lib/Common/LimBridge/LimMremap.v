(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mremap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv LimStar.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Relim.
Variable L : Z. Variable m : Model.
Lemma source_b_relim : forall old old_n z, mremap_source_b (m_vmmaps (m_relim L m)) old old_n z = mremap_source_b (m_vmmaps m) old old_n z.
Proof. reflexivity. Qed.
Lemma uniform_relim : forall old old_n, mremap_backing_uniform_b (m_relim L m) old old_n = mremap_backing_uniform_b m old old_n.
Proof. reflexivity. Qed.
Lemma model_next_relim : forall old old_n dst new_n,
  mremap_model_next (m_relim L m) old old_n dst new_n = m_relim L (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.
Lemma final_budget_relim : forall old old_n dst new_n,
  mremap_final_budget_b (m_relim L m) old old_n dst new_n = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? L)%Z.
Proof. reflexivity. Qed.
Lemma move_charge_relim : forall old old_n new_n, mremap_move_charge (m_relim L m) old old_n new_n = mremap_move_charge m old old_n new_n.
Proof. reflexivity. Qed.
Lemma move_budget_relim : forall old old_n new_n, mremap_move_budget_b (m_relim L m) old old_n new_n = (mremap_move_charge m old old_n new_n <=? L)%Z.
Proof. reflexivity. Qed.
End Relim.

Lemma page_round_up_Z_mod : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intros z. unfold page_round_up_Z. apply Z.mod_mul. unfold page_size. lia. Qed.
Lemma new_n_facts : forall w : word, page_align_is0_b w = false ->
  (0 < page_round_up_Z (bv_unsigned w) < two_pow_64 /\ bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned w))) = page_round_up_Z (bv_unsigned w))%Z.
Proof.
  intros w H. pose proof (page_align_is0_false_pos w H) as Hp. unfold page_align_is0_b in H. apply orb_false_iff in H. destruct H as [_ H].
  apply Z.leb_gt in H. split; [lia |]. apply mremap_u64. lia.
Qed.
Lemma region_free_app_r' : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  induction l1 as [| [b s] r IH]; intros l2 lo n H; [exact H |].
  cbn [app region_free] in H. apply andb_true_iff in H. destruct H as [_ H]. exact (IH l2 lo n H).
Qed.

(* [comment removed for export] *)
Lemma fresh_relim : forall L m (old old_size new_size dst : word),
  Inv m -> page_align_is0_b new_size = false ->
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let old_n := Z_to_bv 64 old_nZ in let new_n := Z_to_bv 64 new_nZ in
  mremap_move_budget_b (m_relim L m) old old_n new_n = true ->
  mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true ->
  mremap_fresh_b (m_relim L m) old_nZ new_nZ old old_n dst new_n = true.
Proof.
  intros L m old old_size new_size dst HI Hns old_nZ new_nZ old_n new_n Hmb H.
  destruct (new_n_facts new_size Hns) as [Hr Hu]. fold new_nZ in Hr, Hu. fold new_n in Hu.
  unfold mremap_fresh_b in *. cbv zeta in *.
  apply andb_true_iff in H. destruct H as [H Hfb].
  apply andb_true_iff. split; [exact H |].
  rewrite final_budget_relim. rewrite move_budget_relim in Hmb. apply Z.leb_le in Hmb. apply Z.leb_le.
  apply andb_true_iff in H. destruct H as [H Hrf]. apply andb_true_iff in H. destruct H as [H Htop].
  apply andb_true_iff in H. destruct H as [H _]. apply andb_true_iff in H. destruct H as [_ Hal].
  apply Z.eqb_eq in Hal. apply Z.leb_le in Htop. pose proof (alloc_top_lt (m_vmmaps m)) as Hat.
  eapply Z.le_trans; [| exact Hmb].
  apply mremap_star; [exact HI | exact Hal | rewrite Hu; apply page_round_up_Z_mod | rewrite Hu; lia | rewrite Hu; lia |].
  exact (region_free_app_r' _ _ _ _ Hrf).
Qed.

Lemma bind_get_model_iff' {B} (k : Model -> Sys B) : forall i m o, bind get_model k i m o <-> k m i m o.
Proof. intros i m o. apply bind_get_model. Qed.

Lemma mremap_lpres : forall (old old_size new_size flags : word), lpres (mremap_spec old old_size new_size flags).
Proof. intros. lpres_brute. Qed.

Lemma mremap_frame : forall L (old old_size new_size flags : word) i m o,
  mremap_spec old old_size new_size flags i m o ->
  Inv m ->
  mremap_budget_refused_b old old_size new_size flags m = false ->
  mremap_budget_refused_b old old_size new_size flags (m_relim L m) = false ->
  mremap_spec old old_size new_size flags i (m_relim L m) (o_relim L o).
Proof.
  intros L old old_size new_size flags i m o H HI HG0 HG1.
  unfold mremap_spec in *. unfold mremap_budget_refused_b in HG0, HG1.
  assert (Lun : lrel L (@unmodeled SyscallEffect) unmodeled) by apply lrel_unmodeled.
  assert (Lerr : forall e, lrel L (err_ret e) (err_ret e)) by (intros e; lrel_go).
  assert (Lret : forall r, lrel L (ret_only r) (ret_only r)) by (intros r; lrel_go).
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z) eqn:E1; [exact (Lun i m o H) |].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z) eqn:E2; [exact (Lerr _ i m o H) |].
  destruct (page_align_is0_b new_size) eqn:E3; [exact (Lerr _ i m o H) |].
  destruct (page_align_is0_b old_size) eqn:E4; [exact (Lun i m o H) |].
  apply bind_get_model_iff' in H. apply bind_get_model_iff'. cbv zeta in *.
  rewrite source_b_relim, uniform_relim in *.
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)) in *. set (new_nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  set (old_n := Z_to_bv 64 old_nZ) in *. set (new_n := Z_to_bv 64 new_nZ) in *.
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)) eqn:E5; [exact (Lun i m o H) |].
  destruct (old_nZ =? new_nZ)%Z eqn:E6; [exact (Lret _ i m o H) |].
  assert (Lmod : forall (dst : word) (eff : SyscallEffect), lrel L (modify (fun _ => mremap_model_next m old old_n dst new_n) ;; pure eff)
                                   (modify (fun _ => mremap_model_next (m_relim L m) old old_n dst new_n) ;; pure eff)).
  { intros dst eff. apply lrel_bind; [apply lrel_modify; intros m1; apply model_next_relim | intros []; apply lrel_pure]. }
  destruct H as [H | H]; [left; revert H; generalize i m o; change (lrel L (e <- errno_from mremap_errnos ;; err_ret e) (e <- errno_from mremap_errnos ;; err_ret e)); lrel_go | right].
  destruct (new_nZ <? old_nZ)%Z eqn:E7; [exact (Lmod _ _ i m o H) |].
  (* [comment removed for export] *)
  assert (E8 : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; apply Z.ltb_ge in E7; apply Z.eqb_neq in E6; lia).
  rewrite E8 in HG0, HG1. apply negb_false_iff in HG0, HG1.
  apply andb_true_iff in HG0, HG1. destruct HG0 as [HGi0 HGm0]. destruct HG1 as [HGi1 HGm1].
  assert (Lmove : lrel L (dst <- choose (fun dst => mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
                          modify (fun _ => mremap_model_next m old old_n dst new_n) ;; pure (mremap_move_effect old old_n dst old_nZ new_nZ))
                         (dst <- choose (fun dst => mremap_fresh_b (m_relim L m) old_nZ new_nZ old old_n dst new_n = true) ;;
                          modify (fun _ => mremap_model_next (m_relim L m) old old_n dst new_n) ;; pure (mremap_move_effect old old_n dst old_nZ new_nZ))).
  { apply lrel_bind; [apply lrel_choose_imp; intros dst Hd; exact (fresh_relim L m old old_size new_size dst HI E3 HGm1 Hd) | intros dst; apply Lmod]. }
  assert (Egrow : mremap_inplace_grow_b (m_relim L m) old old_n new_n old_nZ new_nZ = mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ).
  { unfold mremap_inplace_grow_b. cbv zeta. rewrite HGi0, HGi1. reflexivity. }
  rewrite Egrow.
  destruct (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ) eqn:E9; [| exact (Lmove i m o H)].
  destruct H as [H | H]; [left; exact (Lmod _ _ i m o H) | right; exact (Lmove i m o H)].
Qed.
