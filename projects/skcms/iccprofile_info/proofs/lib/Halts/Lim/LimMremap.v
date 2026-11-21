(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimMremap.v at commit theorem-labs/oss-verify-proofs@c5665593c2d8, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim and nothing else. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the mremap budget proofs follow the TASK_SIZE gate and the in-place answer when there is room (mremap_inplace_room_b), with a comment of this file's own on each, the source's comments on the shrink and grow branches of mremap_at_up are left out, and the cited source commit is named by its public id. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim Require Import LimBase LimMm LimMmap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma mremap_model_next_setL : forall L m old old_n dst new_n,
  mremap_model_next (setL L m) old old_n dst new_n = setL L (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.
Lemma mlim_mremap_model_next : forall m old old_n dst new_n, mlim (mremap_model_next m old old_n dst new_n) = mlim m.
Proof. reflexivity. Qed.
Lemma mremap_final_budget_b_setL : forall L m old old_n dst new_n,
  mremap_final_budget_b (setL L m) old old_n dst new_n = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? L)%Z.
Proof. reflexivity. Qed.
Lemma mremap_final_budget_b_up : forall L m old old_n dst new_n,
  (mlim m <= L)%Z -> mremap_final_budget_b m old old_n dst new_n = true -> mremap_final_budget_b (setL L m) old old_n dst new_n = true.
Proof.
  intros L m old old_n dst new_n HL H. rewrite mremap_final_budget_b_setL.
  unfold mremap_final_budget_b, vm_backing_within_limit in H. apply Z.leb_le in H. apply Z.leb_le.
  change (vm_limit (m_vmmaps (mremap_model_next m old old_n dst new_n))) with (mlim m) in H. lia.
Qed.

Lemma mremap_at_up : forall L i m old old_size new_size flags,
  (mlim m <= L)%Z ->
  mremap_budget_refused_b old old_size new_size flags m = false ->
  lim_at L i m (mremap_spec old old_size new_size flags) (mremap_spec old old_size new_size flags).
Proof.
  intros L i m old old_size new_size flags HL R1.
  unfold mremap_spec, mremap_budget_refused_b in *. cbv zeta in *.
  revert R1.
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)). set (new_nZ := page_round_up_Z (bv_unsigned new_size)).
  set (old_n := Z_to_bv 64 old_nZ). set (new_n := Z_to_bv 64 new_nZ).
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z); [intros _; at_auto|].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z); [intros _; at_auto|].
  destruct (page_align_is0_b new_size); [intros _; at_auto|].
  (* LPS 08b1429: a page-aligned new length over TASK_SIZE is EINVAL before any VMA
     is looked up, in the spec and in the mark alike. *)
  destruct (TASK_SIZE <? new_nZ)%Z; [intros _; at_auto|].
  destruct (page_align_is0_b old_size); [intros _; at_auto|].
  intros R1. apply at_get_model. cbv beta zeta.
  change (mremap_source_b (m_vmmaps (setL L m)) old old_n old_nZ) with (mremap_source_b (m_vmmaps m) old old_n old_nZ).
  change (mremap_backing_uniform_b (setL L m) old old_n) with (mremap_backing_uniform_b m old old_n).
  revert R1.
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)); [intros _; at_auto|].
  destruct (old_nZ =? new_nZ)%Z eqn:Eeq; [intros _; at_auto|].
  intros R1. apply at_alt; [at_auto|].
  destruct (new_nZ <? old_nZ)%Z eqn:Elt.
  -
    apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
  -
    assert (Hle : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; apply Z.ltb_ge in Elt; apply Z.eqb_neq in Eeq; lia).
    rewrite Hle in R1.
    (* LPS 08b1429: with room the only non-errno answer is the in-place one, gated by
       [mremap_final_budget_b]; without room it is the move, whose destination predicate
       is [mremap_dst_ok]. [setL] changes only [vm_limit], which neither the room test
       nor [linux_place] reads. *)
    assert (IR : mremap_inplace_room_b (setL L m) old old_n new_n old_nZ new_nZ
                 = mremap_inplace_room_b m old old_n new_n old_nZ new_nZ).
    { unfold mremap_inplace_room_b. cbv zeta.
      change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
      change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
      change (vm_reserved (setvl L (m_vmmaps m))) with (vm_reserved (m_vmmaps m)).
      change (vm_maps (setvl L (m_vmmaps m))) with (vm_maps (m_vmmaps m)).
      reflexivity. }
    rewrite IR. revert R1.
    destruct (mremap_inplace_room_b m old old_n new_n old_nZ new_nZ) eqn:Eroom; intros R1.
    +
      apply at_bind.
      * apply at_choose. intros [] Hd. apply mremap_final_budget_b_up; assumption.
      * intros [] m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
    +
      apply at_bind.
      * apply at_choose. intros dst Hd. unfold mremap_dst_ok in *. destruct Hd as [Hp Hf].
        split; [exact Hp|]. unfold mremap_fresh_b in *. cbv zeta in *.
        apply andb_true_iff in Hf as [Hf Hb]. apply andb_true_iff. split; [exact Hf|].
        apply mremap_final_budget_b_up; assumption.
      * intros dst m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
Qed.
