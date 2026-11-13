(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimMremap.v at commit c395a1e0dfa, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim and nothing else. *)
(* Modified by gabelogan195, 2026-11: copied from projects/skcms/iccprofile_info/proofs/lib/Halts/Lim/LimMremap.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim changed to OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts.Lim and nothing else changed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts.Lim Require Import LimBase LimMm LimMmap.
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
  destruct (page_align_is0_b old_size); [intros _; at_auto|].
  intros R1. apply at_get_model. cbv beta zeta.
  change (mremap_source_b (m_vmmaps (setL L m)) old old_n old_nZ) with (mremap_source_b (m_vmmaps m) old old_n old_nZ).
  change (mremap_backing_uniform_b (setL L m) old old_n) with (mremap_backing_uniform_b m old old_n).
  revert R1.
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)); [intros _; at_auto|].
  destruct (old_nZ =? new_nZ)%Z eqn:Eeq; [intros _; at_auto|].
  intros R1. apply at_alt; [at_auto|].
  destruct (new_nZ <? old_nZ)%Z eqn:Elt.
  - (* [comment removed for export] *)
    apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
  - (* [comment removed for export] *)
    assert (Hle : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; apply Z.ltb_ge in Elt; apply Z.eqb_neq in Eeq; lia).
    rewrite Hle in R1. apply negb_false_iff in R1. apply andb_true_iff in R1 as [Rf Rm].
    assert (MOVE : lim_at L i m
              (dst <- choose (fun dst => mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
               modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ))
              (dst <- choose (fun dst => mremap_fresh_b (setL L m) old_nZ new_nZ old old_n dst new_n = true) ;;
               modify (fun _ => mremap_model_next (setL L m) old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ))).
    { apply at_bind.
      - apply at_choose. intros dst Hd. unfold mremap_fresh_b in *. cbv zeta in *.
        apply andb_true_iff in Hd as [Hd Hb]. apply andb_true_iff. split; [exact Hd|].
        apply mremap_final_budget_b_up; assumption.
      - intros dst m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto]. }
    assert (IG : mremap_inplace_grow_b (setL L m) old old_n new_n old_nZ new_nZ = mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ).
    { unfold mremap_inplace_grow_b. cbv zeta.
      change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
      change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
      change (vm_reserved (setvl L (m_vmmaps m))) with (vm_reserved (m_vmmaps m)).
      change (vm_maps (setvl L (m_vmmaps m))) with (vm_maps (m_vmmaps m)).
      rewrite Rf. rewrite (mremap_final_budget_b_up L m old old_n old new_n HL Rf). reflexivity. }
    rewrite IG.
    destruct (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ).
    + apply at_alt; [| exact MOVE].
      apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
    + exact MOVE.
Qed.
