(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mat_of (m0 m : Model) (k : Z) : Prop :=
  (exists pages, m = with_vm_backing (m_vm_lazy m0) pages m0) /\ vm_backing_used m <= vm_backing_used m0 + 4096 * k.

Lemma with_vm_backing_id : forall m, with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma with_vm_backing_twice : forall L P P' m, with_vm_backing L P' (with_vm_backing L P m) = with_vm_backing L P' m.
Proof. intros L P P' [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma vm_used_with : forall L P m,
  vm_backing_used (with_vm_backing L P m) = live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) L)
                                            + Z.of_nat (length P) * page_size.
Proof. intros L P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma mat_of_refl : forall m0, mat_of m0 m0 0.
Proof.
  intros m0. split; [exists (m_vm_materialized m0); symmetry; apply with_vm_backing_id | lia].
Qed.

Lemma mat_of_mono : forall m0 m k k', mat_of m0 m k -> k <= k' -> mat_of m0 m k'.
Proof. intros m0 m k k' [H1 H2] Hk. split; [exact H1 | lia]. Qed.

Lemma mat_of_halted : forall m0 m k, mat_of m0 m k -> m_halted m = m_halted m0.
Proof. intros m0 m k [(P & ->) _]. destruct m0 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma mat_of_lazy : forall m0 m k, mat_of m0 m k -> m_vm_lazy m = m_vm_lazy m0.
Proof. intros m0 m k [(P & ->) _]. destruct m0 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma mat_of_vmmaps : forall m0 m k, mat_of m0 m k -> m_vmmaps m = m_vmmaps m0.
Proof. intros m0 m k [(P & ->) _]. destruct m0 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma no_lazy_mat : forall m0 m k lo hi, mat_of m0 m k -> no_lazy m0 lo hi -> no_lazy m lo hi.
Proof. intros m0 m k lo hi H Hn p z Hp Hz. rewrite (mat_of_lazy m0 m k H) in Hp. exact (Hn p z Hp Hz). Qed.

Lemma acc_ok_mat : forall m0 m k acc, mat_of m0 m k -> acc_ok m0 acc -> acc_ok m acc.
Proof.
  intros m0 m k acc H Ha. unfold acc_ok in *. eapply Forall_impl; [|exact Ha].
  intros [a n] [H1 H2]. split; [exact H1 | exact (no_lazy_mat m0 m k _ _ H H2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_base_same : forall a i, 0 <= a -> 0 <= i -> a mod 4096 + i < 4096 ->
  page_base_of (a + i) = page_base_of a.
Proof.
  intros a i Ha Hi H. unfold page_base_of, page_size. f_equal.
  assert (E : (a + i) / 4096 = a / 4096).
  { pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.mod_pos_bound a 4096 ltac:(lia)).
    replace (a + i) with ((a mod 4096 + i) + (a / 4096) * 4096) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rewrite E. reflexivity.
Qed.

Lemma page_insert_same : forall p pages, page_mem p pages = true -> page_insert p pages = pages.
Proof. intros p pages H. unfold page_insert. rewrite H. reflexivity. Qed.

Lemma page_mem_hd : forall p pages, page_mem p (p :: pages) = true.
Proof. intros p pages. unfold page_mem. cbn [existsb]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma access_pages_in_page : forall n a, 0 <= a -> a mod 4096 + Z.of_nat n <= 4096 -> (0 < n)%nat ->
  access_pages_acc a n [] = [page_base_of a].
Proof.
  intros n a Ha Hn Hpos.
  assert (G : forall m j, (0 <= j)%Z -> a mod 4096 + j + Z.of_nat m <= 4096 ->
            access_pages_acc (a + j) m [page_base_of a] = [page_base_of a]).
  { induction m as [|m IH]; intros j Hj Hm; [reflexivity|].
    cbn [access_pages_acc]. rewrite (page_base_same a j) by lia.
    rewrite page_insert_same by apply page_mem_hd.
    replace (a + j + 1) with (a + (j + 1)) by lia. apply IH; lia. }
  destruct n as [|n]; [lia|]. cbn [access_pages_acc]. unfold page_insert at 1. cbn [page_mem existsb].
  replace (a + 1) with (a + 1) by reflexivity.
  apply (G n 1); lia.
Qed.

(* [comment removed for export] *)
Lemma with_lazy : forall L P m, m_vm_lazy (with_vm_backing L P m) = L.
Proof. intros L P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma with_matd : forall L P m, m_vm_materialized (with_vm_backing L P m) = P.
Proof. intros L P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma with_maps : forall L P m, m_vmmaps (with_vm_backing L P m) = m_vmmaps m.
Proof. intros L P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma mat_step : forall m0 m k (a : word) (n : nat), mat_of m0 m k -> (0 < n)%nat ->
  bv_unsigned a mod 4096 + Z.of_nat n <= 4096 ->
  vm_backing_used m0 + 4096 * (k + 1) <= vm_limit (m_vmmaps m0) ->
  exists m', materialize_model_accesses m [(a, n)] = Some m' /\ mat_of m0 m' (k + 1).
Proof.
  intros m0 m k a n Hm Hn Hpg Hb. pose proof Hm as [(P & HP) Hu].
  pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
  unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages.
  cbn [accesses_pages]. rewrite (access_pages_in_page n (bv_unsigned a)) by lia.
  cbn [List.filter]. subst m. rewrite !with_lazy, !with_matd, !with_maps.
  destruct (page_in_ranges (page_base_of (bv_unsigned a)) (m_vm_lazy m0) && negb (page_mem (page_base_of (bv_unsigned a)) P))%bool.
  - cbn [length]. rewrite (proj2 (Z.leb_le _ _)) by (unfold page_size; lia).
    eexists. split; [reflexivity|]. split.
    + rewrite with_vm_backing_twice. eexists; reflexivity.
    + rewrite with_vm_backing_twice, vm_used_with. rewrite vm_used_with in Hu. cbn [app length].
      rewrite Nat2Z.inj_succ. unfold page_size in *. lia.
  - eexists. split; [reflexivity|]. rewrite with_vm_backing_twice. split; [eexists; reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma node_instr_mat : forall ms model ms' acc model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  materialize_model_accesses model acc = Some model' ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' acc model' Hh Hsvc Hs Hmat.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model')).
  { unfold mi_account_step. rewrite Hs. cbn [accessed_ranges access_value]. rewrite Hmat. reflexivity. }
  split.
  - intros []. apply sstep_cfg_instr; assumption.
  - intros e st Hss. inversion Hss; subst;
      try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : mi_account_step _ _ _ = _ |- _ =>
        rewrite Hacc in H1; first [ injection H1 as <- <-; exists tt; split; reflexivity | discriminate H1 ] end.
Qed.

Lemma rzc_mat : forall ms model ms' acc model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  materialize_model_accesses model acc = Some model' ->
  realizes_cfg segs cfg (mkCfg ms' model') T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' acc model' T Hh Hsvc Hs Hmat Hc.
  eapply rzc_silent1; [eapply node_instr_mat; eassumption | exact Hc].
Qed.

End Nodes.
