(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimMm.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim and nothing else. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require Import LimBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

(* [comment removed for export] *)
Definition lim_at {A} (L : Z) (i : SyscallInput) (m : Model) (c1 c2 : Sys A) : Prop :=
  forall o, c1 i m o -> c2 i (setL L m) (omap L o) /\ opres m o.

Lemma at_blind {A} L i m (c : Sys A) : lim_blind c -> lim_at L i m c c.
Proof. intros H o Ho. destruct (H i m o Ho) as [Ha Hb]. split; [apply Ha | exact Hb]. Qed.
Lemma at_bind {A B} L i m (c1 c2 : Sys A) (k1 k2 : A -> Sys B) :
  lim_at L i m c1 c2 ->
  (forall x m1 evs, c1 i m (Ok x m1 evs) -> lim_at L i m1 (k1 x) (k2 x)) ->
  lim_at L i m (bind c1 k1) (bind c2 k2).
Proof.
  intros Hc Hk [y m2 evs|].
  - intros (x & m1 & evs1 & evs2 & H1 & H2 & ->).
    destruct (Hc _ H1) as [Ha Hb]. destruct (Hk x m1 evs1 H1 _ H2) as [Hc' Hd]. cbn [opres omap] in *.
    split; [| congruence]. exists x, (setL L m1), evs1, evs2. split; [exact Ha|]. split; [exact Hc' | reflexivity].
  - intros [H | (x & m1 & evs1 & H1 & H2)]; (split; [| exact I]); cbn [omap].
    + left. exact (proj1 (Hc _ H)).
    + right. exists x, (setL L m1), evs1. split; [exact (proj1 (Hc _ H1)) | exact (proj1 (Hk x m1 evs1 H1 _ H2))].
Qed.
Lemma at_get_model {A} L i m (k1 k2 : Model -> Sys A) :
  lim_at L i m (k1 m) (k2 (setL L m)) -> lim_at L i m (bind get_model k1) (bind get_model k2).
Proof. intros H o Ho. apply bind_get_model in Ho. destruct (H o Ho) as [Ha Hb]. split; [apply bind_get_model; exact Ha | exact Hb]. Qed.
Lemma bind_get_vmmaps {A} (k : VmMaps -> Sys A) : forall i m o, bind get_vmmaps k i m o <-> k (m_vmmaps m) i m o.
Proof.
  intros i m o. unfold bind, get_vmmaps. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists (m_vmmaps m), m, [], evs. split; [reflexivity|]. split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|]. injection H1 as -> -> ->. exact H2.
  - intros H. right. exists (m_vmmaps m), m, []. split; [reflexivity | exact H].
Qed.
Lemma at_get_vmmaps {A} L i m (k1 k2 : VmMaps -> Sys A) :
  lim_at L i m (k1 (m_vmmaps m)) (k2 (setvl L (m_vmmaps m))) -> lim_at L i m (bind get_vmmaps k1) (bind get_vmmaps k2).
Proof. intros H o Ho. apply bind_get_vmmaps in Ho. destruct (H o Ho) as [Ha Hb]. split; [apply bind_get_vmmaps; exact Ha | exact Hb]. Qed.
Lemma at_modify L i m (f1 f2 : Model -> Model) :
  f2 (setL L m) = setL L (f1 m) -> mlim (f1 m) = mlim m -> lim_at L i m (modify f1) (modify f2).
Proof. intros Hf Hp o Ho. hnf in Ho. subst o. split; [unfold modify; cbn [omap]; rewrite Hf; reflexivity | exact Hp]. Qed.
Lemma at_choose {A} L i m (P1 P2 : A -> Prop) : (forall x, P1 x -> P2 x) -> lim_at L i m (choose P1) (choose P2).
Proof. intros H o (x & Hx & ->). split; [exists x; split; [apply H; exact Hx | reflexivity] | reflexivity]. Qed.
Lemma at_pure {A} L i m (x1 x2 : A) : x1 = x2 -> lim_at L i m (pure x1) (pure x2).
Proof. intros -> o Ho. hnf in Ho. subst o. split; reflexivity. Qed.
Lemma at_alt {A} L i m (c1 c2 d1 d2 : Sys A) : lim_at L i m c1 c2 -> lim_at L i m d1 d2 -> lim_at L i m (alt c1 d1) (alt c2 d2).
Proof. intros H1 H2 o [H|H]; [destruct (H1 o H) as [Ha Hb]; split; [left; exact Ha | exact Hb] | destruct (H2 o H) as [Ha Hb]; split; [right; exact Ha | exact Hb]]. Qed.
Lemma choose_inv {A} (P : A -> Prop) i m x m1 evs : choose P i m (Ok x m1 evs) -> P x /\ m1 = m /\ evs = [].
Proof. intros (y & Hy & E). injection E as -> -> ->. auto. Qed.
Lemma modify_inv (f : Model -> Model) i m x m1 evs : modify f i m (Ok x m1 evs) -> m1 = f m /\ evs = [].
Proof. intros E. hnf in E. injection E as -> -> ->. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vm_backing_used_setL : forall L m, vm_backing_used (setL L m) = vm_backing_used m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_setL : forall L lo hi m, vm_forget_range lo hi (setL L m) = setL L (vm_forget_range lo hi m).
Proof. reflexivity. Qed.
Lemma forget_vm_ranges_setL : forall L rs m, forget_vm_ranges rs (setL L m) = setL L (forget_vm_ranges rs m).
Proof. intros L rs. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite vm_forget_range_setL. apply IH. Qed.
Lemma mlim_vm_forget_range : forall lo hi m, mlim (vm_forget_range lo hi m) = mlim m.
Proof. reflexivity. Qed.
Lemma mlim_forget_vm_ranges : forall rs m, mlim (forget_vm_ranges rs m) = mlim m.
Proof. intros rs. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_brk_next_setL : forall L m req r, with_brk_next (setL L m) req r = setL L (with_brk_next m req r).
Proof. intros. unfold with_brk_next. cbv zeta. rewrite <- forget_vm_ranges_setL. reflexivity. Qed.
Lemma mlim_with_brk_next : forall m req r, mlim (with_brk_next m req r) = mlim m.
Proof. intros. unfold with_brk_next. cbv zeta. rewrite mlim_forget_vm_ranges. reflexivity. Qed.

Lemma brk_budget_ok_setL : forall L m r, brk_budget_ok (setL L m) r = (vm_backing_used m + bv_unsigned (r - vm_brk (m_vmmaps m)) <=? L)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_transfer : forall L m req r,
  brk_budget_refused_b m req = false -> brk_budget_refused_b (setL L m) req = false ->
  brk_r_ok m req r = true -> brk_r_ok (setL L m) req r = true.
Proof.
  intros L m req r R1 R2 H.
  unfold brk_r_ok, brk_budget_refused_b, brk_grow_ok, min_brk in *. cbv zeta in *.
  change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)) in *.
  cbn [setvl vm_start_brk vm_brk vm_reserved vm_maps alloc_top vm_init_sp] in *.
  change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  set (h := m_vmmaps m) in *.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk h))%Z) eqn:E1; [exact H|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk h))%Z eqn:E2; [exact H|].
  cbn [negb andb] in R1, R2.
  apply andb_true_iff in H as [Hr H]. apply andb_true_iff. split; [exact Hr|].
  destruct ((0 <? bv_unsigned (vm_brk h))%Z && (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z) eqn:E3; [| reflexivity].
  apply andb_true_iff in H as [Hreg Hb]. apply andb_true_iff. split; [exact Hreg|].
  (* [comment removed for export] *)
  apply andb_true_iff in E3 as [E3a E3b].
  apply orb_true_iff in Hr as [Hr|Hr]; apply bv_eqb_eq in Hr; subst r.
  - rewrite E3a, E3b in R2. cbn [andb] in R2. apply negb_false_iff in R2. exact R2.
  - apply Z.ltb_lt in E3b. lia.
Qed.

Lemma brk_at : forall L i m req,
  brk_budget_refused_b m req = false -> brk_budget_refused_b (setL L m) req = false ->
  lim_at L i m (brk_spec req) (brk_spec req).
Proof.
  intros L i m req R1 R2. unfold brk_spec.
  apply at_get_model. cbv zeta.
  apply at_bind.
  - apply at_choose. intros r. apply brk_r_ok_transfer; assumption.
  - intros r m1 evs Hc. apply choose_inv in Hc as (Hr & -> & ->).
    apply at_bind.
    + apply at_modify; [apply with_brk_next_setL | apply mlim_with_brk_next].
    + intros [] m2 evs2 Hm. apply at_pure. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blind_err_ret e : lim_blind (err_ret e).
Proof. lim_auto. Qed.
Lemma blind_ret_only r : lim_blind (ret_only r).
Proof. lim_auto. Qed.
Lemma blind_errno_from es : lim_blind (errno_from es).
Proof. lim_auto. Qed.
Lemma blind_errno_alt es : lim_blind (e <- errno_from es ;; err_ret e).
Proof. lim_auto. Qed.

Ltac at_leaf := first [ apply at_blind; first [apply blind_err_ret | apply blind_ret_only | apply blind_errno_alt | apply lim_blind_unmodeled | apply lim_blind_pure ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munmap_at : forall L i m addr len, lim_at L i m (munmap_spec addr len) (munmap_spec addr len).
Proof.
  intros L i m addr len. unfold munmap_spec.
  destruct (negb (bv_unsigned addr mod page_size =? 0)%Z || w_is0 len); [at_leaf|].
  apply at_get_vmmaps. cbv zeta.
  destruct (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z; [at_leaf|].
  cbn [setvl vm_maps vm_reserved vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
  destruct (map_has (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))).
  - apply at_bind.
    + apply at_modify; reflexivity.
    + intros [] m1 evs Hm. apply at_bind.
      * apply at_blind. unfold forget_vm_range. apply lim_blind_modify; reflexivity.
      * intros [] m2 evs2 Hm2. at_leaf.
  - change (munmap_free_ok (setvl L (m_vmmaps m)) addr (page_round_up_Z (bv_unsigned len)))
      with (munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len))).
    destruct (munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len))); at_leaf.
Qed.

Lemma madvise_at : forall L i m addr len adv, lim_at L i m (madvise_spec addr len adv) (madvise_spec addr len adv).
Proof.
  intros L i m addr len adv. unfold madvise_spec.
  destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [at_leaf|].
  destruct (negb (madvise_dontneed_b adv)); [at_leaf|].
  destruct (w_is0 len); [at_leaf|].
  destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z; [at_leaf|].
  apply at_get_model. cbv zeta.
  change (madvise_dontneed_ok (m_vmmaps (setL L m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
    with (madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))).
  destruct (madvise_dontneed_ok (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))); [| at_leaf].
  apply at_bind.
  - apply at_modify; reflexivity.
  - intros [] m1 evs Hm. at_leaf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mprotect_at : forall L i m addr len prot,
  mprotect_budget_refused_b addr len prot m = false -> mprotect_budget_refused_b addr len prot (setL L m) = false ->
  lim_at L i m (mprotect_spec addr len prot) (mprotect_spec addr len prot).
Proof.
  intros L i m addr len prot R1 R2. unfold mprotect_spec, mprotect_budget_refused_b in *.
  destruct (mprotect_grows_conflict_b prot); [at_leaf|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [at_leaf|].
  destruct (w_is0 len); [at_leaf|].
  destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z; [at_leaf|].
  destruct (mprotect_modeled_b prot); [| at_leaf].
  apply at_get_model. cbv zeta in *.
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) in *.
  change (vm_noaccess (m_vmmaps (setL L m))) with (vm_noaccess (m_vmmaps m)) in *.
  change (vm_maps (m_vmmaps (setL L m))) with (vm_maps (m_vmmaps m)) in *.
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
  - apply negb_false_iff in R1, R2.
    apply at_alt; [at_leaf|].
    apply at_bind.
    + apply at_choose. intros _ _. exact R2.
    + intros [] m1 evs Hc. apply choose_inv in Hc as (_ & -> & ->).
      apply at_bind.
      * apply at_modify; reflexivity.
      * intros [] m2 evs2 Hm. at_leaf.
  - destruct (map_contains (vm_maps (m_vmmaps m)) addr n && region_free (vm_noaccess (m_vmmaps m)) addr n); at_leaf.
Qed.
