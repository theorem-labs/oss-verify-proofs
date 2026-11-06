(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Vm.
Variable L : Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma within_limit_sl : forall m, vm_backing_within_limit (sl L m) = (vm_backing_used m <=? L).
Proof. reflexivity. Qed.

Lemma within_limit_mono : forall m,
  L <= mlim m -> vm_backing_within_limit (sl L m) = true -> vm_backing_within_limit m = true.
Proof.
  intros m HL H. rewrite within_limit_sl in H. apply Z.leb_le in H.
  unfold vm_backing_within_limit. apply Z.leb_le. unfold mlim in HL. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sigmask_deliver_model_sl : forall new m,
  sigmask_deliver_model new (sl L m) = sl L (sigmask_deliver_model new m).
Proof.
  intros new m. unfold sigmask_deliver_model.
  change (m_sigabrt_pending (sl L m)) with (m_sigabrt_pending m).
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; reflexivity.
Qed.

Lemma sigmask_deliver_model_mlim : forall new m, mlim (sigmask_deliver_model new m) = mlim m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; reflexivity.
Qed.

Lemma fr_rt_sigprocmask : forall how nset oset ss i m,
  FR L i m (rt_sigprocmask_spec how nset oset ss) (rt_sigprocmask_spec how nset oset ss).
Proof.
  intros how nset oset ss i m. unfold rt_sigprocmask_spec.
  fr.
  all: first [apply sigmask_deliver_model_sl | apply sigmask_deliver_model_mlim].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fr_madvise : forall addr len advice i m,
  FR L i m (madvise_spec addr len advice) (madvise_spec addr len advice).
Proof.
  intros addr len advice i m. unfold madvise_spec.
  fr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fr_munmap : forall addr len i m,
  FR L i m (munmap_spec addr len) (munmap_spec addr len).
Proof.
  intros addr len i m. unfold munmap_spec.
  fr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mprotect_budget_ok_mono : forall m addr n,
  L <= mlim m -> mprotect_budget_ok (sl L m) addr n = true -> mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n HL H. unfold mprotect_budget_ok in *.
  change (mprotect_model_next (sl L m) addr n) with (sl L (mprotect_model_next m addr n)) in H.
  apply within_limit_mono; [| exact H]. exact HL.
Qed.

Lemma fr_mprotect : forall addr len prot i m,
  L <= mlim m -> mprotect_budget_refused_b addr len prot (sl L m) = false ->
  FR L i m (mprotect_spec addr len prot) (mprotect_spec addr len prot).
Proof.
  intros addr len prot i m HL HM. unfold mprotect_spec.
  frE.
  - (* [comment removed for export] *)
    unfold mprotect_budget_refused_b in HM. sl_norm_in HM. rew_bools_in HM.
    apply negb_false_iff in HM.
    split; intros _; [apply mprotect_budget_ok_mono; [exact HL | exact HM] | exact HM].
  - fr_inv. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_budget_ok_mono : forall m r,
  L <= mlim m -> brk_budget_ok (sl L m) r = true -> brk_budget_ok m r = true.
Proof.
  intros m r HL H. unfold brk_budget_ok in *. sl_norm_in H.
  change (vm_backing_used (sl L m)) with (vm_backing_used m) in H.
  cbv zeta. apply Z.leb_le in H. apply Z.leb_le. unfold mlim in HL. lia.
Qed.

Lemma vm_forget_range_sl : forall lo hi m,
  vm_forget_range lo hi (sl L m) = sl L (vm_forget_range lo hi m).
Proof. reflexivity. Qed.

Lemma vm_forget_range_mlim : forall lo hi m, mlim (vm_forget_range lo hi m) = mlim m.
Proof. reflexivity. Qed.

Lemma forget_vm_ranges_sl : forall rs m,
  forget_vm_ranges rs (sl L m) = sl L (forget_vm_ranges rs m).
Proof.
  induction rs as [| [a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity |].
  rewrite vm_forget_range_sl. apply IH.
Qed.

Lemma forget_vm_ranges_mlim : forall rs m, mlim (forget_vm_ranges rs m) = mlim m.
Proof.
  induction rs as [| [a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity |].
  rewrite IH. apply vm_forget_range_mlim.
Qed.

Lemma with_brk_next_sl : forall m req r,
  with_brk_next (sl L m) req r = sl L (with_brk_next m req r).
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite <- forget_vm_ranges_sl. reflexivity.
Qed.

Lemma with_brk_next_mlim : forall m req r, mlim (with_brk_next m req r) = mlim m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta. rewrite forget_vm_ranges_mlim. reflexivity.
Qed.

Lemma brk_grow_ok_sl : forall m req r,
  L <= mlim m ->
  (Z.ltb 0 (bv_unsigned (vm_brk (m_vmmaps m))) && Z.ltb (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned r) = true ->
   brk_budget_ok (sl L m) r = true) ->
  brk_grow_ok (sl L m) req r = brk_grow_ok m req r.
Proof.
  intros m req r HL HB. unfold brk_grow_ok. cbv zeta.
  change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)).
  cbn [vml vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
  change (alloc_top (vml L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  destruct (Z.ltb 0 (bv_unsigned (vm_brk (m_vmmaps m))) && Z.ltb (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned r))%bool eqn:E;
    [| reflexivity].
  rewrite (HB eq_refl). rewrite (brk_budget_ok_mono m r HL (HB eq_refl)). reflexivity.
Qed.

Lemma brk_r_ok_sl : forall m req r,
  L <= mlim m -> brk_budget_refused_b (sl L m) req = false ->
  brk_r_ok (sl L m) req r = brk_r_ok m req r.
Proof.
  intros m req r HL HM. unfold brk_r_ok. cbv zeta.
  change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)).
  cbn [vml vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
  change (min_brk (vml L (m_vmmaps m))) with (min_brk (m_vmmaps m)).
  unfold brk_budget_refused_b in HM. sl_norm_in HM.
  change (min_brk (vml L (m_vmmaps m))) with (min_brk (m_vmmaps m)) in HM.
  destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m))))%bool eqn:E1; [reflexivity |].
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))) eqn:E2; [reflexivity |].
  cbn [negb andb] in HM.
  destruct (bv_eqb r req) eqn:E3.
  - (* [comment removed for export] *)
    apply bv_eqb_eq in E3. subst r. cbn [orb andb].
    apply brk_grow_ok_sl; [exact HL |]. intros Hg.
    apply andb_true_iff in Hg as [Hg1 Hg2]. rewrite Hg1, Hg2 in HM. cbn [andb] in HM.
    apply negb_false_iff in HM. exact HM.
  - destruct (bv_eqb r (vm_brk (m_vmmaps m))) eqn:E4; [| reflexivity].
    (* [comment removed for export] *)
    apply bv_eqb_eq in E4. subst r. cbn [orb andb].
    apply brk_grow_ok_sl; [exact HL |]. intros Hg.
    apply andb_true_iff in Hg as [_ Hg2]. apply Z.ltb_lt in Hg2. lia.
Qed.

Lemma fr_brk : forall req i m,
  L <= mlim m -> brk_budget_refused_b (sl L m) req = false ->
  FR L i m (brk_spec req) (brk_spec req).
Proof.
  intros req i m HL HM. unfold brk_spec.
  frE.
  - rewrite (brk_r_ok_sl m req x HL HM). reflexivity.
  - apply with_brk_next_sl.
  - fr_inv. apply with_brk_next_mlim.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_noreserve_backed_ok_mono : forall flags m nZ,
  L <= mlim m ->
  mmap_noreserve_backed_ok flags (sl L m) nZ = true -> mmap_noreserve_backed_ok flags m nZ = true.
Proof.
  intros flags m nZ HL H. unfold mmap_noreserve_backed_ok in *.
  destruct (mmap_noreserve_b flags); [reflexivity |].
  change (vm_backing_used (sl L m)) with (vm_backing_used m) in H.
  change (vm_limit (m_vmmaps (sl L m))) with L in H.
  apply Z.leb_le in H. apply Z.leb_le. unfold mlim in HL. lia.
Qed.

Lemma with_mmap_backing_sl : forall flags a n m,
  with_mmap_backing flags a n (sl L m) = sl L (with_mmap_backing flags a n m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_mlim : forall flags a n m, mlim (with_mmap_backing flags a n m) = mlim m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_replacement_sl : forall flags a n m,
  with_mmap_replacement flags a n (sl L m) = sl L (with_mmap_replacement flags a n m).
Proof. intros. unfold with_mmap_replacement. rewrite <- with_mmap_backing_sl. reflexivity. Qed.

Lemma with_mmap_replacement_mlim : forall flags a n m, mlim (with_mmap_replacement flags a n m) = mlim m.
Proof. intros. unfold with_mmap_replacement. rewrite with_mmap_backing_mlim. reflexivity. Qed.

(* [comment removed for export] *)
Ltac vm_commute :=
  unfold with_mmap_replacement, with_mmap_destroyed, with_mmap_backing;
  repeat match goal with |- context [mmap_noreserve_b ?f] => destruct (mmap_noreserve_b f) end;
  reflexivity.

Lemma mmap_fixed_rw_budget_ok_mono : forall flags m addr n,
  L <= mlim m ->
  mmap_fixed_rw_budget_ok flags (sl L m) addr n = true -> mmap_fixed_rw_budget_ok flags m addr n = true.
Proof.
  intros flags m addr n HL H. unfold mmap_fixed_rw_budget_ok in *.
  apply within_limit_mono.
  - rewrite with_mmap_replacement_mlim. exact HL.
  - rewrite <- with_mmap_replacement_sl. exact H.
Qed.

Lemma mmap_fixed_rw_span_budget_ok_mono : forall flags m addr n,
  L <= mlim m ->
  mmap_fixed_rw_span_budget_ok flags (sl L m) addr n = true -> mmap_fixed_rw_span_budget_ok flags m addr n = true.
Proof.
  intros flags m addr n HL H. unfold mmap_fixed_rw_span_budget_ok in *.
  apply within_limit_mono.
  - rewrite with_mmap_replacement_mlim. exact HL.
  - rewrite <- with_mmap_replacement_sl. exact H.
Qed.

(* [comment removed for export] *)
Ltac mmap_mark HM :=
  unfold mmap_budget_refused_b in HM; sl_norm_in HM;
  repeat match type of HM with
         | context [alloc_top (vml ?L0 ?h)] => change (alloc_top (vml L0 h)) with (alloc_top h) in HM
         end;
  rew_bools_in HM; cbn [negb] in HM; rew_bools_in HM;
  try (apply negb_false_iff in HM).

Lemma fr_mmap : forall addr len prot flags fd off i m,
  L <= mlim m -> mmap_budget_refused_b addr len prot flags fd off (sl L m) = false ->
  FR L i m (mmap_spec addr len prot flags fd off) (mmap_spec addr len prot flags fd off).
Proof.
  intros addr len prot flags fd off i m HL HM. unfold mmap_spec.
  frE.
  all: try (fr_inv; vm_commute).
  all: try (mmap_mark HM;
            first [ split; intros _; [apply mmap_fixed_rw_budget_ok_mono; [exact HL | exact HM] | exact HM]
                  | split; intros _; [apply mmap_fixed_rw_span_budget_ok_mono; [exact HL | exact HM] | exact HM]
                  | split; intros (A1 & A2 & A3 & A4 & _);
                    (split; [exact A1 | split; [exact A2 | split; [exact A3 | split; [exact A4 |]]]]);
                    [apply mmap_noreserve_backed_ok_mono; [exact HL | exact HM] | exact HM]
                  | split; intros (A1 & _); (split; [exact A1 |]);
                    [apply mmap_noreserve_backed_ok_mono; [exact HL | exact HM] | exact HM] ]).
Qed.
End Vm.
