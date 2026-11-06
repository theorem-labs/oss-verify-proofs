(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition relim_h (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition relim (L : Z) (mo : Model) : Model := with_vmmaps (relim_h L (m_vmmaps mo)) mo.

Ltac dm mo := destruct mo as [? [? ? ?] ? ? ? ? ?].

Lemma relim_with_vmmaps : forall L h mo, relim L (with_vmmaps h mo) = with_vmmaps (relim_h L h) (relim L mo).
Proof. intros L h mo; dm mo; reflexivity. Qed.
Lemma relim_with_fds : forall L f mo, relim L (with_fds f mo) = with_fds f (relim L mo).
Proof. intros L f mo; dm mo; reflexivity. Qed.
Lemma relim_with_tid : forall L t mo, relim L (with_tid t mo) = with_tid t (relim L mo).
Proof. intros L t mo; dm mo; reflexivity. Qed.
Lemma relim_with_halted : forall L c mo, relim L (with_halted c mo) = with_halted c (relim L mo).
Proof. intros L c mo; dm mo; reflexivity. Qed.
Lemma relim_with_vm_backing : forall L la ma mo, relim L (with_vm_backing la ma mo) = with_vm_backing la ma (relim L mo).
Proof. intros L la ma mo; dm mo; reflexivity. Qed.
Lemma relim_vm_forget_range : forall L lo hi mo, relim L (vm_forget_range lo hi mo) = vm_forget_range lo hi (relim L mo).
Proof. intros L lo hi mo; dm mo; reflexivity. Qed.
Lemma relim_forget_vm_ranges : forall L rs mo, relim L (forget_vm_ranges rs mo) = forget_vm_ranges rs (relim L mo).
Proof. induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH, relim_vm_forget_range. reflexivity. Qed.
Lemma m_fds_relim : forall L mo, m_fds (relim L mo) = m_fds mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_fs_relim : forall L mo, m_fs (relim L mo) = m_fs mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_tid_relim : forall L mo, m_tid (relim L mo) = m_tid mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_halted_relim : forall L mo, m_halted (relim L mo) = m_halted mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_vmmaps_relim : forall L mo, m_vmmaps (relim L mo) = relim_h L (m_vmmaps mo). Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_vm_lazy_relim : forall L mo, m_vm_lazy (relim L mo) = m_vm_lazy mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma m_vm_materialized_relim : forall L mo, m_vm_materialized (relim L mo) = m_vm_materialized mo. Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma with_vmmaps_relim : forall L h mo, with_vmmaps h (relim L mo) = with_vmmaps h mo.
Proof. intros L h mo; dm mo; reflexivity. Qed.
Lemma vm_live_bytes_relim : forall L h, vm_live_bytes (relim_h L h) = vm_live_bytes h. Proof. reflexivity. Qed.
Lemma alloc_top_relim_h : forall L h, alloc_top (relim_h L h) = alloc_top h. Proof. reflexivity. Qed.
Lemma vm_backing_used_relim : forall L mo, vm_backing_used (relim L mo) = vm_backing_used mo.
Proof. intros L mo; dm mo; reflexivity. Qed.
Lemma relim_relim_h_id : forall L h, vm_limit h = L -> relim_h L h = h.
Proof. intros L [? ? ? ? ? ? ?] <-; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn.
  - rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia.
    rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
  - rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia. lia.
  - rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi ->
  live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma backing_le_live : forall mo, m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo Hl Hm. unfold vm_backing_used, vm_backed_maps, vm_live_bytes. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
  rewrite Z.mul_0_l, Z.add_0_r. apply live_bytes_maps_subtract_all.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_grow_ok_relim : forall m req r L,
  brk_grow_ok m req r = true ->
  (0 < bv_unsigned (vm_brk (m_vmmaps m)) -> bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned r ->
   vm_backing_used m + bv_unsigned (r - vm_brk (m_vmmaps m))%bv <= L) ->
  brk_grow_ok (relim L m) req r = true.
Proof.
  intros m req r L Hok HL. unfold brk_grow_ok, brk_budget_ok in *. rewrite m_vmmaps_relim, vm_backing_used_relim, alloc_top_relim_h.
  cbn [vm_brk vm_reserved vm_maps vm_limit relim_h] in *.
  destruct (Z.ltb_spec 0 (bv_unsigned (vm_brk (m_vmmaps m)))); [|reflexivity].
  destruct (Z.ltb_spec (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned r)); [|reflexivity]. cbn [andb] in *.
  apply andb_prop in Hok as [H1 H2]. rewrite H1. cbn [andb]. apply Z.leb_le. apply HL; assumption.
Qed.

Lemma brk_r_ok_relim : forall m req r L,
  brk_r_ok m req r = true ->
  (0 < bv_unsigned (vm_brk (m_vmmaps m)) -> bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned r ->
   vm_backing_used m + bv_unsigned (r - vm_brk (m_vmmaps m))%bv <= L) ->
  brk_r_ok (relim L m) req r = true.
Proof.
  intros m req r L Hok HL. unfold brk_r_ok, min_brk in *. rewrite m_vmmaps_relim. cbn [vm_brk vm_start_brk relim_h] in *.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))))%bool; [exact Hok|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))); [exact Hok|].
  apply andb_prop in Hok as [H1 H2]. rewrite H1. cbn [andb]. apply brk_grow_ok_relim; assumption.
Qed.

Lemma brk_next_live : forall m req r,
  brk_r_ok m req r = true -> 0 < bv_unsigned (vm_brk (m_vmmaps m)) -> bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned r ->
  vm_live_bytes (brk_model_next (m_vmmaps m) req r) = vm_live_bytes (m_vmmaps m) + bv_unsigned (r - vm_brk (m_vmmaps m))%bv.
Proof.
  intros m req r Hok Hb Hlt. unfold brk_model_next, vm_live_bytes. cbn [vm_maps]. unfold brk_maps_next.
  replace (bv_unsigned r <? bv_unsigned (vm_brk (m_vmmaps m))) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
  unfold brk_grants, brk_is_grow. rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.ltb_lt _ _) Hlt).
  assert (Hreq : w_is0 req = false).
  { unfold brk_r_ok in Hok. destruct (w_is0 req) eqn:E; [|reflexivity]. cbn [orb] in Hok. apply bv_eqb_eq in Hok. rewrite Hok in Hlt. lia. }
  rewrite Hreq. cbn. lia.
Qed.

Lemma brk_model_next_relim : forall L h req r,
  brk_model_next (relim_h L h) req r = relim_h L (brk_model_next h req r).
Proof. intros. reflexivity. Qed.

Lemma with_brk_next_relim : forall L m req r, with_brk_next (relim L m) req r = relim L (with_brk_next m req r).
Proof.
  intros L m req r. unfold with_brk_next. rewrite m_vmmaps_relim. cbn [vm_brk relim_h].
  rewrite relim_forget_vm_ranges. f_equal; dm m; reflexivity.
Qed.

Lemma m_vmmaps_with_brk_next : forall m req r, m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps. reflexivity. Qed.

Lemma check_brk_relim : forall req eff m m' evs L,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  check_brk req eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m) /\
  ((vm_live_bytes (m_vmmaps m') <= L \/ vm_limit (m_vmmaps m) <= L) ->
   check_brk req eff (relim L m) = CheckOk (relim L m') evs).
Proof.
  intros req eff m m' evs L Hlz Hmt H. unfold check_brk in *. rewrite m_vmmaps_relim.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok m req r) eqn:Hok; [|discriminate].
  change (vm_brk (relim_h L (m_vmmaps m))) with (vm_brk (m_vmmaps m)).
  destruct (listNN_eqb zs _); [|discriminate]. destruct (listNN_eqb us _); [|discriminate]. cbn [andb] in H.
  injection H as <- <-. split.
  { rewrite m_vmmaps_with_brk_next. reflexivity. }
  intros HL. rewrite (brk_r_ok_relim _ _ _ L Hok).
  - cbn [andb]. rewrite with_brk_next_relim. reflexivity.
  - intros Hb Hlt. pose proof (backing_le_live m Hlz Hmt) as BL. destruct HL as [HL|HL].
    + rewrite m_vmmaps_with_brk_next, (brk_next_live m req r Hok Hb Hlt) in HL. lia.
    + unfold brk_r_ok, brk_grow_ok, brk_budget_ok in Hok.
      destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m))))%bool.
      { apply bv_eqb_eq in Hok. rewrite Hok in Hlt. lia. }
      destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) eqn:E.
      { apply orb_prop in Hok as [Hok|Hok]; apply bv_eqb_eq in Hok; rewrite Hok in Hlt; [apply Z.ltb_lt in E; lia| lia]. }
      rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.ltb_lt _ _) Hlt) in Hok. cbn [andb] in Hok.
      apply andb_prop in Hok as [_ Hok]. apply andb_prop in Hok as [_ Hok]. apply Z.leb_le in Hok. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_Z_nonneg : forall x, 0 <= x -> 0 <= page_round_up_Z x.
Proof. intros x Hx. unfold page_round_up_Z. change page_size with 4096. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.

Lemma check_ret_only_relim : forall eff x m m' es evs L,
  check_ret_only eff x m es = CheckOk m' evs -> m' = m /\ check_ret_only eff x (relim L m) es = CheckOk (relim L m') evs.
Proof.
  intros eff x m m' es evs L H. apply check_ret_only_ok_iff in H as (-> & -> & ->). split; [reflexivity|].
  apply check_ret_only_ok_iff. auto.
Qed.

Lemma with_mmap_backing_plain : forall flags a n m, mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.
Lemma with_mmap_replacement_plain : forall flags a n m, mmap_noreserve_b flags = false ->
  with_mmap_replacement flags a n m = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m.
Proof. intros flags a n m H. unfold with_mmap_replacement. rewrite with_mmap_backing_plain by exact H. reflexivity. Qed.
Lemma mmap_noreserve_backed_ok_plain : forall flags m nZ, mmap_noreserve_b flags = false ->
  mmap_noreserve_backed_ok flags m nZ = (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m)).
Proof. intros flags m nZ H. unfold mmap_noreserve_backed_ok. rewrite H. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros lo hi m; dm m; reflexivity. Qed.
Lemma vm_forget_range_nolazy : forall lo hi m, m_vm_lazy m = [] -> m_vm_materialized m = [] -> vm_forget_range lo hi m = m.
Proof. intros lo hi m; dm m; cbn; intros -> ->; reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m. Proof. intros h m; dm m; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m. Proof. intros h m; dm m; reflexivity. Qed.

Lemma check_munmap_relim : forall addr len eff m m' evs L,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m) /\
  check_munmap addr len eff (relim L m) = CheckOk (relim L m') evs.
Proof.
  intros addr len eff m m' evs L H. unfold check_munmap in *. cbv zeta in H. cbv zeta. rewrite m_vmmaps_relim.
  change (munmap_free_ok (relim_h L (m_vmmaps m))) with (munmap_free_ok (m_vmmaps m)).
  cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp relim_h] in *.
  match type of H with (if ?a then _ else _) = _ => destruct a end.
  { apply (check_ret_only_relim _ _ _ _ _ _ L) in H as [-> H]. split; [reflexivity| exact H]. }
  destruct (TASK_SIZE <? _).
  { apply (check_ret_only_relim _ _ _ _ _ _ L) in H as [-> H]. split; [reflexivity| exact H]. }
  match type of H with (if ?a then _ else _) = _ => destruct a end.
  - destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    match type of H with (if ?a then _ else _) = _ => destruct a; [|discriminate] end.
    injection H as <- <-. split; [unfold with_mmap_destroyed; rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps; reflexivity|].
    unfold with_mmap_destroyed. rewrite relim_vm_forget_range. f_equal; f_equal; dm m; reflexivity.
  - match type of H with (if ?a then _ else _) = _ => destruct a; [|discriminate] end.
    apply (check_ret_only_relim _ _ _ _ _ _ L) in H as [-> H]. split; [reflexivity| exact H].
Qed.

Lemma mprotect_model_next_relim : forall L m a n, mprotect_model_next (relim L m) a n = relim L (mprotect_model_next m a n).
Proof. intros L m a n. unfold mprotect_model_next. rewrite m_vmmaps_relim, with_vmmaps_relim, relim_with_vmmaps, with_vmmaps_relim. dm m; reflexivity. Qed.

Lemma m_vmmaps_mprotect_model_next : forall m a n,
  m_vmmaps (mprotect_model_next m a n) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
    (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. intros. unfold mprotect_model_next. apply m_vmmaps_with_vmmaps. Qed.

Lemma relim_init_model : forall resv brk mbase sp lim inp L, relim L (init_model resv brk mbase sp lim inp) = init_model resv brk mbase sp L inp.
Proof. reflexivity. Qed.
