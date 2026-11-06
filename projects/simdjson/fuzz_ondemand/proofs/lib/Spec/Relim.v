(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import PropExec MState ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition relim_h (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition relim (L : Z) (mo : Model) : Model := with_vmmaps (relim_h L (m_vmmaps mo)) mo.

Lemma alloc_top_relim : forall L h, alloc_top (relim_h L h) = alloc_top h.
Proof. reflexivity. Qed.

Definition vm_clean (mo : Model) : Prop := m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Lemma minv_clean : forall mo, minv mo -> vm_clean mo.
Proof. intros mo H. split; [apply minv_lazy| apply minv_materialized]; exact H. Qed.

Lemma relim_with_vmmaps : forall L h mo, relim L (with_vmmaps h mo) = with_vmmaps (relim_h L h) (relim L mo).
Proof. intros L h [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_fds : forall L f mo, relim L (with_fds f mo) = with_fds f (relim L mo).
Proof. intros L f [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_tid : forall L t mo, relim L (with_tid t mo) = with_tid t (relim L mo).
Proof. intros L t [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_halted : forall L c mo, relim L (with_halted c mo) = with_halted c (relim L mo).
Proof. intros L c [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_vm_forget_range : forall L lo hi mo, relim L (vm_forget_range lo hi mo) = vm_forget_range lo hi (relim L mo).
Proof. intros L lo hi [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_forget_vm_ranges : forall L rs mo, relim L (forget_vm_ranges rs mo) = forget_vm_ranges rs (relim L mo).
Proof. induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH, relim_vm_forget_range. reflexivity. Qed.
Lemma m_fds_relim : forall L mo, m_fds (relim L mo) = m_fds mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_fs_relim : forall L mo, m_fs (relim L mo) = m_fs mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_tid_relim : forall L mo, m_tid (relim L mo) = m_tid mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vmmaps_relim : forall L mo, m_vmmaps (relim L mo) = relim_h L (m_vmmaps mo). Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vmmaps_with_vmmaps : forall h mo, m_vmmaps (with_vmmaps h mo) = h. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n mo, m_vmmaps (with_mmap_backing flags a n mo) = m_vmmaps mo.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma m_vm_lazy_relim : forall L mo, m_vm_lazy (relim L mo) = m_vm_lazy mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vm_materialized_relim : forall L mo, m_vm_materialized (relim L mo) = m_vm_materialized mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma with_vmmaps_relim : forall L h mo, with_vmmaps h (relim L mo) = with_vmmaps h mo.
Proof. intros L h [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma vm_live_bytes_relim : forall L h, vm_live_bytes (relim_h L h) = vm_live_bytes h. Proof. reflexivity. Qed.
Lemma vm_backed_maps_relim : forall L h, vm_backed_maps (relim_h L h) = vm_backed_maps h. Proof. reflexivity. Qed.
Lemma vm_backing_used_relim : forall L mo, vm_backing_used (relim L mo) = vm_backing_used mo.
Proof. intros L mo. unfold vm_backing_used. rewrite m_vmmaps_relim, vm_backed_maps_relim, m_vm_lazy_relim, m_vm_materialized_relim. reflexivity. Qed.
Lemma vm_backing_used_with_vmmaps_relim : forall L h mo,
  vm_backing_used (with_vmmaps h (relim L mo)) = vm_backing_used (with_vmmaps h mo).
Proof. intros. rewrite with_vmmaps_relim. reflexivity. Qed.
Lemma relim_with_mmap_backing : forall L flags a n mo,
  relim L (with_mmap_backing flags a n mo) = with_mmap_backing flags a n (relim L mo).
Proof.
  intros L flags a n mo. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|reflexivity].
  unfold vm_add_lazy. destruct mo as [fd [mp lz mt] io fs pr lm tm]; reflexivity.
Qed.
Lemma relim_with_mmap_destroyed : forall L a n h mo,
  relim L (with_mmap_destroyed a n h mo) = with_mmap_destroyed a n (relim_h L h) (relim L mo).
Proof. intros. unfold with_mmap_destroyed. rewrite relim_vm_forget_range, relim_with_vmmaps. reflexivity. Qed.
Lemma relim_with_mmap_replacement : forall L flags a n mo,
  relim L (with_mmap_replacement flags a n mo) = with_mmap_replacement flags a n (relim L mo).
Proof. intros. unfold with_mmap_replacement. rewrite relim_with_mmap_backing, relim_vm_forget_range. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app live_bytes];
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64).
  - rewrite !Z.mod_small by lia. lia.
  - pose proof (Z.mod_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) (2^64) ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) (2^64) ltac:(lia) ltac:(lia)). lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all : forall cuts maps, live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma vm_backing_used_clean : forall mo, vm_clean mo ->
  vm_backing_used mo = live_bytes (vm_backed_maps (m_vmmaps mo)).
Proof.
  intros mo [Hl Hm]. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat]. lia.
Qed.

Lemma vm_backing_used_le_live' : forall mo, m_vm_materialized mo = [] ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo Hm. unfold vm_backing_used. rewrite Hm. cbn [length Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r.
  unfold vm_backed_maps, vm_live_bytes.
  etransitivity; [apply live_bytes_maps_subtract_all|]. apply live_bytes_maps_subtract_all.
Qed.

Lemma vm_backing_used_le_live : forall mo, vm_clean mo ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo [_ Hm]. apply vm_backing_used_le_live'. exact Hm. Qed.

Lemma vm_clean_with_vmmaps : forall h mo, vm_clean mo -> vm_clean (with_vmmaps h mo).
Proof. intros h mo [A B]. split; assumption. Qed.

Lemma page_round_up_Z_nonneg : forall x, 0 <= x -> 0 <= page_round_up_Z x.
Proof. intros x Hx. unfold page_round_up_Z. change page_size with 4096. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.

Lemma vm_clean_mprotect_model_next : forall m a n, vm_clean m -> vm_clean (mprotect_model_next m a n).
Proof. intros m a n Hc. unfold mprotect_model_next. apply vm_clean_with_vmmaps. exact Hc. Qed.

Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  | Cho k => forall z, tlive B (k z) mo
  end.

Definition nstep_lim (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ vm_live_bytes (m_vmmaps mo') <= B.

Lemma tpath_lim : forall {R} B (t : itree node R) mo tr r mo',
  tlive B t mo -> (tpath (nstep_lim B) t mo tr r mo' <-> tpath nstep t mo tr r mo').
Proof.
  intros R B t. induction t as [x|n k IH|kc IHc]; intros mo tr r mo' Hl; cbn [tpath]; [tauto| |].
  2:{ cbn [tlive] in Hl. split; intros [z Hp]; exists z; [apply (IHc z)| apply (IHc z) in Hp]; auto. }
  cbn [tlive] in Hl. split.
  - intros (rsp & mo1 & evs & tr' & [Hst Hb] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [|reflexivity].
    apply (IH rsp); [exact (proj2 (Hl _ _ _ Hst))| exact Hp].
  - intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp, mo1, evs, tr'. destruct (Hl _ _ _ Hst) as [Hb Hl'].
    split; [split; assumption|]. split; [|reflexivity]. apply IH; assumption.
Qed.

Lemma texit_lim : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> (texit (nstep_lim B) nexit t mo tr <-> texit nstep nexit t mo tr).
Proof.
  intros R B t. induction t as [x|n k IH|kc IHc]; intros mo tr Hl; cbn [texit]; [tauto| |].
  2:{ cbn [tlive] in Hl. split; intros [z Hp]; exists z; [apply (IHc z)| apply (IHc z) in Hp]; auto. }
  cbn [tlive] in Hl. split.
  - intros [H|(rsp & mo1 & evs & tr' & [Hst Hb] & Hx & ->)]; [left; exact H| right]. exists rsp, mo1, evs, tr'.
    split; [exact Hst|]. split; [|reflexivity]. apply (IH rsp); [exact (proj2 (Hl _ _ _ Hst))| exact Hx].
  - intros [H|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]; [left; exact H| right]. exists rsp, mo1, evs, tr'. destruct (Hl _ _ _ Hst) as [Hb Hl'].
    split; [split; assumption|]. split; [|reflexivity]. apply IH; assumption.
Qed.

Lemma ttrace_lim : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> (ttrace (nstep_lim B) nexit t mo tr <-> ttrace nstep nexit t mo tr).
Proof.
  intros R B t mo tr Hl. rewrite !ttrace_split. rewrite (texit_lim B t mo tr Hl). split.
  - intros [H|(r & mo' & Hp)]; [left; exact H| right]. exists r, mo'. apply (tpath_lim B t mo tr r mo' Hl). exact Hp.
  - intros [H|(r & mo' & Hp)]; [left; exact H| right]. exists r, mo'. apply (tpath_lim B t mo tr r mo' Hl). exact Hp.
Qed.

Lemma tlive_mono : forall {R} B B' (t : itree node R) mo, B <= B' -> tlive B t mo -> tlive B' t mo.
Proof.
  intros R B B' t. induction t as [x|n k IH|kc IHc]; intros mo HB Hl; cbn [tlive] in *; [exact I| |intros z; apply IHc; [exact HB| apply Hl]].
  intros rsp mo' evs Hst. destruct (Hl _ _ _ Hst) as [Hb Hl']. split; [lia|]. apply IH; assumption.
Qed.
