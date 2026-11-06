(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad LimFitBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_range : forall w : word, 0 <= bv_unsigned w < two_pow_64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  unfold two_pow_64. exact R.
Qed.

Lemma unsigned_Z_to_bv_le : forall z, 0 <= z -> bv_unsigned (Z_to_bv 64 z) <= z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.mod_le; [exact Hz | lia].
Qed.

Lemma unsigned_Z_to_bv_small : forall z, 0 <= z < two_pow_64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. unfold two_pow_64 in Hz.
  apply Z.mod_small. exact Hz.
Qed.

Lemma entry_fits_top : forall h (a : word) nZ,
  0 <= nZ -> bv_unsigned a + nZ <= alloc_top h -> entry_fits (a, Z_to_bv 64 nZ).
Proof.
  intros h a nZ Hn Ht. unfold entry_fits. cbn [fst snd].
  pose proof (alloc_top_lt h). pose proof (unsigned_Z_to_bv_le nZ Hn). lia.
Qed.

Lemma fits_iv_subtract : forall a sz lo hi,
  entry_fits (a, sz) -> Forall entry_fits (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hf. unfold entry_fits in Hf. cbn [fst snd] in Hf.
  pose proof (word_range a) as Ra. pose proof (word_range sz) as Rs.
  unfold iv_subtract. cbv zeta. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [| constructor].
    apply Z.ltb_lt in E. constructor; [| constructor].
    unfold entry_fits. cbn [fst snd].
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [| constructor].
    apply Z.ltb_lt in E. constructor; [| constructor].
    unfold entry_fits. cbn [fst snd].
    rewrite (unsigned_Z_to_bv_small (Z.max (bv_unsigned a) hi)) by (unfold two_pow_64 in *; lia).
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia). lia.
Qed.

Lemma fits_maps_subtract : forall l lo hi,
  Forall entry_fits l -> Forall entry_fits (maps_subtract l lo hi).
Proof.
  induction l as [| [a sz] r IH]; intros lo hi H; cbn [maps_subtract]; [constructor |].
  inversion H as [| e l' He Hr]; subst. apply Forall_app. split.
  - apply fits_iv_subtract. exact He.
  - apply IH. exact Hr.
Qed.

Lemma fits_map_remove : forall l a, Forall entry_fits l -> Forall entry_fits (map_remove l a).
Proof.
  intros l a H. unfold map_remove. apply Forall_forall. intros e He.
  apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) H e He).
Qed.

Lemma map_has_In : forall l a n, map_has l a n = true -> In (a, n) l.
Proof.
  induction l as [| [b s] r IH]; intros a n H; cbn in H; [discriminate |].
  apply orb_true_iff in H as [H | H].
  - apply andb_true_iff in H as [H1 H2]. apply bv_eqb_eq in H1, H2. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma fits_vm_forget_range : forall lo hi m, fits (vm_forget_range lo hi m) <-> fits m.
Proof. reflexivity. Qed.

Lemma fits_forget_vm_ranges : forall rs m, fits (forget_vm_ranges rs m) <-> fits m.
Proof.
  induction rs as [| [a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity |].
  rewrite IH. apply fits_vm_forget_range.
Qed.

Lemma fits_with_mmap_backing : forall flags a n m, fits (with_mmap_backing flags a n m) <-> fits m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma fits_with_mmap_replacement : forall flags a n m, fits (with_mmap_replacement flags a n m) <-> fits m.
Proof. intros. unfold with_mmap_replacement. rewrite fits_with_mmap_backing. reflexivity. Qed.

Lemma fits_with_vmmaps : forall h m, fits (with_vmmaps h m) <-> Forall entry_fits (vm_maps h).
Proof. reflexivity. Qed.

Lemma fits_vm_resize_backing : forall sl old old_n dst new_n m,
  fits (vm_resize_backing sl old old_n dst new_n m) <-> fits m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fits_sigmask_deliver_model : forall new m, fits (sigmask_deliver_model new m) <-> fits m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; reflexivity.
Qed.

Lemma pr_rt_sigprocmask : forall how nset oset ss i m, PR i m (rt_sigprocmask_spec how nset oset ss).
Proof.
  intros how nset oset ss i m. unfold rt_sigprocmask_spec. pr.
  all: intros HF; apply fits_sigmask_deliver_model; exact HF.
Qed.

Lemma pr_mprotect : forall addr len prot i m, PR i m (mprotect_spec addr len prot).
Proof.
  intros addr len prot i m. unfold mprotect_spec. pr.
  all: fr_inv; exact (fun F => F).
Qed.

Lemma pr_madvise : forall addr len advice i m, PR i m (madvise_spec addr len advice).
Proof. intros addr len advice i m. unfold madvise_spec. pr. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pr_munmap : forall addr len i m, PR i m (munmap_spec addr len).
Proof.
  intros addr len i m. unfold munmap_spec. pr.
  all: intros HF; apply fits_with_vmmaps; cbn [vm_maps]; apply fits_map_remove; exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pr_brk : forall req i m, PR i m (brk_spec req).
Proof.
  intros req i m. unfold brk_spec. pr.
  fr_inv. intros HF.
  unfold with_brk_next. cbv zeta. apply fits_forget_vm_ranges. apply fits_with_vmmaps.
  unfold brk_model_next. cbn [vm_maps]. unfold brk_maps_next.
  destruct (Z.ltb 0 (bv_unsigned (vm_brk (m_vmmaps m))) && Z.ltb (bv_unsigned x0) (bv_unsigned (vm_brk (m_vmmaps m))))%bool.
  - apply fits_maps_subtract. exact HF.
  - apply Forall_app. split; [| exact HF].
    unfold brk_grants. destruct (brk_is_grow req x0 (vm_brk (m_vmmaps m))) eqn:G; [| constructor].
    constructor; [| constructor]. unfold entry_fits. cbn [fst snd].
    unfold brk_is_grow in G. apply andb_true_iff in G as [_ G]. apply Z.ltb_lt in G.
    pose proof (word_range x0). pose proof (word_range (vm_brk (m_vmmaps m))).
    rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus.
    rewrite Z.mod_small by (unfold two_pow_64 in *; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_Z_nonneg : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac fits_entry :=
  match goal with
  | Hx : _ /\ _ /\ (bv_unsigned ?a + ?nZ <= alloc_top ?h) /\ _ |- entry_fits (?a, Z_to_bv 64 ?nZ) =>
      apply (entry_fits_top h); [apply page_round_up_Z_nonneg; apply word_range | exact (proj1 (proj2 (proj2 Hx)))]
  | E : negb (bv_unsigned ?a + ?nZ <=? alloc_top ?h) = false |- entry_fits (?a, Z_to_bv 64 ?nZ) =>
      apply (entry_fits_top h); [apply page_round_up_Z_nonneg; apply word_range
                                | apply Z.leb_le; apply negb_false_iff; exact E]
  end.

Ltac fits_vm HF :=
  repeat first [ apply fits_with_mmap_backing | apply fits_with_mmap_replacement
               | (unfold with_mmap_destroyed; apply fits_vm_forget_range) ];
  apply fits_with_vmmaps;
  unfold mmap_fixed_rw_next, mmap_fixed_destroyed_next, mmap_fixed_rw_span_next, mmap_fixed_noaccess_span_next;
  cbn [vm_maps];
  repeat first [ exact HF | apply fits_maps_subtract | apply Forall_cons; [fits_entry |] ].

Lemma pr_mmap : forall addr len prot flags fd off i m, PR i m (mmap_spec addr len prot flags fd off).
Proof.
  intros addr len prot flags fd off i m. unfold mmap_spec.
  pr.
  all: fr_inv; intros HF;
       repeat match goal with
              | H : @eq word ?x ?y /\ _ |- _ => is_var x; destruct H as [-> _]
              | H : @eq word ?x ?y |- _ => is_var x; subst x
              end;
       fits_vm HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fits_mremap_model_next : forall m old old_n dst new_nZ,
  0 <= new_nZ -> bv_unsigned dst + new_nZ <= alloc_top (m_vmmaps m) ->
  fits m -> fits (mremap_model_next m old old_n dst (Z_to_bv 64 new_nZ)).
Proof.
  intros m old old_n dst new_nZ Hn Ht HF. unfold mremap_model_next.
  apply fits_vm_resize_backing. apply fits_with_vmmaps. unfold mremap_maps_next. cbn [vm_maps].
  apply Forall_cons.
  - exact (entry_fits_top (m_vmmaps m) dst new_nZ Hn Ht).
  - apply fits_map_remove. exact HF.
Qed.

Lemma pr_mremap : forall old old_size new_size flags i m, PR i m (mremap_spec old old_size new_size flags).
Proof.
  intros old old_size new_size flags i m. unfold mremap_spec.
  pr.
  all: fr_inv; apply fits_mremap_model_next;
       [ apply page_round_up_Z_nonneg; apply word_range | ].
  - (* [comment removed for export] *)
    apply negb_false_iff in Heqb3. apply andb_true_iff in Heqb3 as [Hs _].
    unfold mremap_source_b in Hs.
    apply andb_true_iff in Hs as [Hs _]. apply andb_true_iff in Hs as [Hs _].
    apply andb_true_iff in Hs as [Hs _]. apply Z.leb_le in Hs. apply Z.ltb_lt in Heqb5. lia.
  - (* [comment removed for export] *)
    match goal with E : mremap_inplace_grow_b _ _ _ _ _ _ = true |- _ =>
      unfold mremap_inplace_grow_b in E; cbv zeta in E;
      apply andb_true_iff in E as [E _]; apply andb_true_iff in E as [E _]; apply Z.leb_le in E; exact E end.
  - (* [comment removed for export] *)
    match goal with E : mremap_fresh_b _ _ _ _ _ _ _ = true |- _ =>
      unfold mremap_fresh_b in E; cbv zeta in E;
      apply andb_true_iff in E as [E _]; apply andb_true_iff in E as [E _];
      apply andb_true_iff in E as [_ E]; apply Z.leb_le in E; exact E end.
  - (* [comment removed for export] *)
    match goal with E : mremap_fresh_b _ _ _ _ _ _ _ = true |- _ =>
      unfold mremap_fresh_b in E; cbv zeta in E;
      apply andb_true_iff in E as [E _]; apply andb_true_iff in E as [E _];
      apply andb_true_iff in E as [_ E]; apply Z.leb_le in E; exact E end.
Qed.
