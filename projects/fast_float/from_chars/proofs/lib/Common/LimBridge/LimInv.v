(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition in_space (e : word * word) : Prop := (0 < bv_unsigned (snd e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= two_pow_64)%Z.
Definition maps_in_space (l : list (word * word)) : Prop := Forall in_space l.
Definition Inv (m : Model) : Prop := maps_in_space (vm_maps (m_vmmaps m)).

Lemma Inv_relim : forall L m, Inv (m_relim L m) <-> Inv m.
Proof. intros L m. unfold Inv. autorewrite with relim. reflexivity. Qed.

Lemma mis_nil : maps_in_space []. Proof. constructor. Qed.
Lemma mis_cons : forall e l, in_space e -> maps_in_space l -> maps_in_space (e :: l).
Proof. intros e l He Hl. constructor; assumption. Qed.
Lemma mis_app : forall l1 l2, maps_in_space l1 -> maps_in_space l2 -> maps_in_space (l1 ++ l2).
Proof. intros l1 l2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma mis_filter : forall f l, maps_in_space l -> maps_in_space (List.filter f l).
Proof.
  intros f l H. induction H as [| e l He Hl IH]; cbn [List.filter]; [constructor |].
  destruct (f e); [constructor; assumption | exact IH].
Qed.
Lemma mis_remove : forall l a, maps_in_space l -> maps_in_space (map_remove l a).
Proof. intros l a H. unfold map_remove. apply mis_filter. exact H. Qed.
Lemma mis_iv_subtract : forall (a sz : word) lo hi, in_space (a, sz) -> maps_in_space (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi [Hp He]. cbn [fst snd] in *. apply Forall_forall. intros [b s] Hin.
  destruct (iv_subtract_within a sz lo hi b s He Hin) as [_ Hb]. unfold in_space. cbn [fst snd]. split; [| lia].
  pose proof (mremap_word_range a) as Ha. pose proof (mremap_word_range sz) as Hsz. unfold two_pow_64 in *.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [| destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin | []]. injection Hin as _ <-.
    rewrite mremap_u64 by (unfold two_pow_64; lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E; [| destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin | []]. injection Hin as _ <-.
    rewrite mremap_u64 by (unfold two_pow_64; lia). lia.
Qed.
Lemma mis_subtract : forall l lo hi, maps_in_space l -> maps_in_space (maps_subtract l lo hi).
Proof.
  intros l lo hi H. induction H as [| [a sz] l He Hl IH]; cbn [maps_subtract]; [constructor |].
  apply mis_app; [apply mis_iv_subtract; exact He | exact IH].
Qed.

(* [comment removed for export] *)
Lemma in_space_top : forall h (a : word) nZ,
  (0 < nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z -> in_space (a, Z_to_bv 64 nZ).
Proof.
  intros h a nZ Hn Hle. unfold in_space. cbn [fst snd].
  pose proof (alloc_top_lt h) as Ht. pose proof (mremap_word_range a) as Ha.
  rewrite mremap_u64 by (unfold two_pow_64 in *; lia). lia.
Qed.
Lemma page_round_up_Z_pos : forall z, (0 < z)%Z -> (0 < page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  assert (1 <= (z + 4096 - 1) / 4096)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Lemma page_align_is0_false_pos : forall w : word, page_align_is0_b w = false -> (0 < page_round_up_Z (bv_unsigned w))%Z.
Proof.
  intros w H. unfold page_align_is0_b in H. apply orb_false_iff in H. destruct H as [H _].
  apply page_round_up_Z_pos. apply w_is0_false_pos. exact H.
Qed.
Lemma in_space_word_end : forall (a r : word), (bv_unsigned a < bv_unsigned r)%Z -> in_space (a, (r - a)%bv).
Proof.
  intros a r Hlt. unfold in_space. cbn [fst snd].
  pose proof (mremap_word_range a). pose proof (mremap_word_range r). unfold two_pow_64 in *.
  rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mvm_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h. Proof. reflexivity. Qed.
Lemma mvm_with_vm_backing : forall l p m, m_vmmaps (with_vm_backing l p m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma mvm_vm_add_lazy : forall a n m, m_vmmaps (vm_add_lazy a n m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma mvm_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma mvm_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. intros rs. induction rs as [| [a n] rs IH]; intros m; [reflexivity |]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.
Lemma mvm_with_mmap_backing : forall flags a n m, m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mvm_with_mmap_replacement : forall flags a n m, m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite mvm_with_mmap_backing. reflexivity. Qed.
Lemma mvm_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.
Lemma mvm_vm_resize_backing : forall sl old old_n dst new_n m, m_vmmaps (vm_resize_backing sl old old_n dst new_n m) = m_vmmaps m.
Proof. reflexivity. Qed.
Create Rewrite HintDb mvm.
#[export] Hint Rewrite mvm_with_vmmaps mvm_with_vm_backing mvm_vm_add_lazy mvm_vm_forget_range mvm_forget_vm_ranges mvm_with_mmap_backing
  mvm_with_mmap_replacement mvm_with_mmap_destroyed mvm_vm_resize_backing : mvm.

(* [comment removed for export] *)
Lemma brk_inv : forall req i m eff m' evs, brk_spec req i m (Ok eff m' evs) -> Inv m -> Inv m'.
Proof.
  intros req i m eff m' evs H HI. unfold brk_spec in H. sys_inv_hyp H.
  unfold Inv, with_brk_next. autorewrite with mvm. unfold brk_model_next. cbn [vm_maps]. unfold brk_maps_next.
  destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m)))%Z && (bv_unsigned x <? bv_unsigned (vm_brk (m_vmmaps m)))%Z).
  - apply mis_subtract. exact HI.
  - apply mis_app; [| exact HI]. unfold brk_grants. destruct (brk_is_grow req x (vm_brk (m_vmmaps m))) eqn:E; [| constructor].
    unfold brk_is_grow in E. apply andb_true_iff in E. destruct E as [_ E]. apply Z.ltb_lt in E.
    apply mis_cons; [apply in_space_word_end; exact E | constructor].
Qed.

(* [comment removed for export] *)
Lemma munmap_inv : forall addr len i m eff m' evs, munmap_spec addr len i m (Ok eff m' evs) -> Inv m -> Inv m'.
Proof.
  intros addr len i m eff m' evs H HI. unfold munmap_spec in H. sys_inv_hyp H.
  all: unfold Inv in *; autorewrite with mvm; cbn [vm_maps]; try assumption.
  all: try (apply mis_remove; assumption).
  all: try (apply mis_subtract; assumption).
Qed.
Lemma mprotect_inv : forall addr len prot i m eff m' evs, mprotect_spec addr len prot i m (Ok eff m' evs) -> Inv m -> Inv m'.
Proof.
  intros addr len prot i m eff m' evs H HI. unfold mprotect_spec in H. sys_inv_hyp H.
  all: unfold Inv, mprotect_model_next in *; autorewrite with mvm; cbn [vm_maps]; try assumption.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_nonneg' : forall z, (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [| lia]. apply Z.div_pos; lia. Qed.
Lemma source_b_top : forall h old old_n old_nZ, mremap_source_b h old old_n old_nZ = true -> (bv_unsigned old + old_nZ <= alloc_top h)%Z.
Proof.
  intros h old old_n old_nZ E. unfold mremap_source_b in E.
  apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E; destruct E as [E _].
  apply Z.leb_le in E. exact E.
Qed.
Lemma inplace_grow_b_top : forall m old old_n new_n old_nZ new_nZ,
  mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true -> (bv_unsigned old + new_nZ <= alloc_top (m_vmmaps m))%Z.
Proof.
  intros m old old_n new_n old_nZ new_nZ E. unfold mremap_inplace_grow_b in E. cbv zeta in E.
  apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E; destruct E as [E _]. apply Z.leb_le in E. exact E.
Qed.
Lemma fresh_b_top : forall m old_nZ new_nZ old old_n dst new_n,
  mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true -> (bv_unsigned dst + new_nZ <= alloc_top (m_vmmaps m))%Z.
Proof.
  intros m old_nZ new_nZ old old_n dst new_n E. unfold mremap_fresh_b in E. cbv zeta in E.
  apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E; destruct E as [_ E].
  apply Z.leb_le in E. exact E.
Qed.
Lemma mremap_inv : forall old old_size new_size flags i m eff m' evs,
  mremap_spec old old_size new_size flags i m (Ok eff m' evs) -> Inv m -> Inv m'.
Proof.
  intros old old_size new_size flags i m eff m' evs H HI. unfold mremap_spec in H. sys_inv_hyp H.
  all: unfold Inv, mremap_model_next, mremap_maps_next in *; autorewrite with mvm; cbn [vm_maps]; try assumption.
  all: apply mis_cons; [| apply mis_remove; assumption].
  all: pose proof (mremap_word_range new_size) as Hns; pose proof (mremap_word_range old_size) as Hos.
  all: apply (in_space_top (m_vmmaps m));
       [match goal with E : page_align_is0_b _ = false |- _ => exact (page_align_is0_false_pos _ E) end |].
  all: try solve [ match goal with E : mremap_fresh_b _ _ _ _ _ _ _ = true |- _ => exact (fresh_b_top _ _ _ _ _ _ _ E) end
                  | match goal with E : mremap_inplace_grow_b _ _ _ _ _ _ = true |- _ => exact (inplace_grow_b_top _ _ _ _ _ _ E) end ].
  all: match goal with E : negb (mremap_source_b _ _ _ _ && _) = false, E2 : (_ <? _)%Z = true |- _ =>
         apply negb_false_iff in E; apply andb_true_iff in E; destruct E as [E _]; apply source_b_top in E; apply Z.ltb_lt in E2; lia end.
Qed.

(* [comment removed for export] *)
Ltac top_fin :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with E : negb _ = false |- _ => apply negb_false_iff in E end;
  repeat match goal with E : (_ <=? _)%Z = true |- _ => apply Z.leb_le in E end;
  subst; first [ assumption | lia ].
Lemma mmap_inv : forall addr len prot flags fd off i m eff m' evs,
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs) -> Inv m -> Inv m'.
Proof.
  intros addr len prot flags fd off i m eff m' evs H HI. unfold mmap_spec in H.
  pose proof (mremap_word_range len) as Hlen.
  sys_inv_hyp H.
  all: unfold Inv, mmap_fixed_rw_next, mmap_fixed_destroyed_next, mmap_fixed_rw_span_next, mmap_fixed_noaccess_span_next in *;
       autorewrite with mvm; cbn [vm_maps]; try assumption.
  all: repeat first [ assumption | apply mis_subtract | apply mis_cons ].
  all: apply (in_space_top (m_vmmaps m));
       [match goal with E : w_is0 _ = false |- _ => exact (page_round_up_Z_pos _ (w_is0_false_pos _ E)) end | top_fin].
Qed.
