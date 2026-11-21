(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from bzip2/bzip2_compress_target's lib/Common/BudgetBridge/LimVm.v as that unit ported it to LPS 727298f3 (munmap in the allocation family, the rounded brk grants, Linux's mmap placement and the MAP_FIXED overflow branch); module paths moved to this unit. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uaccess SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Signal.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetBridge Require Import Relim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* [comment removed for export] *)
Definition maps_fit (l : list (word * word)) : Prop :=
  forall a sz, In (a, sz) l -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

(* [comment removed for export] *)
Definition INV (m : Model) : Prop :=
  maps_fit (vm_maps (m_vmmaps m)) /\ entries_nonzero (vm_maps (m_vmmaps m)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ofrV (m : Model) {A} (o : outcome A) : Prop :=
  match o with Ok _ m' _ => mlim m' = mlim m /\ (INV m -> INV m') | Unmodeled => True end.

Lemma ofrV_of_ofr : forall m A (o : outcome A), ofr m o -> ofrV m o.
Proof. intros m A [x m' e|] H; [| exact I]. cbn in *. unfold mlim, INV. rewrite H. split; [reflexivity| exact (fun X => X)]. Qed.

(* [comment removed for export] *)
Definition LIV {A} (c : Sys A) : Prop :=
  forall i m o, c i m o -> ofrV m o /\ forall l, c i (relim l m) (relimo l o).

Lemma LIV_of_LI {A} (c : Sys A) : LI c -> LIV c.
Proof. intros H i m o Hc. destruct (H _ _ _ Hc) as [F S]. split; [exact (ofrV_of_ofr _ _ _ F)| exact S]. Qed.

(* [comment removed for export] *)
Definition ARM (no : Z) (c : Sys SyscallEffect) : Prop :=
  forall i m o l, bv_unsigned (in_sysno i) = no -> c i m o ->
    ofrV m o /\
    (INV m -> alloc_budget_refused_b i m = false -> alloc_budget_refused_b i (relim l m) = false ->
     c i (relim l m) (relimo l o)).

Lemma ARM_of_LIV no c : LIV c -> ARM no c.
Proof. intros H i m o l _ Hc. destruct (H _ _ _ Hc) as [F S]. split; [exact F|]. intros _ _ _. exact (S l). Qed.

Lemma ARM_of_LI no c : LI c -> ARM no c.
Proof. intros H. apply ARM_of_LIV, LIV_of_LI, H. Qed.

(* [comment removed for export] *)
Lemma bind_get_vmmaps {A} (k : VmMaps -> Sys A) : forall i m o,
  bind get_vmmaps k i m o <-> k (m_vmmaps m) i m o.
Proof.
  intros i m o. unfold bind, get_vmmaps. destruct o as [y m2 evs|]; split.
  - intros (x & m1 & e1 & e2 & H0 & H2 & ->). injection H0 as -> -> ->. exact H2.
  - intros H2. exists (m_vmmaps m), m, [], evs. repeat split; auto.
  - intros [H0|(x & m1 & e1 & H0 & H2)]; [discriminate H0|]. injection H0 as -> -> ->. exact H2.
  - intros H2. right. exists (m_vmmaps m), m, []. split; [reflexivity| exact H2].
Qed.

Lemma modify_pure_iff {A} (f : Model -> Model) (x : A) : forall i m o,
  (modify f ;; pure x) i m o <-> o = Ok x (f m) [].
Proof.
  intros i m o. unfold bind, modify, pure. destruct o as [y m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & H1 & H2 & ->). injection H1 as _ -> ->. injection H2 as -> -> ->. reflexivity.
  - intros H. injection H as -> -> ->. exists tt, (f m), [], []. repeat split; reflexivity.
  - intros [H|(u & m1 & e1 & _ & H)]; discriminate H.
  - intros H; discriminate H.
Qed.

Lemma modify2_pure_iff {A} (f g : Model -> Model) (x : A) : forall i m o,
  (modify f ;; modify g ;; pure x) i m o <-> o = Ok x (g (f m)) [].
Proof.
  intros i m o. unfold bind at 1. unfold modify at 1. destruct o as [y m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & H1 & H2 & ->). injection H1 as _ -> ->. apply modify_pure_iff in H2.
    injection H2 as -> -> ->. reflexivity.
  - intros H. injection H as -> -> ->. exists tt, (f m), [], []. split; [reflexivity|]. split; [| reflexivity].
    apply modify_pure_iff. reflexivity.
  - intros [H|(u & m1 & e1 & H1 & H)]; [discriminate H|]. apply modify_pure_iff in H. discriminate H.
  - intros H; discriminate H.
Qed.

Lemma choose_modify_pure_iff {X A} (P : X -> Prop) (f : X -> Model -> Model) (r : X -> A) : forall i m o,
  (x <- choose P ;; modify (f x) ;; pure (r x)) i m o <-> exists x, P x /\ o = Ok (r x) (f x m) [].
Proof.
  intros i m o. unfold bind at 1. unfold choose. destruct o as [y m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & (x & HP & H1) & H2 & ->). injection H1 as -> -> ->. apply modify_pure_iff in H2.
    injection H2 as -> -> ->. exists x. split; [exact HP| reflexivity].
  - intros (x & HP & H). injection H as -> -> ->. exists x, m, [], []. split; [exists x; split; [exact HP|reflexivity]|].
    split; [| reflexivity]. apply modify_pure_iff. reflexivity.
  - intros [(x & _ & H)|(u & m1 & e1 & _ & H)]; [discriminate H|]. apply modify_pure_iff in H. discriminate H.
  - intros (x & _ & H); discriminate H.
Qed.

Lemma errno_ret_iff (L : list Z) : forall i m o,
  (e <- errno_from L ;; err_ret e) i m o <-> exists e, In e L /\ o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof.
  intros i m o. unfold bind, errno_from, choose, err_ret, ret_only, pure. destruct o as [y m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & (x & HP & H1) & H2 & ->). injection H1 as -> -> ->. injection H2 as -> -> ->.
    exists x. split; [exact HP| reflexivity].
  - intros (x & HP & H). injection H as -> -> ->. exists x, m, [], []. split; [exists x; split; [exact HP|reflexivity]|].
    split; reflexivity.
  - intros [(x & _ & H)|(u & m1 & e1 & _ & H)]; discriminate H.
  - intros (x & _ & H); discriminate H.
Qed.

Lemma err_ret_iff e : forall i m o, err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros i m o. reflexivity. Qed.

Lemma ret_only_iff r : forall i m o, ret_only r i m o <-> o = Ok (mkEffect r [] []) m [].
Proof. intros i m o. reflexivity. Qed.

Lemma LI_err_ret e : LI (err_ret e).
Proof. unfold err_ret, ret_only. apply LI_pure. Qed.

Lemma LI_ret_only r : LI (ret_only r).
Proof. unfold ret_only. apply LI_pure. Qed.

(* [comment removed for export] *)
Lemma LIV_ok_same {A} (c : Sys A) i m x :
  (forall l, c i (relim l m) (Ok x (relim l m) [])) -> ofrV m (Ok x m []) /\ forall l, c i (relim l m) (relimo l (Ok x m [])).
Proof. intros H. split; [split; [reflexivity| exact (fun X => X)]| exact H]. Qed.

Lemma LIV_unmodeled {A} (c : Sys A) i m :
  (forall l, c i (relim l m) Unmodeled) -> ofrV m (@Unmodeled A) /\ forall l, c i (relim l m) (relimo l (@Unmodeled A)).
Proof. intros H. split; [exact I| exact H]. Qed.

(* [comment removed for export] *)
Lemma LI_set_sigmask_deliver new : LI (set_sigmask_deliver new).
Proof.
  unfold set_sigmask_deliver. apply LI_modify; intros; unfold sigmask_deliver_model.
  - destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; [reflexivity|].
    destruct (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool; reflexivity.
  - change (m_sigabrt_pending (relim l m)) with (m_sigabrt_pending m).
    change (m_sigpipe_pending (relim l m)) with (m_sigpipe_pending m).
    destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; [reflexivity|].
    destruct (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool; reflexivity.
Qed.

Ltac li_step2 :=
  lazymatch goal with
  | |- LI (set_sigmask_deliver _) => apply LI_set_sigmask_deliver
  | |- LI (err_ret _) => apply LI_err_ret
  | |- LI (ret_only _) => apply LI_ret_only
  | _ => li_step
  end.
Ltac li2 := repeat li_step2.

Lemma arm_135 : LI (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof.
  unfold LI; intros i; cbv beta.
  lazymatch goal with |- forall m o, ?c i m o -> _ => enough (HLI : LI c) by exact (HLI i) end.
  li2.
Qed.

Ltac cond_of H :=
  lazymatch type of H with
  | (if ?b then _ else _) _ _ _ => b
  | (if ?b then _ else _) _ _ => b
  | (if ?b then _ else _) _ => b
  end.

(* [comment removed for export] *)
Ltac sync E :=
  lazymatch type of E with ?b0 = _ =>
    match goal with |- context [if ?b' then _ else _] => change b' with b0; rewrite E end
  end.

(* [comment removed for export] *)
Lemma arm_233 : LI (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i).
Proof.
  unfold LI; intros i; cbv beta.
  lazymatch goal with |- forall m o, ?c i m o -> _ => enough (HLI : LI c) by exact (HLI i) end.
  unfold madvise_spec.
  repeat (apply LI_if; [apply LI_err_ret || apply LI_unmodeled || apply LI_ret_only|]).
  apply LI_bind_get_model. intros i' m o H. cbv beta zeta in H |- *.
  let b := cond_of H in destruct b eqn:E.
  - apply modify_pure_iff in H. subst o. split; [reflexivity|]. intros l. sync E.
    apply modify_pure_iff. reflexivity.
  - unfold unmodeled in H. subst o. split; [exact I|]. intros l. sync E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma maps_fit_filter (f : word * word -> bool) l : maps_fit l -> maps_fit (List.filter f l).
Proof. intros H a sz Hin. apply List.filter_In in Hin as [Hin _]. exact (H a sz Hin). Qed.

Lemma maps_fit_map_remove l lo : maps_fit l -> maps_fit (map_remove l lo).
Proof. unfold map_remove. apply maps_fit_filter. Qed.

Lemma arm_215 : LIV (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i).
Proof.
  intros i m o H. unfold munmap_spec in *.
  let b := cond_of H in destruct b.
  { exact (LIV_of_LI _ (LI_err_ret _) _ _ _ H). }
  apply bind_get_vmmaps in H. cbv beta zeta in H.
  let b := cond_of H in destruct b eqn:E2.
  { apply err_ret_iff in H. subst o. apply LIV_ok_same. intros l. apply bind_get_vmmaps. cbv beta zeta.
    apply err_ret_iff. reflexivity. }
  let b := cond_of H in destruct b eqn:E3.
  - (* the revision's exact-mapping arm is an [alt]: the injected errno, then the unmap *)
    unfold alt in H. destruct H as [H|H].
    + apply errno_ret_iff in H. destruct H as (e & He & ->). apply LIV_ok_same. intros l.
      apply bind_get_vmmaps. cbv beta zeta. sync E3. left.
      apply errno_ret_iff. exists e. split; [exact He | reflexivity].
    + unfold set_vmmaps, forget_vm_range in H. apply modify2_pure_iff in H. subst o. split.
      * split; [reflexivity|]. unfold INV.
        cbn [m_vmmaps vm_forget_range with_vm_backing with_vmmaps vmst_maps m_vm vm_maps mmap_fixed_destroyed_next].
        intros [HF HN]. split;
          [ intros b s Hin; destruct (maps_subtract_In _ _ _ b s Hin) as (a & sz & Hin0 & Hiv);
            pose proof (HF a sz Hin0) as Hf; pose proof (iv_subtract_within a sz _ _ b s Hf Hiv); lia
          | apply maps_subtract_nonzero, HN ].
      * intros l. apply bind_get_vmmaps. cbv beta zeta. sync E3. right.
        unfold set_vmmaps, forget_vm_range. apply modify2_pure_iff. reflexivity.
  - let b := cond_of H in destruct b eqn:E4.
    + apply ret_only_iff in H. subst o. apply LIV_ok_same. intros l. apply bind_get_vmmaps. cbv beta zeta.
      sync E3. sync E4. apply ret_only_iff. reflexivity.
    + (* the revision's partial-cut arm ([munmap_cut_ok]): again an injected errno or the cut *)
      let b := cond_of H in destruct b eqn:E5.
      * unfold alt in H. destruct H as [H|H].
        -- apply errno_ret_iff in H. destruct H as (e & He & ->). apply LIV_ok_same. intros l.
           apply bind_get_vmmaps. cbv beta zeta. sync E3. sync E4. sync E5. left.
           apply errno_ret_iff. exists e. split; [exact He | reflexivity].
        -- apply modify_pure_iff in H. subst o. split.
           ++ split; [reflexivity|]. unfold INV, with_mmap_destroyed.
              cbn [m_vmmaps vm_forget_range with_vm_backing with_vmmaps vmst_maps m_vm vm_maps mmap_fixed_destroyed_next].
              intros [HF HN]. split;
                [ intros b s Hin; destruct (maps_subtract_In _ _ _ b s Hin) as (a & sz & Hin0 & Hiv);
                  pose proof (HF a sz Hin0) as Hf; pose proof (iv_subtract_within a sz _ _ b s Hf Hiv); lia
                | apply maps_subtract_nonzero, HN ].
           ++ intros l. apply bind_get_vmmaps. cbv beta zeta. sync E3. sync E4. sync E5. right.
              apply modify_pure_iff. reflexivity.
      * unfold unmodeled in H. subst o. apply LIV_unmodeled. intros l. apply bind_get_vmmaps. cbv beta zeta.
        sync E3. sync E4. sync E5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_range : forall w : word, (0 <= bv_unsigned w < two_pow_64)%Z.
Proof. exact mremap_word_range. Qed.

Lemma u64_of_Z : forall z, (0 <= z < two_pow_64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact mremap_u64. Qed.

(* [comment removed for export] *)
Lemma maps_fit_nil : maps_fit [].
Proof. intros a sz []. Qed.

Lemma maps_fit_cons (a n : word) l :
  (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z -> maps_fit l -> maps_fit ((a, n) :: l).
Proof. intros H Hl b s [E|Hin]; [injection E as <- <-; exact H| exact (Hl b s Hin)]. Qed.

Lemma maps_fit_app l1 l2 : maps_fit l1 -> maps_fit l2 -> maps_fit (l1 ++ l2).
Proof. intros H1 H2 b s Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 b s Hin)| exact (H2 b s Hin)]. Qed.

Lemma maps_fit_maps_subtract l lo hi : maps_fit l -> maps_fit (maps_subtract l lo hi).
Proof.
  intros H b s Hin. destruct (maps_subtract_In l lo hi b s Hin) as (a & sz & Hin0 & Hiv).
  pose proof (H a sz Hin0) as Hf. pose proof (iv_subtract_within a sz lo hi b s Hf Hiv). lia.
Qed.

Lemma maps_fit_top (a : word) nZ h :
  (0 <= nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z ->
  (bv_unsigned a + bv_unsigned (Z_to_bv 64 nZ) <= two_pow_64)%Z.
Proof.
  intros H0 H. pose proof (alloc_top_lt h). pose proof (word_range a). rewrite u64_of_Z; lia.
Qed.

Lemma nonzero_top (a : word) nZ h :
  (0 < nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z -> (0 < bv_unsigned (Z_to_bv 64 nZ))%Z.
Proof.
  intros H0 H. pose proof (alloc_top_lt h). pose proof (word_range a). rewrite u64_of_Z; lia.
Qed.

Lemma page_round_up_Z_pos (len : word) : w_is0 len = false -> (0 < page_round_up_Z (bv_unsigned len))%Z.
Proof.
  intros H. apply w_is0_false_pos in H. unfold page_round_up_Z, page_size.
  pose proof (Z.mul_div_le (bv_unsigned len + 4096 - 1) 4096). pose proof (Z.div_pos (bv_unsigned len + 4096 - 1) 4096).
  assert (4096 * ((bv_unsigned len + 4096 - 1) / 4096) > bv_unsigned len + 4096 - 1 - 4096)%Z.
  { pose proof (Z.mul_succ_div_gt (bv_unsigned len + 4096 - 1) 4096). lia. }
  lia.
Qed.

Lemma entries_nonzero_filter (f : word * word -> bool) l : entries_nonzero l -> entries_nonzero (List.filter f l).
Proof. intros H a sz Hin. apply List.filter_In in Hin as [Hin _]. exact (H a sz Hin). Qed.

Lemma entries_nonzero_app l1 l2 : entries_nonzero l1 -> entries_nonzero l2 -> entries_nonzero (l1 ++ l2).
Proof. intros H1 H2 b s Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 b s Hin)| exact (H2 b s Hin)]. Qed.

(* [comment removed for export] *)
Lemma m_vmmaps_forget_vm_ranges : forall L m, m_vmmaps (forget_vm_ranges L m) = m_vmmaps m.
Proof. induction L as [|[a n] L IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.

Lemma forget_vm_ranges_relim : forall L l m, forget_vm_ranges L (relim l m) = relim l (forget_vm_ranges L m).
Proof. induction L as [|[a n] L IH]; intros l m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite <- IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma abr_214 i m : bv_unsigned (in_sysno i) = 214%Z ->
  alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0).
Proof. intros E. exact (proj1 (alloc_mark_sysnos_dispatched i m) E). Qed.
(* At the revision [alloc_mark_sysnos_dispatched] gained munmap (215) in
   second position, so every later projection moves one place right. *)
Lemma abr_216 i m : bv_unsigned (in_sysno i) = 216%Z ->
  alloc_budget_refused_b i m = mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros E. exact (proj1 (proj2 (proj2 (alloc_mark_sysnos_dispatched i m))) E). Qed.
Lemma abr_222 i m : bv_unsigned (in_sysno i) = 222%Z ->
  alloc_budget_refused_b i m = mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros E. exact (proj1 (proj2 (proj2 (proj2 (alloc_mark_sysnos_dispatched i m)))) E). Qed.
Lemma abr_226 i m : bv_unsigned (in_sysno i) = 226%Z ->
  alloc_budget_refused_b i m = mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros E. exact (proj2 (proj2 (proj2 (proj2 (alloc_mark_sysnos_dispatched i m)))) E). Qed.

(* [comment removed for export] *)
Lemma ARM_leaf_ok i m x l (c : Sys SyscallEffect) (P Q R : Prop) :
  (P -> Q -> R -> c i (relim l m) (Ok x (relim l m) [])) ->
  ofrV m (Ok x m []) /\ (P -> Q -> R -> c i (relim l m) (relimo l (Ok x m []))).
Proof. intros H. split; [split; [reflexivity| exact (fun X => X)]| exact H]. Qed.

Lemma ARM_leaf_unmodeled i m l (c : Sys SyscallEffect) (P Q R : Prop) :
  (P -> Q -> R -> c i (relim l m) Unmodeled) ->
  ofrV m (@Unmodeled SyscallEffect) /\ (P -> Q -> R -> c i (relim l m) (relimo l (@Unmodeled SyscallEffect))).
Proof. intros H. split; [exact I| exact H]. Qed.

(* [comment removed for export] *)
Ltac syncall :=
  repeat (cbv beta zeta;
          lazymatch goal with
          | |- bind get_model _ _ _ _ => apply (proj2 (bind_get_model _ _ _ _))
          | |- context [if _ then _ else _] =>
              match goal with |- context [if ?b' then _ else _] =>
                match goal with E : ?b0 = _ |- _ => change b' with b0; rewrite E end end
          end).

Ltac synch M :=
  repeat match type of M with context [if ?b' then _ else _] =>
           match goal with E : ?b0 = _ |- _ => change b' with b0 in M; rewrite E in M end end.

Ltac leaves H :=
  repeat (cbv beta zeta in H;
          lazymatch type of H with
          | bind get_model _ _ _ _ => apply (proj1 (bind_get_model _ _ _ _)) in H
          | _ => let b := cond_of H in destruct b eqn:?
          end);
  cbv beta zeta in H.

Ltac leaf_li H :=
  first [ apply err_ret_iff in H | apply ret_only_iff in H | unfold unmodeled in H ]; subst;
  first [ apply ARM_leaf_ok | apply ARM_leaf_unmodeled ]; intros _ _ _; syncall;
  first [ apply err_ret_iff | apply ret_only_iff | idtac ]; reflexivity.

(* [comment removed for export] *)
Lemma arm_226 : ARM 226 (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof.
  intros i m o l Hno H. cbv beta in H.
  unfold mprotect_spec in H. leaves H.
  all: rewrite !(abr_226 _ _ Hno); unfold mprotect_budget_refused_b, mprotect_spec;
       repeat match goal with E : ?b = _ |- context [if ?b then _ else _] => rewrite E end; cbv zeta.
  all: try (solve [leaf_li H]).
  - (* [comment removed for export] *)
    destruct H as [H|H].
    + (* [comment removed for export] *)
      apply errno_ret_iff in H as (e & Hin & ->). apply ARM_leaf_ok. intros _ _ _. syncall.
      left. apply errno_ret_iff. exists e. split; [exact Hin| reflexivity].
    + apply choose_modify_pure_iff in H as (u & Hok & ->). split; [split; [reflexivity| exact (fun X => X)]|].
      intros _ _ M2. syncall. synch M2. right. apply choose_modify_pure_iff. exists tt. split; [| reflexivity].
      revert M2. match goal with |- context [negb ?b] => destruct b; [reflexivity| intros X; discriminate X] end.
Qed.

(* [comment removed for export] *)
Lemma brk_spec_iff req : forall i m o,
  brk_spec req i m o <->
  exists r, brk_r_ok m req r = true /\
    o = Ok (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m))) (brk_unmaps r (vm_brk (m_vmmaps m))) [] [])
           (with_brk_next m req r) [].
Proof.
  intros i m o. unfold brk_spec. rewrite (bind_get_model _ i m o). cbv beta zeta. apply choose_modify_pure_iff.
Qed.

(* At the revision [brk_grants] grants the whole pages between the rounded
   old and new breaks ([brk_page_range]) instead of the raw byte range, and
   nothing when they round to the same page. *)
Lemma page_round_up_Z_bounds x : (0 <= x < two_pow_64)%Z -> (0 <= page_round_up_Z x <= two_pow_64)%Z.
Proof.
  intros Hx. change two_pow_64 with 18446744073709551616%Z in *. unfold page_round_up_Z, page_size.
  pose proof (Z.div_pos (x + 4096 - 1) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (x + 4096 - 1) 4096 4503599627370497 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma page_round_up_Z_ge x : (0 <= x)%Z -> (x <= page_round_up_Z x)%Z.
Proof.
  intros Hx. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma maps_fit_brk_page_range lo hi : (0 <= lo)%Z -> (hi <= two_pow_64)%Z -> maps_fit (brk_page_range lo hi).
Proof.
  intros H0 H1. unfold brk_page_range. destruct (lo <? hi)%Z eqn:L; [| apply maps_fit_nil]. apply Z.ltb_lt in L.
  apply maps_fit_cons; [| apply maps_fit_nil].
  assert (Hm : bv_modulus 64 = (2 ^ 64)%Z) by reflexivity.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Hm. unfold two_pow_64 in *.
  rewrite (Z.mod_small lo) by lia.
  pose proof (Z.mod_le (hi - lo) (2 ^ 64)%Z ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma entries_nonzero_brk_page_range lo hi : (0 < lo)%Z -> (hi <= two_pow_64)%Z -> entries_nonzero (brk_page_range lo hi).
Proof.
  intros H0 H1. unfold brk_page_range. destruct (lo <? hi)%Z eqn:L; [| apply entries_nonzero_nil]. apply Z.ltb_lt in L.
  apply entries_nonzero_cons; [| apply entries_nonzero_nil].
  assert (Hm : bv_modulus 64 = (2 ^ 64)%Z) by reflexivity.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hm. unfold two_pow_64 in *.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma maps_fit_brk_grants req r b : maps_fit (brk_grants req r b).
Proof.
  unfold brk_grants. destruct (brk_is_grow req r b) eqn:G; [| apply maps_fit_nil].
  pose proof (page_round_up_Z_bounds _ (word_range r)). pose proof (page_round_up_Z_bounds _ (word_range b)).
  apply maps_fit_brk_page_range; lia.
Qed.

Lemma entries_nonzero_brk_grants req r b : entries_nonzero (brk_grants req r b).
Proof.
  unfold brk_grants. destruct (brk_is_grow req r b) eqn:G; [| apply entries_nonzero_nil].
  unfold brk_is_grow in G. apply andb_prop in G as [G _]. apply andb_prop in G as [_ G]. apply Z.ltb_lt in G.
  pose proof (page_round_up_Z_bounds _ (word_range r)). pose proof (page_round_up_Z_ge (bv_unsigned b) ltac:(lia)).
  apply entries_nonzero_brk_page_range; lia.
Qed.

Lemma brk_r_ok_relim m req r l :
  brk_budget_refused_b (relim l m) req = false ->
  brk_r_ok m req r = true -> brk_r_ok (relim l m) req r = true.
Proof.
  unfold brk_budget_refused_b, brk_r_ok, brk_grow_ok. cbv zeta.
  change (min_brk (m_vmmaps (relim l m))) with (min_brk (m_vmmaps m)).
  change (vm_brk (m_vmmaps (relim l m))) with (vm_brk (m_vmmaps m)).
  change (alloc_top (m_vmmaps (relim l m))) with (alloc_top (m_vmmaps m)).
  change (vm_reserved (m_vmmaps (relim l m))) with (vm_reserved (m_vmmaps m)).
  change (vm_maps (m_vmmaps (relim l m))) with (vm_maps (m_vmmaps m)).
  set (b := vm_brk (m_vmmaps m)).
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))%Z); [intros _ H; exact H|].
  destruct (bv_unsigned req <? bv_unsigned b)%Z; [intros _ H; exact H|].
  cbn [negb andb]. intros M H. apply andb_true_iff in H as [R G]. rewrite R. cbn [andb].
  destruct ((0 <? bv_unsigned b)%Z) eqn:E0; [| reflexivity]. cbn [andb] in *.
  destruct ((bv_unsigned b <? bv_unsigned r)%Z) eqn:E1; [| reflexivity].
  apply andb_true_iff in G as [G _]. rewrite G. cbn [andb].
  assert (r = req) as ->.
  { apply orb_true_iff in R as [R|R]; apply bv_eqb_eq in R; [exact R|].
    exfalso. subst r. rewrite Z.ltb_irrefl in E1. discriminate E1. }
  rewrite E1 in M. destruct (brk_budget_ok (relim l m) req); [reflexivity| discriminate M].
Qed.

Lemma arm_214 : ARM 214 (fun i => brk_spec (in_arg i 0) i).
Proof.
  intros i m o l Hno H. cbv beta in H. apply brk_spec_iff in H as (r & Hok & ->).
  rewrite !(abr_214 _ _ Hno). split.
  - split.
    + unfold mlim, with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges. reflexivity.
    + unfold INV, with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges.
      cbn [m_vmmaps with_vmmaps vmst_maps m_vm]. unfold brk_model_next. cbn [vm_maps]. unfold brk_maps_next.
      match goal with |- context [if ?b then _ else _] => destruct b end; intros [HF HN];
        try (unfold brk_unmap_cut; cbv zeta; match goal with |- context [if ?c then _ else _] => destruct c end);
        split;
        first [ apply maps_fit_maps_subtract, HF | apply maps_subtract_nonzero, HN | exact HF | exact HN
              | apply maps_fit_app; [apply maps_fit_brk_grants| exact HF]
              | apply entries_nonzero_app; [apply entries_nonzero_brk_grants| exact HN] ].
  - intros _ _ M2. apply brk_spec_iff. exists r. split; [exact (brk_r_ok_relim _ _ _ _ M2 Hok)|].
    cbn [relimo]. unfold with_brk_next. cbv zeta. rewrite <- forget_vm_ranges_relim. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_nonneg z : (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof. intros. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.

Lemma m_vmmaps_with_mmap_backing f a n m : m_vmmaps (with_mmap_backing f a n m) = m_vmmaps m.
Proof. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma m_vmmaps_with_mmap_replacement f a n m : m_vmmaps (with_mmap_replacement f a n m) = m_vmmaps m.
Proof. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma with_mmap_backing_relim f a n l m : with_mmap_backing f a n (relim l m) = relim l (with_mmap_backing f a n m).
Proof. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma with_mmap_replacement_relim f a n l m :
  with_mmap_replacement f a n (relim l m) = relim l (with_mmap_replacement f a n m).
Proof. unfold with_mmap_replacement. rewrite <- with_mmap_backing_relim. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_destroyed a n h m : m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.

Lemma true_of_negb_false b : negb b = false -> b = true.
Proof. destruct b; [reflexivity| discriminate]. Qed.
Lemma le_of_negb_leb_false x y : negb (x <=? y)%Z = false -> (x <= y)%Z.
Proof. intros H. apply Z.leb_le. exact (true_of_negb_false _ H). Qed.

(* At the revision [mmap_spec]'s anonymous arms pick the address Linux
   picks ([Mmap.linux_place]) instead of listing the four admissibility
   facts, so the budget bridge reads those facts off the placement. *)
Lemma mmap_place_facts (h : VmMaps) (thp : bool) (hint len a : word) :
  w_is0 len = false ->
  linux_place h thp hint (page_round_up_Z (bv_unsigned len)) (bv_unsigned a) ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + page_round_up_Z (bv_unsigned len) <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true.
Proof.
  intros H0 HL.
  exact (Placement.linux_place_admissible h thp hint _ _
           (page_round_up_Z_pos len H0) (Placement.page_round_up_Z_aligned _) HL).
Qed.

(* [relim] changes only [vm_limit], and [linux_place] reads the ledger,
   the mmap base and the initial stack pointer, so it is unchanged. *)
Lemma linux_place_relim l m thp hint nZ a :
  linux_place (m_vmmaps (relim l m)) thp hint nZ a
  = linux_place (m_vmmaps m) thp hint nZ a.
Proof. reflexivity. Qed.

Lemma kb_thp_relim l m : kb_thp (m_kernel (relim l m)) = kb_thp (m_kernel m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac unrelim :=
  repeat match goal with
  | |- context [vm_reserved (m_vmmaps (relim ?l ?m))] => change (vm_reserved (m_vmmaps (relim l m))) with (vm_reserved (m_vmmaps m))
  | |- context [vm_maps (m_vmmaps (relim ?l ?m))] => change (vm_maps (m_vmmaps (relim l m))) with (vm_maps (m_vmmaps m))
  | |- context [vm_noaccess (m_vmmaps (relim ?l ?m))] => change (vm_noaccess (m_vmmaps (relim l m))) with (vm_noaccess (m_vmmaps m))
  | |- context [alloc_top (m_vmmaps (relim ?l ?m))] => change (alloc_top (m_vmmaps (relim l m))) with (alloc_top (m_vmmaps m))
  | |- context [linux_place (m_vmmaps (relim ?l ?m)) ?t ?hi ?nz ?aa] => rewrite (linux_place_relim l m t hi nz aa)
  | |- context [kb_thp (m_kernel (relim ?l ?m))] => rewrite (kb_thp_relim l m)
  end.

Ltac mm_hyp H :=
  lazymatch type of H with
  | alt _ _ _ _ _ => destruct H as [H|H]; mm_hyp H
  | bind get_model _ _ _ _ => apply (proj1 (bind_get_model _ _ _ _)) in H; cbv beta zeta in H; mm_hyp H
  | _ => idtac
  end.
Ltac mm_go X :=
  lazymatch goal with
  | |- alt _ _ _ _ _ => first [left; mm_go X | right; mm_go X]
  | |- bind get_model _ _ _ _ => apply (proj2 (bind_get_model _ _ _ _)); cbv beta zeta; mm_go X
  | _ => X
  end.
Ltac from_negb M := match goal with |- ?b = true => exact (true_of_negb_false b M) end.
Ltac mm_inv HI :=
  repeat first [ exact HI
               | apply maps_fit_cons
               | apply maps_fit_maps_subtract
               | eapply maps_fit_top; [apply page_round_up_Z_nonneg; apply (proj1 (word_range _))
                                      | first [eassumption | eapply le_of_negb_leb_false; eassumption] ] ].
Ltac mm_nz HN :=
  repeat first [ exact HN
               | apply entries_nonzero_cons
               | apply maps_subtract_nonzero
               | eapply nonzero_top; [apply page_round_up_Z_pos; eassumption
                                     | first [eassumption | eapply le_of_negb_leb_false; eassumption] ] ].
Ltac mm_frame :=
  split; [ unfold mlim; rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement, ?m_vmmaps_with_mmap_destroyed;
           reflexivity
         | let HF := fresh "HF" in let HN := fresh "HN" in intros [HF HN]; unfold INV in *;
           rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement, ?m_vmmaps_with_mmap_destroyed;
           cbn [m_vmmaps with_vmmaps vmst_maps m_vm vm_maps mmap_fixed_rw_next mmap_fixed_rw_span_next
                mmap_fixed_noaccess_span_next mmap_fixed_destroyed_next]; split; [mm_inv HF| mm_nz HN] ].
Ltac mm_model := cbn [relimo]; rewrite <- ?with_mmap_backing_relim, <- ?with_mmap_replacement_relim; reflexivity.
Ltac mm_conds M2 :=
  unrelim; repeat match goal with |- _ /\ _ => split end;
  first [ eassumption | reflexivity | from_negb M2 | tauto ].

Ltac mm_atom H :=
  lazymatch type of H with
  | (bind (errno_from _) ?k) _ _ _ =>
      lazymatch k with
      | context [modify _] =>
          let e := fresh "e" in let Hin := fresh "Hin" in
          apply choose_modify_pure_iff in H as (e & Hin & ->);
          split; [ mm_frame
                 | let HI := fresh "HI" in let M1 := fresh "M1" in let M2 := fresh "M2" in
                   intros HI M1 M2; syncall; synch M2;
                   mm_go ltac:(apply choose_modify_pure_iff; exists e; split; [exact Hin| mm_model]) ]
      | _ =>
          let e := fresh "e" in let Hin := fresh "Hin" in
          apply errno_ret_iff in H as (e & Hin & ->); apply ARM_leaf_ok; intros _ _ _; syncall;
          mm_go ltac:(apply errno_ret_iff; exists e; split; [exact Hin| reflexivity])
      end
  | (bind (choose _) _) _ _ _ =>
      let a := fresh "a" in let HP := fresh "HP" in
      apply choose_modify_pure_iff in H as (a & HP & ->); repeat match type of HP with _ /\ _ => destruct HP as [? HP] end;
      try match goal with Ea : a = _ |- _ => subst a end;
      (* the placement carries the alignment, the positivity, the top bound
         and the free region the old guard listed one by one *)
      try match goal with
          | HL : linux_place ?hh ?tt ?hi (page_round_up_Z (bv_unsigned ?ln)) (bv_unsigned ?aa) |- _ =>
              destruct (mmap_place_facts hh tt hi ln aa ltac:(eassumption) HL) as (? & ? & ? & ?)
          end;
      split; [ mm_frame
             | let HI := fresh "HI" in let M1 := fresh "M1" in let M2 := fresh "M2" in
               intros HI M1 M2; syncall; synch M2;
               mm_go ltac:(apply choose_modify_pure_iff; (first [exists a| eexists]); split; [mm_conds M2| mm_model]) ]
  | (bind (modify _) _) _ _ _ =>
      apply modify_pure_iff in H; subst;
      split; [ mm_frame
             | let HI := fresh "HI" in let M1 := fresh "M1" in let M2 := fresh "M2" in
               intros HI M1 M2; syncall; synch M2; mm_go ltac:(apply modify_pure_iff; mm_model) ]
  | err_ret _ _ _ _ =>
      apply err_ret_iff in H; subst; apply ARM_leaf_ok; intros _ _ _; syncall; mm_go ltac:(apply err_ret_iff; reflexivity)
  (* LPS 75d69e00 (#105): an error-valued MAP_FIXED address comes back as itself ([Mmap.mmap_fixed_overflow]) *)
  | ret_only _ _ _ _ =>
      apply ret_only_iff in H; subst; apply ARM_leaf_ok; intros _ _ _; syncall; mm_go ltac:(apply ret_only_iff; reflexivity)
  end.

Lemma arm_222 : ARM 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof.
  intros i m o l Hno H. cbv beta in H. rewrite !(abr_222 _ _ Hno).
  (* LPS 75d69e00 (#105): the MAP_FIXED overflow branch is [mmap_fixed_overflow], opened here so its
     [if] and its two leaves are split like every other arm; it reads no model state *)
  unfold mmap_spec, mmap_fixed_overflow in H. leaves H. all: cbv beta zeta in H.
  all: unfold mmap_budget_refused_b, mmap_spec, mmap_fixed_overflow;
       repeat match goal with E : ?b = _ |- context [if ?b then _ else _] => rewrite E end; cbv zeta.
  all: try (solve [leaf_li H]).
  (* the revision answers a closed fd on the file-backed path with EBADF
     (a match on the fd table), a held one unmodeled; the budget does not
     touch the fd table *)
  all: try (solve [
    lazymatch type of H with context [fd_lookup (m_fds ?mm) ?k] =>
      let Ef := fresh "Ef" in
      destruct (fd_lookup (m_fds mm) k) as [?|] eqn:Ef; cbv beta iota in H;
      first [apply err_ret_iff in H | unfold unmodeled in H]; subst;
      first [apply ARM_leaf_ok | apply ARM_leaf_unmodeled]; intros _ _ _; syncall;
      repeat match goal with |- context [m_fds (relim ?l0 ?m0)] => change (m_fds (relim l0 m0)) with (m_fds m0) end;
      rewrite Ef; cbv beta iota;
      first [apply err_ret_iff | idtac]; reflexivity
    end]).
  all: mm_hyp H.
  all: mm_atom H.
Qed.
