(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonlazy_bytes (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m = nonlazy_bytes m + Z.of_nat (List.length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ainv (lz : list (word * word)) (AL : word -> Prop) (N : nat) (m : Model) : Prop := mkAinv {
  ai_lazy  : m_vm_lazy m = lz;
  ai_nodup : List.NoDup (m_vm_materialized m);
  ai_allow : forall p, List.In p (m_vm_materialized m) -> AL p;
  ai_fin   : exists L, List.NoDup L /\ (List.length L <= N)%nat /\ forall p, AL p -> List.In p L;
  ai_room  : nonlazy_bytes m + Z.of_nat N * page_size <= vm_limit (m_vmmaps m)
}.

Lemma ainv_len : forall lz AL N m, ainv lz AL N m -> (List.length (m_vm_materialized m) <= N)%nat.
Proof.
  intros lz AL N m [_ ND AW (L & NDL & LEN & INL) _].
  assert (List.incl (m_vm_materialized m) L) by (intros p Hp; auto).
  pose proof (NoDup_incl_length ND H). lia.
Qed.

Lemma ainv_within_limit : forall lz AL N m, ainv lz AL N m -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros lz AL N m H. pose proof (ainv_len _ _ _ _ H) as LEN. destruct H as [_ _ _ _ ROOM].
  rewrite vm_backing_used_split. unfold page_size in *. nia.
Qed.

Lemma ainv_within_limit_b : forall lz AL N m, ainv lz AL N m -> vm_backing_within_limit m = true.
Proof. intros lz AL N m H. unfold vm_backing_within_limit. apply Z.leb_le. eapply ainv_within_limit; eauto. Qed.

(* [comment removed for export] *)
Lemma ainv_weaken : forall lz (AL AL' : word -> Prop) (N N' : nat) m,
  ainv lz AL N m ->
  (forall p, AL p -> AL' p) ->
  (exists L', List.NoDup L' /\ (List.length L' <= N')%nat /\ forall p, AL' p -> List.In p L') ->
  nonlazy_bytes m + Z.of_nat N' * page_size <= vm_limit (m_vmmaps m) ->
  ainv lz AL' N' m.
Proof.
  intros lz AL AL' N N' m [LZ ND AW _ _] SUB FIN ROOM. constructor; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_ok (lz : list (word * word)) (AL : word -> Prop) (p : word) : Prop :=
  page_in_ranges p lz = false \/ AL p.

Definition accesses_ok (lz : list (word * word)) (AL : word -> Prop) (accs : list (word * nat)) : Prop :=
  forall p, List.In p (accesses_pages accs []) -> page_ok lz AL p.

Lemma page_insert_cases : forall p q pages, List.In p (page_insert q pages) -> p = q \/ List.In p pages.
Proof.
  intros p q pages. unfold page_insert. destruct (page_mem q pages); cbn; intuition.
Qed.

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> List.In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hq & E). apply bv_eqb_eq in E. subst. exact Hq.
  - intros H. exists p. split; [exact H|]. apply bv_eqb_eq. reflexivity.
Qed.

Lemma page_insert_nodup : forall q pages, List.NoDup pages -> List.NoDup (page_insert q pages).
Proof.
  intros q pages ND. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact ND|].
  constructor; [|exact ND]. intros Hin. apply (proj2 (page_mem_In q pages)) in Hin. congruence.
Qed.

Lemma access_pages_acc_nodup : forall n base pages, List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages ND; cbn; [exact ND|].
  apply IH. apply page_insert_nodup. exact ND.
Qed.

Lemma accesses_pages_nodup : forall accs pages, List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages ND; cbn; [exact ND|].
  apply IH. apply access_pages_acc_nodup. exact ND.
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  List.In p (access_pages_acc base n pages) ->
  List.In p pages \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_cases _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  List.In p (accesses_pages accs pages) ->
  List.In p pages \/ exists a n k, List.In (a, n) accs /\ (k < n)%nat /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin) as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition same_but_mat (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_mat_refl : forall a, same_but_mat a a.
Proof. intros a. unfold same_but_mat. destruct a as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

Lemma same_but_mat_trans : forall a b c, same_but_mat a b -> same_but_mat b c -> same_but_mat a c.
Proof.
  intros a b c -> ->. unfold same_but_mat.
  destruct a as [fd [mp lzz mt] io fs pr lm tm]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_mat_frame : forall m m', same_but_mat m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m /\
  m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\ m_lim m' = m_lim m /\
  m_time m' = m_time m.   (* [comment removed for export] *)
Proof.
  intros m m' ->. destruct m as [fd [mp lzz mt] io fs pr lm tm]; repeat split; reflexivity.
Qed.

Lemma same_but_mat_halted : forall mo mo', same_but_mat mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

Lemma same_but_mat_nonlazy : forall mo mo', same_but_mat mo mo' -> nonlazy_bytes mo' = nonlazy_bytes mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ainv_same_but_mat : forall lz AL N m m',
  same_but_mat m m' -> m_vm_materialized m' = m_vm_materialized m -> ainv lz AL N m -> ainv lz AL N m'.
Proof.
  intros lz AL N m m' SB EM [LZ ND AW FIN ROOM].
  pose proof (same_but_mat_frame _ _ SB) as (_ & VM & LZ' & _).
  constructor; rewrite ?EM, ?LZ', ?VM, ?(same_but_mat_nonlazy _ _ SB); auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_app_intro : forall {A} (l1 l2 : list A),
  List.NoDup l1 -> List.NoDup l2 -> (forall x, List.In x l1 -> ~ List.In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 N1 N2 D. induction l1 as [|x l1 IH]; cbn; [exact N2|].
  inversion N1; subst. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [contradiction|]. exact (D x (or_introl eq_refl) Hin).
  - apply IH; [assumption|]. intros y Hy. apply D. right; exact Hy.
Qed.

(* [comment removed for export] *)
Lemma account_ok : forall lz AL N m accs,
  ainv lz AL N m -> accesses_ok lz AL accs ->
  exists m', materialize_model_accesses m accs = Some m' /\ ainv lz AL N m' /\ same_but_mat m m'.
Proof.
  intros lz AL N m accs INV OK.
  destruct INV as [LZ ND AW FIN ROOM].
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs).
  assert (NEWP : forall p, List.In p new -> List.In p (accesses_pages accs []) /\ page_in_ranges p lz = true
                                      /\ ~ List.In p (m_vm_materialized m) /\ AL p).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
    apply andb_prop in Hf as [H1 H2]. rewrite LZ in H1.
    assert (~ List.In p (m_vm_materialized m)).
    { intros Hm. apply (proj2 (page_mem_In _ _)) in Hm. rewrite Hm in H2. discriminate. }
    repeat split; auto. destruct (OK p Hin) as [E|A]; [congruence|exact A]. }
  assert (NDnew : List.NoDup new).
  { unfold new, newly_materialized_pages. apply NoDup_filter. apply accesses_pages_nodup. constructor. }
  assert (NDall : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app_intro; auto. intros x Hx. apply NEWP in Hx. tauto. }
  assert (LENall : (List.length (new ++ m_vm_materialized m) <= N)%nat).
  { destruct FIN as (L & NDL & LEN & INL).
    assert (List.incl (new ++ m_vm_materialized m) L).
    { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; apply INL; [apply NEWP in Hp; tauto| auto]. }
    pose proof (NoDup_incl_length NDall H). lia. }
  destruct new as [|p0 new'] eqn:En.
  - exists m. split; [|split; [constructor; auto| apply same_but_mat_refl]].
    destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
  - rewrite <- En in *.
    assert (FIT : (vm_backing_used m + Z.of_nat (List.length new) * page_size <=? vm_limit (m_vmmaps m)) = true).
    { apply Z.leb_le. rewrite vm_backing_used_split. rewrite length_app in LENall. unfold page_size in *. nia. }
    rewrite En. rewrite <- En. rewrite FIT.
    eexists. split; [reflexivity|]. split.
    + constructor; cbn.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact LZ.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact NDall.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *.
        intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [apply NEWP in Hp; tauto|auto].
      * exact FIN.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact ROOM.
    + destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_ok : forall segs lz AL N ms mo ms' accs,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs) ->
  ainv lz AL N mo -> accesses_ok lz AL accs ->
  exists mo', mi_account_step segs ms mo = MachineOk (ms', mo') /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros segs lz AL N ms mo ms' accs Hs INV OK.
  destruct (account_ok lz AL N mo accs INV OK) as (mo' & Hm & INV' & SB).
  exists mo'. unfold mi_account_step. rewrite Hs. cbn. rewrite Hm. auto.
Qed.

(* [comment removed for export] *)
Lemma materialize_accesses_nonlazy : forall m accs,
  (forall p, List.In p (accesses_pages accs []) -> page_in_ranges p (m_vm_lazy m) = false) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs NL. unfold materialize_model_accesses, materialize_accesses.
  replace (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) with (@nil word).
  - cbn. destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
  - unfold newly_materialized_pages. symmetry.
    assert (G : forall l, (forall p, List.In p l -> page_in_ranges p (m_vm_lazy m) = false) ->
              List.filter (fun p => page_in_ranges p (m_vm_lazy m) && negb (page_mem p (m_vm_materialized m))) l = []).
    { induction l as [|p l IH]; intros Hl; cbn; [reflexivity|].
      rewrite (Hl p (or_introl eq_refl)). cbn. apply IH. intros q Hq. apply Hl. right; exact Hq. }
    apply G. exact NL.
Qed.
