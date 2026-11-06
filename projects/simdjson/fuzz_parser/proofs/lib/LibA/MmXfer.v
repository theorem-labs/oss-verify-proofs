(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import AcctCore ModelX.
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_true : forall {A} (l : list A), List.filter (fun _ => true) l = l.
Proof. induction l; cbn; congruence. Qed.

Lemma filter_and : forall {A} (f g : A -> bool) (l : list A),
  List.filter f (List.filter g l) = List.filter (fun a => g a && f a) l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  destruct (g x); cbn; [|exact IH]. destruct (f x); cbn; congruence.
Qed.

Lemma filter_length_le : forall {A} (f : A -> bool) (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma NoDup_filter' : forall {A} (f : A -> bool) (l : list A), List.NoDup l -> List.NoDup (List.filter f l).
Proof. intros. apply NoDup_filter. assumption. Qed.

Lemma incl_filter : forall {A} (f : A -> bool) (l : list A), List.incl (List.filter f l) l.
Proof. intros A f l x Hx. apply filter_In in Hx. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition relX (mo : Model) (mat : list word) (rX r : check_result) : Prop :=
  match rX, r with
  | CheckOk mX eX, CheckOk m e =>
      eX = e /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
      exists f, mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo)
  | CheckReject, CheckReject => True
  | CheckUnmodeled, CheckUnmodeled => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Lemma relX_ok_l : forall mo mat mX eX r,
  relX mo mat (CheckOk mX eX) r ->
  exists m f, r = CheckOk m eX /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
              mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof. intros mo mat mX eX [m e| |] H; cbn in H; try contradiction. destruct H as (-> & S & f & A & B). eauto 6. Qed.

Lemma relX_ok_r : forall mo mat rX m e,
  relX mo mat rX (CheckOk m e) ->
  strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
  exists f, rX = CheckOk (MX m (List.filter f mat)) e /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof. intros mo mat [mX eX| |] m e H; cbn in H; try contradiction. destruct H as (-> & S & f & -> & B). eauto. Qed.

Lemma relX_unmodeled : forall mo mat rX r, relX mo mat rX r -> (rX = CheckUnmodeled <-> r = CheckUnmodeled).
Proof. intros mo mat [| |] [| |] H; cbn in H; try contradiction; split; congruence. Qed.

(* [comment removed for export] *)
Lemma strip_self : forall mo, strip mo = with_vmmaps (m_vmmaps mo) (strip mo).
Proof. intros mo. reflexivity. Qed.

Lemma relX_id : forall mo mat e, relX mo mat (CheckOk (MX mo mat) e) (CheckOk mo e).
Proof.
  intros mo mat e. cbn. split; [reflexivity|]. split; [apply strip_self|]. exists (fun _ => true). rewrite !filter_true. auto.
Qed.

Lemma relX_filter : forall mo mat m f e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
  relX mo mat (CheckOk (MX m (List.filter f mat)) e) (CheckOk m e).
Proof. intros mo mat m f e S H. cbn. split; [reflexivity|]. split; [exact S|]. exists f. auto. Qed.

Lemma relX_same : forall mo mat m e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = m_vm_materialized mo ->
  relX mo mat (CheckOk (MX m mat) e) (CheckOk m e).
Proof.
  intros mo mat m e S H. cbn. split; [reflexivity|]. split; [exact S|]. exists (fun _ => true). rewrite !filter_true. auto.
Qed.

Lemma relX_reject : forall mo mat, relX mo mat CheckReject CheckReject. Proof. intros; exact I. Qed.
Lemma relX_unm : forall mo mat, relX mo mat CheckUnmodeled CheckUnmodeled. Proof. intros; exact I. Qed.

Lemma relX_ret_only : forall mo mat eff r e,
  relX mo mat (check_ret_only eff r (MX mo mat) e) (check_ret_only eff r mo e).
Proof.
  intros mo mat [ret ws zs us cs ci] r e. unfold check_ret_only.
  destruct ws; [|exact I]. destruct zs; [|exact I]. destruct us; [|exact I]. destruct cs; [|exact I]. destruct ci; [|exact I].
  destruct (bv_eqb ret r); [apply relX_id| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_mmap_backing_MX : forall flags a n m mat,
  with_mmap_backing flags a n (MX m mat) = MX (with_mmap_backing flags a n m) mat.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma mat_with_mmap_backing : forall flags a n m,
  m_vm_materialized (with_mmap_backing flags a n m) = m_vm_materialized m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma vmmaps_with_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_destroyed_MX : forall a n h m mat,
  with_mmap_destroyed a n h (MX m mat) =
  MX (with_mmap_destroyed a n h m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. reflexivity. Qed.

Lemma mat_with_mmap_destroyed : forall a n h m,
  m_vm_materialized (with_mmap_destroyed a n h m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. reflexivity. Qed.

Lemma with_mmap_replacement_MX : forall flags a n m mat,
  with_mmap_replacement flags a n (MX m mat) =
  MX (with_mmap_replacement flags a n m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. unfold with_mmap_replacement. rewrite vm_forget_range_MX. apply with_mmap_backing_MX. Qed.

Lemma mat_with_mmap_replacement : forall flags a n m,
  m_vm_materialized (with_mmap_replacement flags a n m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. unfold with_mmap_replacement. rewrite mat_with_mmap_backing. reflexivity. Qed.

Lemma vmmaps_with_mmap_replacement : forall flags a n m,
  m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite vmmaps_with_mmap_backing. reflexivity. Qed.

Lemma mprotect_model_next_MX : forall m mat a n,
  mprotect_model_next (MX m mat) a n = MX (mprotect_model_next m a n) mat.
Proof. intros. reflexivity. Qed.

Lemma mat_mprotect_model_next : forall m a n, m_vm_materialized (mprotect_model_next m a n) = m_vm_materialized m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_next_MX : forall m mat a n,
  madvise_dontneed_next (MX m mat) a n =
  MX (madvise_dontneed_next m a n) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. reflexivity. Qed.

Lemma mat_madvise_dontneed_next : forall m a n,
  m_vm_materialized (madvise_dontneed_next m a n) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. reflexivity. Qed.

Lemma vmmaps_madvise_dontneed_next : forall m a n, m_vmmaps (madvise_dontneed_next m a n) = m_vmmaps m.
Proof. intros. reflexivity. Qed.

Lemma madvise_dontneed_next_canon : forall m a n,
  m_vm_materialized m = [] -> madvise_dontneed_next m a n = m.
Proof.
  intros m a n H. unfold madvise_dontneed_next. rewrite H. cbn [List.filter].
  rewrite <- H. apply (MX_mat m).
Qed.

(* [comment removed for export] *)
Fixpoint ranges_keep (ranges : list (word * word)) (p : word) : bool :=
  match ranges with
  | [] => true
  | (a, n) :: rest => page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) p && ranges_keep rest p
  end.

Lemma forget_vm_ranges_MX : forall l m mat,
  forget_vm_ranges l (MX m mat) = MX (forget_vm_ranges l m) (List.filter (ranges_keep l) mat)
  /\ m_vm_materialized (forget_vm_ranges l m) = List.filter (ranges_keep l) (m_vm_materialized m)
  /\ m_vmmaps (forget_vm_ranges l m) = m_vmmaps m.
Proof.
  induction l as [|[a n] l IH]; intros m mat; cbn [forget_vm_ranges ranges_keep].
  - rewrite !filter_true. repeat split; reflexivity.
  - rewrite vm_forget_range_MX.
    destruct (IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)
                 (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat)) as (E1 & E2 & E3).
    rewrite E1, E2, E3, !filter_and.
    change (m_vm_materialized (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m))
      with (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m)).
    rewrite filter_and. repeat split; reflexivity.
Qed.

Lemma forget_vm_ranges_strip : forall l m,
  strip (forget_vm_ranges l m) = with_vmmaps (m_vmmaps (forget_vm_ranges l m)) (strip m).
Proof.
  induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges].
  - apply strip_self.
  - rewrite IH. reflexivity.
Qed.

Lemma with_brk_next_MX : forall m mat req r,
  with_brk_next (MX m mat) req r = MX (with_brk_next m req r) (List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) mat)
  /\ m_vm_materialized (with_brk_next m req r) =
       List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) (m_vm_materialized m).
Proof.
  intros m mat req r. unfold with_brk_next. rewrite m_vmmaps_MX, with_vmmaps_MX.
  destruct (forget_vm_ranges_MX (brk_unmaps r (vm_brk (m_vmmaps m))) (with_vmmaps (brk_model_next (m_vmmaps m) req r) m) mat)
    as (E1 & E2 & _).
  rewrite E1, E2. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Slack.
Variable NMAX : nat.

Definition robust (x lim : Z) : Prop := x + Z.of_nat NMAX * page_size <= lim \/ lim < x.

Lemma robust_leb : forall x lim d, robust x lim -> 0 <= d <= Z.of_nat NMAX * page_size ->
  (x + d <=? lim) = (x <=? lim).
Proof. intros x lim d [H|H] Hd; apply eq_true_iff_eq; rewrite !Z.leb_le; lia. Qed.

Lemma vm_backing_used_canon : forall m, m_vm_materialized m = [] -> vm_backing_used m = nonlazy_bytes m.
Proof. intros m H. rewrite vm_backing_used_split, H. cbn. lia. Qed.

Lemma mat_bound : forall (mat : list word) f, (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length (List.filter f mat)) * page_size <= Z.of_nat NMAX * page_size.
Proof. intros mat f H. pose proof (filter_length_le f mat). unfold page_size. nia. Qed.

Lemma mat_bound0 : forall (mat : list word), (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length mat) * page_size <= Z.of_nat NMAX * page_size.
Proof. intros mat H. unfold page_size. nia. Qed.

(* [comment removed for export] *)
Lemma backing_within_limit_X : forall m' mat f,
  m_vm_materialized m' = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes m') (vm_limit (m_vmmaps m')) ->
  vm_backing_within_limit (MX m' (List.filter f mat)) = vm_backing_within_limit m'.
Proof.
  intros m' mat f CAN LEN R. unfold vm_backing_within_limit.
  rewrite vm_backing_used_MX, m_vmmaps_MX, (vm_backing_used_canon m' CAN).
  apply robust_leb; [exact R| apply mat_bound; exact LEN].
Qed.

Lemma noreserve_backed_ok_X : forall flags mo mat nZ,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  (mmap_noreserve_b flags = true \/ robust (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
  mmap_noreserve_backed_ok flags (MX mo mat) nZ = mmap_noreserve_backed_ok flags mo nZ.
Proof.
  intros flags mo mat nZ CAN LEN R. unfold mmap_noreserve_backed_ok.
  destruct (mmap_noreserve_b flags) eqn:E; [reflexivity|].
  destruct R as [R|R]; [congruence|].
  rewrite vm_backing_used_MX, m_vmmaps_MX, (vm_backing_used_canon mo CAN).
  replace (nonlazy_bytes mo + Z.of_nat (length mat) * page_size + nZ) with (nonlazy_bytes mo + nZ + Z.of_nat (length mat) * page_size) by lia.
  apply robust_leb; [exact R| apply mat_bound0; exact LEN].
Qed.

Lemma fixed_rw_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_budget_ok flags mo addr n.
Proof.
  intros flags mo mat addr n CAN LEN R. unfold mmap_fixed_rw_budget_ok.
  rewrite m_vmmaps_MX, with_vmmaps_MX, with_mmap_replacement_MX.
  apply backing_within_limit_X.
  - rewrite mat_with_mmap_replacement. change (m_vm_materialized (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo)) with (m_vm_materialized mo).
    rewrite CAN. reflexivity.
  - exact LEN.
  - rewrite vmmaps_with_mmap_replacement. exact R.
Qed.

(* [comment removed for export] *)
Lemma fixed_rw_span_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_span_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_span_budget_ok flags mo addr n.
Proof.
  intros flags mo mat addr n CAN LEN R. unfold mmap_fixed_rw_span_budget_ok.
  rewrite m_vmmaps_MX, with_vmmaps_MX, with_mmap_replacement_MX.
  apply backing_within_limit_X.
  - rewrite mat_with_mmap_replacement. change (m_vm_materialized (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo)) with (m_vm_materialized mo).
    rewrite CAN. reflexivity.
  - exact LEN.
  - rewrite vmmaps_with_mmap_replacement. exact R.
Qed.

Lemma mprotect_budget_ok_X : forall mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (mprotect_model_next mo addr n)) (vm_limit (m_vmmaps mo)) ->
  mprotect_budget_ok (MX mo mat) addr n = mprotect_budget_ok mo addr n.
Proof.
  intros mo mat addr n CAN LEN R. unfold mprotect_budget_ok. rewrite mprotect_model_next_MX.
  rewrite <- (filter_true mat). apply backing_within_limit_X; [exact CAN| exact LEN| exact R].
Qed.

Lemma brk_r_ok_X : forall mo mat req r,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes mo + bv_unsigned (bv_sub req (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo)) ->
  brk_r_ok (MX mo mat) req r = brk_r_ok mo req r.
Proof.
  intros mo mat req r CAN LEN R. unfold brk_r_ok, brk_grow_ok, brk_budget_ok. rewrite !m_vmmaps_MX.
  rewrite vm_backing_used_MX, (vm_backing_used_canon mo CAN).
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo))))%bool; [reflexivity|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo))); [reflexivity|].
  destruct (bv_eqb r req) eqn:Er; cbn [orb].
  - apply bv_eqb_eq in Er. subst r.
    destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps mo))) && (bv_unsigned (vm_brk (m_vmmaps mo)) <? bv_unsigned req))%bool; [|reflexivity].
    f_equal. f_equal.
    replace (nonlazy_bytes mo + Z.of_nat (length mat) * page_size + bv_unsigned (req - vm_brk (m_vmmaps mo)))
      with (nonlazy_bytes mo + bv_unsigned (req - vm_brk (m_vmmaps mo)) + Z.of_nat (length mat) * page_size) by lia.
    apply robust_leb; [exact R| apply mat_bound0; exact LEN].
  - destruct (bv_eqb r (vm_brk (m_vmmaps mo))) eqn:Eb; cbn [andb]; [|reflexivity].
    apply bv_eqb_eq in Eb. subst r.
    destruct (0 <? bv_unsigned (vm_brk (m_vmmaps mo))); cbn [andb]; [|reflexivity].
    rewrite Z.ltb_irrefl. reflexivity.
Qed.

End Slack.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strip_with_vmmaps : forall h m, strip (with_vmmaps h m) = with_vmmaps h (strip m). Proof. reflexivity. Qed.
Lemma vmmaps_strip : forall m, m_vmmaps (strip m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma strip_vm_add_lazy : forall a n m, strip (vm_add_lazy a n m) = strip m. Proof. reflexivity. Qed.
Lemma strip_vm_forget_range : forall lo hi m, strip (vm_forget_range lo hi m) = strip m. Proof. reflexivity. Qed.
Lemma strip_with_mmap_backing : forall f a n m, strip (with_mmap_backing f a n m) = strip m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma strip_with_mmap_destroyed : forall a n h m, strip (with_mmap_destroyed a n h m) = with_vmmaps h (strip m).
Proof. reflexivity. Qed.
Lemma strip_with_mmap_replacement : forall f a n m, strip (with_mmap_replacement f a n m) = strip m.
Proof. intros. unfold with_mmap_replacement. rewrite strip_with_mmap_backing. reflexivity. Qed.
Lemma strip_mprotect_model_next : forall m a n, strip (mprotect_model_next m a n) = with_vmmaps (m_vmmaps (mprotect_model_next m a n)) (strip m).
Proof. reflexivity. Qed.
Lemma strip_madvise_dontneed_next : forall m a n, strip (madvise_dontneed_next m a n) = strip m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_idem : forall h h' m, with_vmmaps h (with_vmmaps h' m) = with_vmmaps h m. Proof. reflexivity. Qed.
Lemma with_vmmaps_strip_vmmaps : forall m h, with_vmmaps (m_vmmaps (with_vmmaps h (strip m))) (strip m) = with_vmmaps h (strip m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac strip_tac :=
  rewrite ?strip_with_mmap_replacement, ?strip_with_mmap_backing, ?strip_with_mmap_destroyed, ?strip_with_vmmaps,
          ?vmmaps_with_mmap_replacement, ?vmmaps_with_mmap_backing;
  first [ reflexivity | apply strip_self ].

(* [comment removed for export] *)
Ltac xfer_leaf :=
  first [ exact I
        | apply relX_id
        | apply relX_same; [ strip_tac | rewrite ?mat_with_mmap_backing; reflexivity ]
        | apply relX_filter; [ strip_tac | rewrite ?mat_with_mmap_replacement, ?mat_with_mmap_backing; reflexivity ]
        | apply relX_ret_only ].

(* [comment removed for export] *)
Ltac xfer_push :=
  progress (rewrite ?m_vmmaps_MX, ?with_vmmaps_MX, ?with_mmap_backing_MX, ?with_mmap_destroyed_MX,
                    ?with_mmap_replacement_MX, ?mprotect_model_next_MX).

Ltac xfer :=
  cbv zeta;
  repeat first
    [ xfer_leaf
    | lazymatch goal with
      | |- relX _ _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x
      end
    | xfer_push ].

Section Transfer.
Variable NMAX : nat.

Lemma check_munmap_X : forall addr len eff mo mat,
  relX mo mat (check_munmap addr len eff (MX mo mat)) (check_munmap addr len eff mo).
Proof.
  intros addr len eff mo mat. unfold check_munmap.
  rewrite !m_vmmaps_MX, !with_mmap_destroyed_MX.
  xfer.
Qed.

(* [comment removed for export] *)
Lemma check_madvise_X : forall addr len advice eff mo mat,
  relX mo mat (check_madvise addr len advice eff (MX mo mat)) (check_madvise addr len advice eff mo).
Proof.
  intros addr len advice eff mo mat. unfold check_madvise.
  rewrite !m_vmmaps_MX, !madvise_dontneed_next_MX.
  xfer;
    (apply relX_filter; [ rewrite strip_madvise_dontneed_next, vmmaps_madvise_dontneed_next; apply strip_self
                        | apply mat_madvise_dontneed_next ]).
Qed.

Lemma check_mprotect_X : forall addr len prot eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust NMAX (nonlazy_bytes (mprotect_model_next mo addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))))
              (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_mprotect addr len prot eff (MX mo mat)) (check_mprotect addr len prot eff mo).
Proof.
  intros addr len prot eff mo mat CAN LEN R. unfold check_mprotect.
  rewrite !(mprotect_budget_ok_X NMAX) by assumption.
  rewrite !m_vmmaps_MX, !mprotect_model_next_MX.
  xfer.
Qed.

Lemma check_brk_X : forall req eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust NMAX (nonlazy_bytes mo + bv_unsigned (bv_sub req (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_brk req eff (MX mo mat)) (check_brk req eff mo).
Proof.
  intros req eff mo mat CAN LEN R. unfold check_brk.
  destruct (with_brk_next_MX mo mat req (eff_ret eff)) as [E1 E2].
  destruct eff as [r ws zs us cs ci]; cbn [eff_ret] in E1, E2.
  destruct ws; [|exact I]. destruct cs; [|exact I]. destruct ci; [|exact I].
  rewrite !(brk_r_ok_X NMAX) by assumption. rewrite !m_vmmaps_MX.
  xfer. rewrite E1. apply relX_filter; [| exact E2].
  unfold with_brk_next. rewrite forget_vm_ranges_strip. reflexivity.
Qed.

Lemma check_mmap_X : forall addr len prot flags fd off eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  (mmap_noreserve_b flags = true \/ robust NMAX (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
  robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                                 (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
              (vm_limit (m_vmmaps mo)) ->
  (* [comment removed for export] *)
  robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                                 (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
              (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_mmap addr len prot flags fd off eff (MX mo mat)) (check_mmap addr len prot flags fd off eff mo).
Proof.
  intros addr len prot flags fd off eff mo mat CAN LEN nZ R1 R2 R3. unfold check_mmap.
  rewrite !(noreserve_backed_ok_X NMAX) by assumption.
  rewrite !(fixed_rw_budget_ok_X NMAX) by assumption.
  rewrite !(fixed_rw_span_budget_ok_X NMAX) by assumption.
  rewrite !m_vmmaps_MX, !with_vmmaps_MX, !with_mmap_backing_MX, !with_mmap_destroyed_MX, !with_mmap_replacement_MX.
  xfer.
Qed.

End Transfer.
