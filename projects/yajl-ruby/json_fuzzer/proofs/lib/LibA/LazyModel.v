(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition acc_page (x : acc) (k : nat) : word :=
  page_base_of (bv_unsigned (fst x) + Z.of_nat k)%Z.

Definition acc_nowrap (x : acc) : Prop := (bv_unsigned (fst x) + Z.of_nat (snd x) <= 2 ^ 64)%Z.

(* [comment removed for export] *)
Definition acc_out (L : list (word * word)) (x : acc) : Prop :=
  acc_nowrap x /\
  forall lo sz, In (lo, sz) L ->
    (bv_unsigned (fst x) + Z.of_nat (snd x) <= bv_unsigned lo
     \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned (fst x))%Z.

(* [comment removed for export] *)
Definition acc_inS (S : word -> Prop) (x : acc) : Prop :=
  acc_nowrap x /\ forall k, (k < snd x)%nat -> S (acc_page x k).

Definition acc_ok (L : list (word * word)) (S : word -> Prop) (x : acc) : Prop :=
  acc_out L x \/ acc_inS S x.

Lemma acc_out_ok : forall L S x, acc_out L x -> acc_ok L S x.
Proof. intros; left; assumption. Qed.

(* [comment removed for export] *)
Lemma acc_out_intro : forall L (a : Z) (n : nat),
  (0 <= a < 2^64)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
  (forall lo sz, In (lo, sz) L -> (a + Z.of_nat n <= bv_unsigned lo \/ bv_unsigned lo + bv_unsigned sz <= a)%Z) ->
  acc_out L (Z_to_bv 64 a, n).
Proof.
  intros L a n Ha Hn HL. unfold acc_out, acc_nowrap. cbn [fst snd].
  rewrite unsigned_lit by lia. split; [lia|]. exact HL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hq & E). apply bv_eqb_eq in E. subst. exact Hq.
  - intros H. exists p. split; [exact H|]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma page_insert_nodup : forall p pages, List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages H. unfold page_insert. destruct (page_mem p pages) eqn:E; [exact H|].
  constructor; [|exact H]. intros Hin. apply (proj2 (page_mem_In p pages)) in Hin. congruence.
Qed.

Lemma page_insert_in : forall p q pages, In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H. destruct (page_mem q pages); [right; exact H|].
  destruct H as [H|H]; [left; symmetry; exact H| right; exact H].
Qed.

Lemma access_pages_acc_nodup : forall n base pages, List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof. induction n as [|n IH]; intros base pages H; cbn; [exact H|]. apply IH. apply page_insert_nodup. exact H. Qed.

Lemma accesses_pages_nodup : forall rs pages, List.NoDup pages -> List.NoDup (accesses_pages rs pages).
Proof.
  induction rs as [|[a n] rs IH]; intros pages H; cbn; [exact H|].
  apply IH. apply access_pages_acc_nodup. exact H.
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall rs pages p,
  In p (accesses_pages rs pages) ->
  In p pages \/ exists x k, In x rs /\ (k < snd x)%nat /\ p = acc_page x k.
Proof.
  induction rs as [|[a n] rs IH]; cbn [accesses_pages]; intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (x & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin) as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists (a, n), k. split; [left; reflexivity | split; assumption].
    + right. exists x, k. split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_outside : forall L x k,
  (k < snd x)%nat -> acc_out L x -> page_in_ranges (acc_page x k) L = false.
Proof.
  intros L [a n] k Hk [Hnw Hout]. unfold acc_nowrap in Hnw. cbn [fst snd] in *. unfold acc_page. cbn [fst].
  pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  assert (Hz : (0 <= z < 2^64)%Z) by (unfold z; lia).
  pose proof (Z.div_mod z page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z) = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. unfold page_size in *. lia. }
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue. apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest). cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. rewrite Hpb in Hlo, Hhi.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg. unfold bv_modulus in Hlo_rg.
  destruct (Hout lo sz Hin) as [Hd|Hd]; unfold page_size in *; unfold z in *; lia.
Qed.

Lemma NoDup_filter {A} : forall (f : A -> bool) l, List.NoDup l -> List.NoDup (List.filter f l).
Proof.
  intros f l H; induction H as [|x l Hx H IH]; cbn; [constructor|].
  destruct (f x); [|exact IH]. constructor; [|exact IH]. intros Hin. apply filter_In in Hin. tauto.
Qed.

Lemma NoDup_app_disj {A} : forall (l1 l2 : list A),
  List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 Hd; induction H1 as [|x l Hx H IH]; cbn; [exact H2|].
  constructor.
  - rewrite in_app_iff. intros [K|K]; [exact (Hx K)| exact (Hd x (or_introl eq_refl) K)].
  - apply IH. intros y Hy. apply Hd. right; exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vm_backing_id : forall m, with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Theorem materialize_disjoint : forall L mo rs,
  incl (m_vm_lazy mo) L -> Forall (acc_out L) rs ->
  materialize_model_accesses mo rs = Some mo.
Proof.
  intros L mo rs HL Hrs.
  assert (Hnew : newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) rs = []).
  { unfold newly_materialized_pages. 
    assert (G : forall p, In p (accesses_pages rs []) -> page_in_ranges p (m_vm_lazy mo) && negb (page_mem p (m_vm_materialized mo)) = false).
    { intros p Hp. destruct (accesses_pages_in rs [] p Hp) as [[] | (x & k & Hin & Hk & ->)].
      rewrite (page_in_ranges_outside (m_vm_lazy mo) x k Hk); [reflexivity|].
      pose proof (proj1 (Forall_forall _ _) Hrs x Hin) as [Hnw Ho]. split; [exact Hnw|].
      intros lo sz Hlz. apply Ho. apply HL. exact Hlz. }
    induction (accesses_pages rs []) as [|p l IH]; cbn; [reflexivity|].
    rewrite (G p (or_introl eq_refl)). apply IH. intros q Hq. apply G. right; exact Hq. }
  unfold materialize_model_accesses, materialize_accesses. rewrite Hnew. cbv beta iota zeta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eager_used (mo : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo)).

Lemma vm_backing_used_split : forall mo,
  vm_backing_used mo = (eager_used mo + Z.of_nat (length (m_vm_materialized mo)) * page_size)%Z.
Proof. reflexivity. Qed.

Section LI.
(* [comment removed for export] *)
Variable S : word -> Prop.            (* [comment removed for export] *)
Variable N : nat.                     (* [comment removed for export] *)
Variable EB : Z.                      (* [comment removed for export] *)

Record LI (mo : Model) : Prop := {
  li_nodup  : List.NoDup (m_vm_materialized mo);
  li_inS    : Forall S (m_vm_materialized mo);
  li_cap    : forall l, List.NoDup l -> Forall S l -> (length l <= N)%nat;
  li_eager  : (eager_used mo <= EB)%Z;
  li_budget : (EB + Z.of_nat N * page_size <= vm_limit (m_vmmaps mo))%Z
}.

(* [comment removed for export] *)
Definition magree (mo mo' : Model) : Prop :=
  exists M', mo' = with_vm_backing (m_vm_lazy mo) M' mo.

Lemma magree_refl : forall mo, magree mo mo.
Proof. intros mo. exists (m_vm_materialized mo). symmetry. apply with_vm_backing_id. Qed.

Lemma magree_trans : forall a b c, magree a b -> magree b c -> magree a c.
Proof.
  intros a b c [M1 ->] [M2 ->]. exists M2.
  destruct a as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma magree_frame : forall mo mo', magree mo mo' ->
  m_fds mo' = m_fds mo /\ m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo /\
  m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\ m_tid mo' = m_tid mo /\ m_stdin mo' = m_stdin mo /\
  m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\ m_proc mo' = m_proc mo /\ m_lim mo' = m_lim mo /\ m_fd mo' = m_fd mo.
Proof. intros mo mo' [M' ->]. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

Lemma magree_lazy : forall mo mo', magree mo mo' -> m_vm_lazy mo' = m_vm_lazy mo.
Proof. intros mo mo' H. apply (magree_frame mo mo' H). Qed.
Lemma magree_halted : forall mo mo', magree mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' H. apply (magree_frame mo mo' H). Qed.
Lemma magree_vmmaps : forall mo mo', magree mo mo' -> m_vmmaps mo' = m_vmmaps mo.
Proof. intros mo mo' H. apply (magree_frame mo mo' H). Qed.

(* [comment removed for export] *)
Theorem materialize_ok : forall mo rs,
  LI mo -> Forall (acc_ok (m_vm_lazy mo) S) rs ->
  exists M', materialize_model_accesses mo rs = Some (with_vm_backing (m_vm_lazy mo) M' mo)
             /\ LI (with_vm_backing (m_vm_lazy mo) M' mo).
Proof.
  intros mo rs HLI Hrs. destruct HLI as [HND HS HC HE HB].
  set (L := m_vm_lazy mo) in *.
  set (M := m_vm_materialized mo) in *.
  set (new := newly_materialized_pages L M rs).
  (* [comment removed for export] *)
  assert (HnewS : Forall S new).
  { apply Forall_forall. intros p Hp. unfold new, newly_materialized_pages in Hp.
    apply filter_In in Hp. destruct Hp as [Hp Hf]. apply andb_true_iff in Hf. destruct Hf as [Hin _].
    destruct (accesses_pages_in rs [] p Hp) as [[] | (x & k & Hx & Hk & ->)].
    destruct (proj1 (Forall_forall _ _) Hrs x Hx) as [Ho | [_ HSx]].
    - rewrite (page_in_ranges_outside L x k Hk Ho) in Hin. discriminate.
    - apply HSx. exact Hk. }
  assert (HnewND : List.NoDup new).
  { unfold new, newly_materialized_pages. apply NoDup_filter. apply accesses_pages_nodup. constructor. }
  assert (Hdisj : forall p, In p new -> ~ In p M).
  { intros p Hp HM. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp.
    destruct Hp as [_ Hf]. apply andb_true_iff in Hf. destruct Hf as [_ Hnm].
    apply (proj2 (page_mem_In p M)) in HM. rewrite HM in Hnm. discriminate. }
  assert (HND' : List.NoDup (new ++ M)) by (apply NoDup_app_disj; assumption).
  assert (HS' : Forall S (new ++ M)) by (apply Forall_app; split; assumption).
  pose proof (HC _ HND' HS') as Hlen. rewrite length_app in Hlen.
  unfold materialize_model_accesses. fold L. fold M. unfold materialize_accesses. fold new.
  destruct new as [|p new'] eqn:En.
  - exists M. split; [reflexivity|]. constructor; cbn; auto.
  - rewrite <- En in *.
    replace (vm_backing_used mo + Z.of_nat (length new) * page_size <=? vm_limit (m_vmmaps mo))%Z with true.
    2:{ symmetry. apply Z.leb_le. rewrite vm_backing_used_split. fold M. unfold page_size in *. nia. }
    exists (new ++ M). split; [reflexivity|]. constructor; cbn; auto.
Qed.

(* [comment removed for export] *)
Lemma LI_transfer : forall mo mo',
  LI mo ->
  (forall p, In p (m_vm_materialized mo') -> In p (m_vm_materialized mo)) ->
  List.NoDup (m_vm_materialized mo') ->
  (eager_used mo' <= EB)%Z -> vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  LI mo'.
Proof.
  intros mo mo' [HND HS HC HE HB] Hsub HND' HE' HL. constructor; auto.
  - apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HS). apply Hsub. exact Hp.
  - rewrite HL. exact HB.
Qed.

(* [comment removed for export] *)
Lemma NoDup_filter_pages : forall f (l : list word), List.NoDup l -> List.NoDup (List.filter f l).
Proof. intros; apply NoDup_filter; assumption. Qed.

End LI.

(* [comment removed for export] *)
Lemma LI_grow : forall (S S' : word -> Prop) N N' EB EB' mo,
  LI S N EB mo ->
  (forall p, S p -> S' p) ->
  (forall l, List.NoDup l -> Forall S' l -> (length l <= N')%nat) ->
  (EB <= EB')%Z ->
  (EB' + Z.of_nat N' * page_size <= vm_limit (m_vmmaps mo))%Z ->
  LI S' N' EB' mo.
Proof.
  intros S S' N N' EB EB' mo [HND HS HC HE HB] HSS' HC' HEB HB'. constructor; auto.
  - eapply Forall_impl; [|exact HS]. exact HSS'.
  - lia.
Qed.

(* [comment removed for export] *)
Definition lazy_disjoint (mo : Model) (lo hi : Z) : Prop :=
  forall l sz, In (l, sz) (m_vm_lazy mo) ->
    (hi <= bv_unsigned l \/ bv_unsigned l + bv_unsigned sz <= lo)%Z.

Lemma lazy_disjoint_acc_out : forall mo lo hi (a : Z) (n : nat),
  lazy_disjoint mo lo hi -> (0 <= lo)%Z -> (hi <= 2^64)%Z ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (a < 2^64)%Z ->
  acc_out (m_vm_lazy mo) (Z_to_bv 64 a, n).
Proof.
  intros mo lo hi a n HD Hlo Hhi Ha Hn Ha'. apply acc_out_intro; [lia|lia|].
  intros l sz Hin. destruct (HD l sz Hin); lia.
Qed.

Lemma lazy_disjoint_sub : forall mo lo hi lo' hi',
  lazy_disjoint mo lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> lazy_disjoint mo lo' hi'.
Proof. intros mo lo hi lo' hi' H H1 H2 l sz Hin. destruct (H l sz Hin); lia. Qed.

Lemma lazy_disjoint_magree : forall mo mo' lo hi,
  magree mo mo' -> lazy_disjoint mo lo hi -> lazy_disjoint mo' lo hi.
Proof. intros mo mo' lo hi Hag H l sz Hin. rewrite (magree_lazy _ _ Hag) in Hin. exact (H l sz Hin). Qed.

(* [comment removed for export] *)
Definition pages_budgeted (S : word -> Prop) (lo hi : Z) : Prop :=
  forall z, (lo <= z < hi)%Z -> S (page_base_of z).

Lemma pages_budgeted_acc_inS : forall S lo hi (a : Z) (n : nat),
  pages_budgeted S lo hi -> (0 <= a < 2^64)%Z -> (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (hi <= 2^64)%Z ->
  acc_inS S (Z_to_bv 64 a, n).
Proof.
  intros S lo hi a n HB H0 Hlo Hhi H64. split.
  - unfold acc_nowrap. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
  - intros k Hk. unfold acc_page. cbn [fst snd] in Hk |- *. rewrite unsigned_lit by lia. apply HB. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma mi_account_step_resA : forall ms mo ms' rs,
  resA (RiscvSemantics.step_accesses segs ms) = MachineOk (ms', rs) ->
  mi_account_step segs ms mo =
    match materialize_model_accesses mo rs with
    | Some mo' => MachineOk (ms', mo')
    | None => MachineFault
    end.
Proof.
  intros ms mo ms' rs H. unfold mi_account_step. rewrite (resA_report _ _ _ _ H). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_disjoint : forall L ms mo ms' rs,
  m_halted mo = None -> incl (m_vm_lazy mo) L ->
  mstepA segs ms ms' rs -> Forall (acc_out L) rs ->
  sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo))
  /\ (forall e st, sstep segs (mkCfg ms mo) e st -> e = [] /\ st = SNext (mkCfg ms' mo)).
Proof.
  intros L ms mo ms' rs Hh HL [Hsvc Hst] Hrs.
  assert (E : mi_account_step segs ms mo = MachineOk (ms', mo)).
  { rewrite (mi_account_step_resA _ _ _ _ Hst). rewrite (materialize_disjoint L mo rs HL Hrs). reflexivity. }
  split.
  - apply sstep_instr; assumption.
  - intros e st Hss. inversion Hss; subst; try congruence;
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite E in H; inversion H; subst end; auto.
Qed.

(* [comment removed for export] *)
Lemma sstep_ok : forall S N EB ms mo ms' rs,
  m_halted mo = None -> LI S N EB mo ->
  mstepA segs ms ms' rs -> Forall (acc_ok (m_vm_lazy mo) S) rs ->
  exists mo',
    magree mo mo' /\ LI S N EB mo' /\ m_halted mo' = None
    /\ sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo'))
    /\ (forall e st, sstep segs (mkCfg ms mo) e st -> e = [] /\ st = SNext (mkCfg ms' mo')).
Proof.
  intros S N EB ms mo ms' rs Hh HLI [Hsvc Hst] Hrs.
  destruct (materialize_ok S N EB mo rs HLI Hrs) as (M' & Hmat & HLI').
  set (mo' := with_vm_backing (m_vm_lazy mo) M' mo) in *.
  assert (E : mi_account_step segs ms mo = MachineOk (ms', mo')).
  { rewrite (mi_account_step_resA _ _ _ _ Hst). rewrite Hmat. reflexivity. }
  exists mo'. split; [|split; [exact HLI'|split; [|split]]].
  - exists M'. reflexivity.
  - unfold mo'. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. exact Hh.
  - apply sstep_instr; assumption.
  - intros e st Hss. inversion Hss; subst; try congruence;
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite E in H; inversion H; subst end; auto.
Qed.

(* [comment removed for export] *)
Lemma mstepsA_star : forall S N EB L ms ms' mo,
  m_halted mo = None -> LI S N EB mo -> m_vm_lazy mo = L ->
  mstepsA segs (acc_ok L S) ms ms' ->
  exists mo', magree mo mo' /\ LI S N EB mo' /\ m_halted mo' = None
              /\ star segs (mkCfg ms mo) [] (mkCfg ms' mo').
Proof.
  intros S N EB L ms ms' mo Hh HLI HL Hrun. revert mo Hh HLI HL.
  induction Hrun as [ms|ms ms1 ms2 rs Hst Hrs Hrun IH]; intros mo Hh HLI HL.
  - exists mo. split; [apply magree_refl|]. split; [exact HLI|]. split; [exact Hh|]. apply star_refl.
  - subst L. destruct (sstep_ok S N EB ms mo ms1 rs Hh HLI Hst Hrs) as (mo1 & Hag & HLI1 & Hh1 & Hss & _).
    destruct (IH mo1 Hh1 HLI1 (magree_lazy _ _ Hag)) as (mo' & Hag' & HLI' & Hh' & Hstar).
    exists mo'. split; [eapply magree_trans; eauto|]. split; [exact HLI'|]. split; [exact Hh'|].
    change ([] : list event) with ([] ++ [] : list event). eapply star_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rzA_step_disjoint : forall L ms mo ms' rs T,
  m_halted mo = None -> incl (m_vm_lazy mo) L ->
  mstepA segs ms ms' rs -> Forall (acc_out L) rs ->
  realizes segs (mkCfg ms' mo) T -> realizes segs (mkCfg ms mo) T.
Proof.
  intros L ms mo ms' rs T Hh HL Hst Hrs Hc.
  destruct (sstep_disjoint L ms mo ms' rs Hh HL Hst Hrs) as [H1 H2].
  eapply rz_silent1; [|exact Hc]. split.
  - intros []. exact H1.
  - intros e st Hss. exists tt. exact (H2 e st Hss).
Qed.

Lemma rzA_evt_disjoint : forall L (Q : machine_state -> Prop) ms mo T,
  evtA segs (acc_out L) Q ms -> m_halted mo = None -> incl (m_vm_lazy mo) L ->
  (forall ms', Q ms' -> realizes segs (mkCfg ms' mo) T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros L Q ms mo T (ms' & Hrun & HQ) Hh HL HK.
  induction Hrun as [ms|ms ms1 ms2 rs Hst Hrs Hrun IH].
  - apply HK. exact HQ.
  - eapply rzA_step_disjoint; eauto.
Qed.

Theorem rzA_evt : forall S N EB L (Q : machine_state -> Prop) ms mo T,
  evtA segs (acc_ok L S) Q ms -> m_halted mo = None -> LI S N EB mo -> m_vm_lazy mo = L ->
  (forall ms' mo', Q ms' -> magree mo mo' -> LI S N EB mo' -> m_halted mo' = None ->
     realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros S N EB L Q ms mo T (ms' & Hrun & HQ) Hh HLI HL HK. revert mo Hh HLI HL HK.
  induction Hrun as [ms|ms ms1 ms2 rs Hst Hrs Hrun IH]; intros mo Hh HLI HL HK.
  - apply HK; [exact HQ| apply magree_refl| exact HLI| exact Hh].
  - subst L. destruct (sstep_ok S N EB ms mo ms1 rs Hh HLI Hst Hrs) as (mo1 & Hag & HLI1 & Hh1 & Hss & Hinv).
    eapply rz_silent1.
    + split; [intros []; exact Hss| intros e st H; exists tt; exact (Hinv e st H)].
    + apply IH; [exact HQ| exact Hh1| exact HLI1| exact (magree_lazy _ _ Hag)|].
      intros ms' mo' HQ' Hag' HLI' Hh'. apply HK; auto. eapply magree_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cfg.
Variable cfg : SpuriousCfg.

Lemma node1_cfg_of_sstep_instr : forall ms mo ms' mo',
  ms_svc_pending ms = None ->
  sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo')) ->
  (forall e st, sstep segs (mkCfg ms mo) e st -> e = [] /\ st = SNext (mkCfg ms' mo')) ->
  node_ok_cfg cfg segs (mkCfg ms mo) unit (fun _ => []) (fun _ => mkCfg ms' mo').
Proof.
  intros ms mo ms' mo' Hsvc H1 H2. apply node_ok_cfg_lift.
  - split; [intros []; exact H1| intros e st H; exists tt; exact (H2 e st H)].
  - intros []. apply sstep_cfg_of_sstep_instr; [exact Hsvc| exact H1].
Qed.

Lemma rzA_step_disjoint_cfg : forall L ms mo ms' rs T,
  m_halted mo = None -> incl (m_vm_lazy mo) L ->
  mstepA segs ms ms' rs -> Forall (acc_out L) rs ->
  realizes_cfg cfg segs (mkCfg ms' mo) T -> realizes_cfg cfg segs (mkCfg ms mo) T.
Proof.
  intros L ms mo ms' rs T Hh HL Hst Hrs Hc.
  destruct (sstep_disjoint L ms mo ms' rs Hh HL Hst Hrs) as [H1 H2].
  eapply rz_silent1_cfg; [|exact Hc]. apply node1_cfg_of_sstep_instr; [exact (proj1 Hst)| exact H1| exact H2].
Qed.

Lemma rzA_evt_disjoint_cfg : forall L (Q : machine_state -> Prop) ms mo T,
  evtA segs (acc_out L) Q ms -> m_halted mo = None -> incl (m_vm_lazy mo) L ->
  (forall ms', Q ms' -> realizes_cfg cfg segs (mkCfg ms' mo) T) ->
  realizes_cfg cfg segs (mkCfg ms mo) T.
Proof.
  intros L Q ms mo T (ms' & Hrun & HQ) Hh HL HK.
  induction Hrun as [ms|ms ms1 ms2 rs Hst Hrs Hrun IH].
  - apply HK. exact HQ.
  - eapply rzA_step_disjoint_cfg; eauto.
Qed.

Theorem rzA_evt_cfg : forall S N EB L (Q : machine_state -> Prop) ms mo T,
  evtA segs (acc_ok L S) Q ms -> m_halted mo = None -> LI S N EB mo -> m_vm_lazy mo = L ->
  (forall ms' mo', Q ms' -> magree mo mo' -> LI S N EB mo' -> m_halted mo' = None ->
     realizes_cfg cfg segs (mkCfg ms' mo') T) ->
  realizes_cfg cfg segs (mkCfg ms mo) T.
Proof.
  intros S N EB L Q ms mo T (ms' & Hrun & HQ) Hh HLI HL HK. revert mo Hh HLI HL HK.
  induction Hrun as [ms|ms ms1 ms2 rs Hst Hrs Hrun IH]; intros mo Hh HLI HL HK.
  - apply HK; [exact HQ| apply magree_refl| exact HLI| exact Hh].
  - subst L. destruct (sstep_ok S N EB ms mo ms1 rs Hh HLI Hst Hrs) as (mo1 & Hag & HLI1 & Hh1 & Hss & Hinv).
    eapply rz_silent1_cfg.
    + apply node1_cfg_of_sstep_instr; [exact (proj1 Hst)| exact Hss| exact Hinv].
    + apply IH; [exact HQ| exact Hh1| exact HLI1| exact (magree_lazy _ _ Hag)|].
      intros ms' mo' HQ' Hag' HLI' Hh'. apply HK; auto. eapply magree_trans; eauto.
Qed.
End Cfg.

End WithSegs.
