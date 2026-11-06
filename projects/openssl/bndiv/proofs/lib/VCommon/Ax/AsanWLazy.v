(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import CatSim ShapeAlg ShapeAlgCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition no_lazy (model : Model) (lo hi : Z) : Prop :=
  forall p z, In p (m_vm_lazy model) -> lo <= z < hi ->
    ~ (bv_unsigned (fst p) <= z < bv_unsigned (fst p) + bv_unsigned (snd p)).

(* [comment removed for export] *)
Definition acc_ok (model : Model) (acc : list (word * nat)) : Prop :=
  Forall (fun r => bv_unsigned (fst r) + Z.of_nat (snd r) <= 2 ^ 64
                   /\ no_lazy model (bv_unsigned (fst r)) (bv_unsigned (fst r) + Z.of_nat (snd r))) acc.

(* [comment removed for export] *)
Lemma no_lazy_of_disj : forall model lo hi,
  (forall p, In p (m_vm_lazy model) ->
     bv_unsigned (fst p) + bv_unsigned (snd p) <= lo \/ hi <= bv_unsigned (fst p)) ->
  no_lazy model lo hi.
Proof. intros model lo hi H p z Hp Hz. destruct (H p Hp); lia. Qed.

Lemma no_lazy_sub : forall model lo hi lo' hi',
  no_lazy model lo hi -> lo <= lo' -> hi' <= hi -> no_lazy model lo' hi'.
Proof. intros model lo hi lo' hi' H H1 H2 p z Hp Hz. apply (H p z Hp). lia. Qed.

Lemma no_lazy_empty : forall model lo hi, hi <= lo -> no_lazy model lo hi.
Proof. intros model lo hi H p z Hp Hz. lia. Qed.

Lemma no_lazy_union : forall model lo mid hi,
  no_lazy model lo mid -> no_lazy model mid hi -> no_lazy model lo hi.
Proof.
  intros model lo mid hi H1 H2 p z Hp Hz. destruct (Z_lt_le_dec z mid).
  - apply (H1 p z Hp). lia.
  - apply (H2 p z Hp). lia.
Qed.

Lemma acc_ok_nil : forall model, acc_ok model [].
Proof. intros model. constructor. Qed.

Lemma acc_ok_cons : forall model (a : word) (n : nat) acc,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  no_lazy model (bv_unsigned a) (bv_unsigned a + Z.of_nat n) ->
  acc_ok model acc -> acc_ok model ((a, n) :: acc).
Proof. intros model a n acc H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.

Lemma acc_ok_app : forall model acc1 acc2,
  acc_ok model acc1 -> acc_ok model acc2 -> acc_ok model (acc1 ++ acc2).
Proof. intros model acc1 acc2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma acc_ok_one : forall model (a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  no_lazy model (bv_unsigned a) (bv_unsigned a + Z.of_nat n) ->
  acc_ok model [(a, n)].
Proof. intros. apply acc_ok_cons; [assumption | assumption | apply acc_ok_nil]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_lazy_above_atop : forall model lo hi,
  (forall p, In p (m_vm_lazy model) -> bv_unsigned (fst p) + bv_unsigned (snd p) <= alloc_top (m_vmmaps model)) ->
  alloc_top (m_vmmaps model) <= lo ->
  no_lazy model lo hi.
Proof.
  intros model lo hi H Hlo. apply no_lazy_of_disj. intros p Hp. left. specialize (H p Hp). lia.
Qed.

(* [comment removed for export] *)
Lemma no_lazy_in_reserved : forall model (segs : list Segment) (sg : Segment) lo hi,
  (forall p q, In p (m_vm_lazy model) -> In q (segments_reserved segs) ->
     bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
     \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p)) ->
  In sg segs ->
  bv_unsigned (fst (segment_reservation sg)) <= lo ->
  hi <= bv_unsigned (fst (segment_reservation sg)) + bv_unsigned (snd (segment_reservation sg)) ->
  no_lazy model lo hi.
Proof.
  intros model segs sg lo hi H Hin Hlo Hhi. apply no_lazy_of_disj. intros p Hp.
  assert (Hq : In (segment_reservation sg) (segments_reserved segs)) by (apply in_map; exact Hin).
  destruct (H p _ Hp Hq) as [E|E]; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Lemma no_lazy_in_segment : forall model (segs : list Segment) (sg : Segment) lo hi,
  (forall p q, In p (m_vm_lazy model) -> In q (segments_reserved segs) ->
     bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
     \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p)) ->
  In sg segs ->
  Z.of_N (seg_base sg) + Z.of_N (seg_size sg) < 2 ^ 64 - 4096 ->
  Z.of_N (seg_base sg) <= lo -> hi <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg) ->
  lo < hi ->
  no_lazy model lo hi.
Proof.
  intros model segs sg lo hi H Hin Hsz Hlo Hhi Hlh.
  apply (no_lazy_in_reserved model segs sg lo hi H Hin).
  - unfold segment_reservation, page_round_down_Z, page_size. cbn [fst].
    pose proof (N2Z.is_nonneg (seg_base sg)) as Hb.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [|change (bv_modulus 64) with (2 ^ 64)].
    + pose proof (Z.mul_div_le (Z.of_N (seg_base sg)) 4096 ltac:(lia)). lia.
    + pose proof (Z.mul_div_le (Z.of_N (seg_base sg)) 4096 ltac:(lia)).
      pose proof (Z.div_pos (Z.of_N (seg_base sg)) 4096 ltac:(lia) ltac:(lia)). lia.
  - unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size. cbn [fst snd].
    pose proof (N2Z.is_nonneg (seg_base sg)) as Hb. pose proof (N2Z.is_nonneg (seg_size sg)) as Hs.
    set (B := Z.of_N (seg_base sg)) in *. set (S := Z.of_N (seg_size sg)) in *.
    pose proof (Z.mul_div_le B 4096 ltac:(lia)) as D1.
    pose proof (Z.div_pos B 4096 ltac:(lia) ltac:(lia)) as D2.
    pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)) as D3.
    assert (D4 : B + S <= (B + S + 4096 - 1) / 4096 * 4096).
    { pose proof (Z.mod_pos_bound (B + S + 4096 - 1) 4096 ltac:(lia)).
      pose proof (Z.div_mod (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
    rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
    rewrite (bv_wrap_small 64 (B / 4096 * 4096)) by (change (bv_modulus 64) with (2 ^ 64); lia).
    rewrite (bv_wrap_small 64 ((B + S + 4096 - 1) / 4096 * 4096 - B / 4096 * 4096))
      by (change (bv_modulus 64) with (2 ^ 64); lia).
    lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_page_insert : forall p q pages, In p (page_insert q pages) -> In p pages \/ p = q.
Proof.
  intros p q pages H. unfold page_insert in H. destruct (page_mem q pages).
  - left; exact H.
  - destruct H as [<-|H]; [right; reflexivity | left; exact H].
Qed.

Lemma in_access_pages_acc : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages \/ exists i, 0 <= i < Z.of_nat n /\ p = page_base_of (base + i).
Proof.
  induction n as [|n IH]; intros base pages p H; cbn [access_pages_acc] in H.
  - left; exact H.
  - destruct (IH _ _ _ H) as [H1|(i & Hi & ->)].
    + destruct (in_page_insert _ _ _ H1) as [H2| ->]; [left; exact H2|].
      right. exists 0. split; [lia|]. rewrite Z.add_0_r. reflexivity.
    + right. exists (i + 1). split; [lia|]. f_equal. lia.
Qed.

Lemma in_accesses_pages : forall acc pages p,
  In p (accesses_pages acc pages) ->
  In p pages \/ exists a n i, In (a, n) acc /\ 0 <= i < Z.of_nat n /\ p = page_base_of (bv_unsigned a + i).
Proof.
  induction acc as [|[a n] acc IH]; intros pages p H; cbn [accesses_pages] in H.
  - left; exact H.
  - destruct (IH _ _ H) as [H1|(a' & n' & i & Hin & Hi & ->)].
    + destruct (in_access_pages_acc _ _ _ _ H1) as [H2|(i & Hi & ->)]; [left; exact H2|].
      right. exists a, n, i. split; [left; reflexivity | split; [exact Hi | reflexivity]].
    + right. exists a', n', i. split; [right; exact Hin | split; [exact Hi | reflexivity]].
Qed.

Lemma page_not_lazy : forall model (a : word) (n : nat) i,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  no_lazy model (bv_unsigned a) (bv_unsigned a + Z.of_nat n) ->
  0 <= i < Z.of_nat n ->
  page_in_ranges (page_base_of (bv_unsigned a + i)) (m_vm_lazy model) = false.
Proof.
  intros model a n i Hnw Hnl Hi. unfold page_in_ranges.
  apply Bool.not_true_iff_false. intros E. apply existsb_exists in E as (r & Hr & E).
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2 ^ 64) in Ha.
  set (x := bv_unsigned a + i) in *.
  assert (Hp : bv_unsigned (page_base_of x) = x / 4096 * 4096).
  { unfold page_base_of, page_size. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64).
    pose proof (Z.mul_div_le x 4096 ltac:(lia)). pose proof (Z.div_pos x 4096 ltac:(lia) ltac:(lia)). lia. }
  rewrite Hp in E1, E2. unfold page_size in E2.
  pose proof (Z.mul_div_le x 4096 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). pose proof (Z.div_mod x 4096 ltac:(lia)).
  apply (Hnl r x Hr); [unfold x; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma materialize_acc_ok : forall model acc,
  acc_ok model acc -> materialize_model_accesses model acc = Some model.
Proof.
  intros model acc Hok.
  assert (Hnew : newly_materialized_pages (m_vm_lazy model) (m_vm_materialized model) acc = []).
  { unfold newly_materialized_pages.
    assert (Hall : forall p, In p (accesses_pages acc []) ->
              page_in_ranges p (m_vm_lazy model) = false).
    { intros p Hp. destruct (in_accesses_pages acc [] p Hp) as [[]|(a & n & i & Hin & Hi & ->)].
      unfold acc_ok in Hok. rewrite Forall_forall in Hok. destruct (Hok _ Hin) as [Hnw Hnl]. cbn [fst snd] in Hnw, Hnl.
      exact (page_not_lazy model a n i Hnw Hnl Hi). }
    revert Hall. generalize (accesses_pages acc []) as L. intros L Hall.
    induction L as [|p ps IH]; [reflexivity|].
    cbn [List.filter]. rewrite (Hall p (or_introl eq_refl)). cbn [andb].
    apply IH. intros q Hq. apply Hall. right; exact Hq. }
  unfold materialize_model_accesses, materialize_accesses.
  rewrite Hnew.
  destruct model as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma account_step_acc : forall ms model ms' acc,
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  acc_ok model acc ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros ms model ms' acc Hs Hok. unfold mi_account_step. rewrite Hs. cbn [accessed_ranges access_value].
  rewrite (materialize_acc_ok model acc Hok). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_acc : forall ms model ms' acc,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  acc_ok model acc ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' acc Hh Hsvc Hs Hok.
  pose proof (account_step_acc ms model ms' acc Hs Hok) as Hacc.
  split.
  - intros []. apply sstep_cfg_instr; assumption.
  - intros e st Hss. inversion Hss; subst;
      try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : mi_account_step _ _ _ = _ |- _ =>
        rewrite Hacc in H1; first [ injection H1 as <- <-; exists tt; split; reflexivity | discriminate H1 ] end.
Qed.

Lemma rzc_acc : forall ms model ms' acc T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  acc_ok model acc ->
  realizes_cfg segs cfg (mkCfg ms' model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' acc T Hh Hsvc Hs Hok Hc.
  eapply rzc_silent1; [eapply node_instr_acc; eassumption | exact Hc].
Qed.

End Nodes.
