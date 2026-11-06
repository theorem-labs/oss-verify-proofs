(* The allocator's depot across the driver's own allocator calls, on the model path (lib/Reusable/YG00.v malloc /
   free, lib/Reusable/YG0k.v apost). The model puts the call's trace with one depot_put (YG00.v malloc, free) and no
   other step of malloc or free writes the depot, so on every model path the depot either stays or gains that trace
   once (YGwildCount.v depot_step). With a fixed trace (In trc (u_fix U), which the driver's malloc / free sites
   give as `In trc (as_universe B)`) the wild part of the depot does not grow: a depot with no wild trace keeps none.
   - dkeep m: m keeps the depot on every model path; proved for each allocator step malloc and free run besides
     depot_put (cache_alloc, sec_alloc, enqueue, maybe_drain and their steps);
   - malloc_depot / free_depot: the depot step of the call's trace;
   - malloc_wild_nil / free_wild_nil: a depot with no wild trace keeps none across a call with a fixed trace;
   - wild_room_loop: the loop entry's room (staged AD1w.v loop_L_x) from an empty wild part and r <= 4 calls;
   - link_wroom: the room of link's universe (lib/A/AD2l.v PcapB, ACejUniv.v Tfib_univ: 32 fixed traces, 4064
     wild) for LINK_CALLS_MAX calls of LINK_WILD_PER_CALL wild traces each. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0k YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2l LinkWildRoom.
Import ListNotations.
Local Open Scope Z_scope.

Definition dkeep {A : Type} (m : M A) : Prop := forall s, apost (m s) (fun r => st_depot (snd r) = st_depot s).

Lemma depot_put_ap : forall trc s, apost (depot_put trc s) (fun r => depot_step trc (st_depot s) (st_depot (snd r))).
Proof. intros trc s tr r H. exact (depot_put_step trc s tr r H). Qed.

Ltac dk_use H := eapply apost_mono; [|exact H]; intros [? ?] ?.

Ltac dk_leaf :=
  cbn [fst snd st_depot set_regions set_cache_inited set_cache set_chunks set_secs set_sec_arr set_sec_reserved
    set_qthread set_qglobal set_fs set_internal_inited set_nev] in *;
  first [reflexivity | congruence | (left; congruence)].

Ltac dk_base :=
  match goal with
  | |- apost (bind _ _ _) _ => apply apost_bind
  | |- apost (ret _ _) _ => apply apost_ret
  | |- apost (IRet _) _ => apply apost_leaf
  | |- apost (get _) _ => apply apost_get
  | |- apost (put _ _) _ => apply apost_put
  | |- apost (modify _ _) _ => apply apost_modify
  | |- apost (askz _ _) _ => apply apost_askz; intros ? _
  | |- apost (mcheck _ _ _) _ => apply apost_mcheck; intros _
  | |- apost (fail _ _) _ => apply apost_fail
  | |- apost (spin _ _) _ => apply apost_spin
  | |- apost ((if ?b then _ else _) _) _ => destruct b
  | |- apost (if ?b then _ else _) _ => destruct b
  | |- apost ((match ?x with _ => _ end) _) _ => destruct x
  | |- apost (match ?x with _ => _ end) _ => destruct x
  | |- _ => progress (cbv zeta; cbn [fst snd])
  end.

Ltac dk_prim := unfold get_region, set_region, get_pc, set_pc, tick, init_cache_if_needed.

Lemma ensure_free_array_dk : forall c need b, dkeep (ensure_free_array c need b).
Proof. intros c need b s. unfold ensure_free_array. dk_prim. repeat dk_base; dk_leaf. Qed.

Lemma map_more_user_dk : forall c need, dkeep (map_more_user c need).
Proof. intros c need s. unfold map_more_user. dk_prim. repeat dk_base; dk_leaf. Qed.

Ltac dk_step1 :=
  match goal with
  | |- apost (ensure_free_array ?c ?n ?b ?s) _ => dk_use (ensure_free_array_dk c n b s)
  | |- apost (map_more_user ?c ?n ?s) _ => dk_use (map_more_user_dk c n s)
  | |- _ => dk_base
  end.

Lemma populate_dk : forall c need, dkeep (populate c need).
Proof. intros c need s. unfold populate. dk_prim. repeat dk_step1; dk_leaf. Qed.

Ltac dk_step2 :=
  match goal with
  | |- apost (populate ?c ?n ?s) _ => dk_use (populate_dk c n s)
  | |- _ => dk_step1
  end.

Lemma get_from_allocator_dk : forall c n, dkeep (get_from_allocator c n).
Proof. intros c n s. unfold get_from_allocator. dk_prim. repeat dk_step2; dk_leaf. Qed.

Ltac dk_step3 :=
  match goal with
  | |- apost (get_from_allocator ?c ?n ?s) _ => dk_use (get_from_allocator_dk c n s)
  | |- _ => dk_step2
  end.

Lemma cache_alloc_dk : forall c, dkeep (cache_alloc c).
Proof. intros c s. unfold cache_alloc, refill_if_empty. dk_prim. repeat dk_step3; dk_leaf. Qed.

Lemma sec_alloc_dk : forall n, dkeep (sec_alloc n).
Proof. intros n s. unfold sec_alloc. repeat dk_base; dk_leaf. Qed.

Lemma return_to_allocator_dk : forall c offs, dkeep (return_to_allocator c offs).
Proof. intros c offs s. unfold return_to_allocator. dk_prim. repeat dk_step1; dk_leaf. Qed.

Ltac dk_step4 :=
  match goal with
  | |- apost (return_to_allocator ?c ?o ?s) _ => dk_use (return_to_allocator_dk c o s)
  | |- apost (cache_alloc ?c ?s) _ => dk_use (cache_alloc_dk c s)
  | |- apost (sec_alloc ?n ?s) _ => dk_use (sec_alloc_dk n s)
  | |- _ => dk_step3
  end.

Lemma cache_dealloc_dk : forall c off, dkeep (cache_dealloc c off).
Proof. intros c off s. unfold cache_dealloc. dk_prim. repeat dk_step4; dk_leaf. Qed.

Lemma sec_dealloc_dk : forall r, dkeep (sec_dealloc r).
Proof. intros r s. unfold sec_dealloc. repeat dk_base; dk_leaf. Qed.

Ltac dk_step5 :=
  match goal with
  | |- apost (cache_dealloc ?c ?o ?s) _ => dk_use (cache_dealloc_dk c o s)
  | |- apost (sec_dealloc ?r ?s) _ => dk_use (sec_dealloc_dk r s)
  | |- _ => dk_step4
  end.

Lemma recycle_chunk_dk : forall k, dkeep (recycle_chunk k).
Proof. intros k s. unfold recycle_chunk. repeat dk_step5; dk_leaf. Qed.

Lemma recycle_items_dk : forall f items, dkeep (recycle_items f items).
Proof.
  induction f as [|f IH]; intros [|k t] s; cbn [recycle_items].
  - apply apost_ret. reflexivity.
  - apply apost_fail.
  - apply apost_ret. reflexivity.
  - apply apost_bind. dk_use (recycle_chunk_dk k s). cbn [fst snd] in *.
    match goal with |- apost (recycle_items f t ?s1) _ => dk_use (IH t s1) end. dk_leaf.
Qed.

Lemma do_recycle_dk : forall f bs, dkeep (do_recycle f bs).
Proof.
  induction f as [|f IH]; intros [|b t] s; cbn [do_recycle].
  - apply apost_ret. reflexivity.
  - apply apost_fail.
  - apply apost_ret. reflexivity.
  - apply apost_bind. dk_use (recycle_items_dk 1100%nat (b_items b) s). cbn [fst snd] in *.
    apply apost_bind. match goal with |- apost (cache_dealloc _ _ ?s1) _ => dk_use (cache_dealloc_dk kBatchClass (b_self b) s1) end.
    cbn [fst snd] in *.
    match goal with |- apost (do_recycle f t ?s1) _ => dk_use (IH t s1) end. dk_leaf.
Qed.

Ltac dk_step6 :=
  match goal with
  | |- apost (do_recycle ?f ?b ?s) _ => dk_use (do_recycle_dk f b s)
  | |- _ => dk_step5
  end.

Lemma enqueue_dk : forall k, dkeep (enqueue k).
Proof. intros k s. unfold enqueue. repeat dk_step6; dk_leaf. Qed.

Lemma maybe_drain_dk : dkeep maybe_drain.
Proof. intros s. unfold maybe_drain. repeat dk_step6; dk_leaf. Qed.

Ltac dk_step7 :=
  match goal with
  | |- apost (enqueue ?k ?s) _ => dk_use (enqueue_dk k s)
  | |- apost (maybe_drain ?s) _ => dk_use (maybe_drain_dk s)
  | |- apost (depot_put ?t ?s) _ => dk_use (depot_put_ap t s)
  | |- _ => dk_step6
  end.

Ltac dk_leaf_step :=
  cbn [fst snd st_depot set_regions set_cache_inited set_cache set_chunks set_secs set_sec_arr set_sec_reserved
    set_qthread set_qglobal set_fs set_internal_inited set_nev] in *;
  first [ (left; congruence)
        | match goal with H : depot_step ?t ?a ?b |- depot_step ?t ?c ?d =>
            replace c with a by congruence; replace d with b by congruence; exact H end ].

Lemma malloc_depot : forall n trc S, apost (malloc n trc S) (fun r => depot_step trc (st_depot S) (st_depot (snd r))).
Proof. intros n trc S. unfold malloc. dk_prim. repeat dk_step7; dk_leaf_step. Qed.

Lemma free_depot : forall p trc S, apost (free p trc S) (fun r => depot_step trc (st_depot S) (st_depot (snd r))).
Proof. intros p trc S. unfold free. dk_prim. repeat dk_step7; dk_leaf_step. Qed.

Lemma wild_nil_step : forall U tr d d', depot_step tr d d' -> In tr (u_fix U) -> wild_part U d = [] -> wild_part U d' = [].
Proof.
  intros U tr d d' [-> | [-> _]] Hf Hw; [exact Hw|].
  rewrite wild_part_app, Hw, wild_part_one. apply mem_trace_In in Hf. rewrite Hf. reflexivity.
Qed.

Lemma malloc_wild_nil : forall U n trc S tr (p : sptr) S', In trc (u_fix U) -> apath (malloc n trc S) tr (p, S') ->
  wild_part U (st_depot S) = [] -> wild_part U (st_depot S') = [].
Proof.
  intros U n trc S tr p S' Hf Hy Hw.
  exact (wild_nil_step U trc _ _ (apost_apath _ _ _ _ (malloc_depot n trc S) Hy) Hf Hw).
Qed.

Lemma free_wild_nil : forall U (p : sptr) trc S tr S', In trc (u_fix U) -> apath (free p trc S) tr (tt, S') ->
  wild_part U (st_depot S) = [] -> wild_part U (st_depot S') = [].
Proof.
  intros U p trc S tr S' Hf Hy Hw.
  exact (wild_nil_step U trc _ _ (apost_apath _ _ _ _ (free_depot p trc S) Hy) Hf Hw).
Qed.

Lemma wild_room_loop : forall U d (r : nat), wild_part U d = [] -> (r <= LINK_CALLS_MAX)%nat ->
  (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax U)%nat ->
  (length (wild_part U d) + LINK_WILD_PER_CALL * r <= u_wmax U)%nat.
Proof. intros U d r Hw Hr Hroom. rewrite Hw. cbn [length]. unfold LINK_CALLS_MAX, LINK_WILD_PER_CALL in *. nia. Qed.

Lemma link_wroom : (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax (YG0f.as_universe PcapB))%nat.
Proof. apply link_wild_room_fits; [vm_compute; reflexivity | reflexivity]. Qed.
