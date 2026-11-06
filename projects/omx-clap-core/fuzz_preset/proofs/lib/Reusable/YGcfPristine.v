(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30 (free_cf's size test, Quarantine::Put): free_tail_cf takes free_cf's size test (definition); yp_free_tail covers the recycle side (yp_recycle_chunk); yp_free_tail_nodrain and free_cf_keeps_pristine_norecycle take the enqueue side's premise (STATEMENT CHANGES; no consumer outside this file); pristine_free_norecycle_cf keeps its statement and derives that premise from Wf_cf. *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf), cgif's "pristine primary
   classes" lemmas (YG0k.v: pristine_malloc_sec :395, pristine_free_null :404, pristine_free_norecycle :418)
   ported to the cf model (YG00cf.v: malloc_cf, free_cf with maybe_drain_cf). prim_pristine_except and
   pristine_class are YG0k.v's (:25-28), not redefined. Every statement is over EVERY apath (no gflag).
   - malloc_cf touches only the class it allocates from: its class-full arm (errb_report_cf, set_exh_cf)
     writes st_secs and the class's own sentinel hole, and kBatchClass keeps cgif's populate.
     quar_bytes is unchanged by every malloc_cf.
   - free_cf touches kBatchClass (enqueue's batch) and, through the drain (maybe_drain_cf -> do_recycle ->
     recycle_chunk -> cache_dealloc), the class of every PRIMARY chunk it recycles. recycle_chunk recycles
     only a chunk that its mcheck finds in st_chunks, so the drain touches only classes of chunks of the
     entry state. Three premises close it:
       (a) free_cf_keeps_pristine_chk: every primary chunk of st_chunks S is of a class in kBatchClass :: cs;
       (b) free_cf_keeps_pristine_except: Wf_cf U S. Under Wf_cf a primary chunk of class c lies below
           rg_alloc_user (reg S c) (wrc_elems), so a pristine class (rg_alloc_user = 0) has no chunk, and
           (a) follows from prim_pristine_except S cs itself. No quantity premise; any p.
       (c) free_cf_keeps_pristine_norecycle / pristine_free_norecycle_cf: cgif's quantity premise
           quar_bytes S + ck_n k + kBatchBytes <= kQuarantineMax, under which the drain recycles nothing.
   - malloc_refusal_sec_cf / malloc_refusal_prim_cf: cgif's malloc_refusal_sec / malloc_refusal_prim (YG0k.v:16, :38)
     for malloc_cf, with Wf_cf for Wf (section "refusal" at the end).
   Nothing here is a function's proof (rule 24). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0k YGcfNames YG00cf YG01cf YG03cf YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ================================================================ frames *)
Lemma yp_and {A} (t : itree astate A) (P Q : A -> Prop) : apost t P -> apost t Q -> apost t (fun a => P a /\ Q a).
Proof. intros HP HQ tr a Hy. split; [exact (HP tr a Hy) | exact (HQ tr a Hy)]. Qed.

Lemma yp_znth_zupd {X} : forall (d : X) i j v l, 1 <= j -> i <> j -> znth d j (zupd i v l) = znth d j l.
Proof. intros d i j v l Hj Hij. unfold znth, zupd. apply nth_lupd_other. lia. Qed.

(* Every class in 1..31 outside T keeps its region and its cache's chunks. *)
Definition ypK (T : Z -> Prop) (s y : astate) : Prop :=
  forall c, 1 <= c <= 31 -> ~ T c -> reg y c = reg s c /\ pc_chunks (cache y c) = pc_chunks (cache s c).

Lemma yp_refl : forall T s, ypK T s s.
Proof. intros T s c _ _. split; reflexivity. Qed.

Lemma yp_trans : forall T s1 s2 s3, ypK T s1 s2 -> ypK T s2 s3 -> ypK T s1 s3.
Proof.
  intros T s1 s2 s3 H1 H2 c Hc Hn. destruct (H1 c Hc Hn) as [A1 B1]. destruct (H2 c Hc Hn) as [A2 B2].
  split; congruence.
Qed.

Lemma yp_mono : forall (T T' : Z -> Prop) s y, (forall c, T c -> T' c) -> ypK T s y -> ypK T' s y.
Proof. intros T T' s y HT H c Hc Hn. apply H; [exact Hc | intros Ht; exact (Hn (HT c Ht))]. Qed.

Lemma yp_mono_range : forall (T T' : Z -> Prop) s y, (forall c, 1 <= c <= 31 -> T c -> T' c) -> ypK T s y -> ypK T' s y.
Proof. intros T T' s y HT H c Hc Hn. apply H; [exact Hc | intros Ht; exact (Hn (HT c Hc Ht))]. Qed.

Lemma yp_same : forall T s y, st_regions y = st_regions s -> st_cache y = st_cache s -> ypK T s y.
Proof. intros T s y E1 E2 c _ _. unfold reg, cache. rewrite E1, E2. split; reflexivity. Qed.

Lemma yp_upd_reg : forall (T : Z -> Prop) c r s, T c -> ypK T s (upd_reg c r s).
Proof.
  intros T c r s Hc c' Hc' Hn. split; [|reflexivity].
  unfold reg, upd_reg. cbn [st_regions set_regions].
  apply yp_znth_zupd; [lia | intros E; apply Hn; rewrite <- E; exact Hc].
Qed.

Lemma yp_upd_pc : forall (T : Z -> Prop) c p s, T c -> ypK T s (upd_pc c p s).
Proof.
  intros T c p s Hc c' Hc' Hn. split; [reflexivity|].
  unfold cache, upd_pc. cbn [st_cache set_cache].
  rewrite yp_znth_zupd; [reflexivity | lia | intros E; apply Hn; rewrite <- E; exact Hc].
Qed.

Lemma yp_init : forall T s, ypK T s (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Proof. intros T s c Hc _. split; [reflexivity|]. rewrite cache_after_init by lia. reflexivity. Qed.

Lemma yp_of_frame : forall (T : Z -> Prop) c s y, T c -> FRAME c s y -> ypK T s y.
Proof. intros T c s y Hc [F _] c' Hc' Hn. apply F; [exact Hc' | intros E; apply Hn; rewrite E; exact Hc]. Qed.

Lemma yp_sameq_refl : forall s, SAMEQ s s.
Proof. intros s. unfold SAMEQ. repeat split; reflexivity. Qed.

Lemma yp_of_sameq : forall T s y, SAMEQ s y -> ypK T s y.
Proof. intros T s y (A & B & _ & _). apply yp_same; assumption. Qed.

(* regions, caches, chunks and both queues unchanged *)
Definition ypE5 (s y : astate) : Prop :=
  st_regions y = st_regions s /\ st_cache y = st_cache s /\ st_chunks y = st_chunks s /\
  st_qthread y = st_qthread s /\ st_qglobal y = st_qglobal s.

Lemma yp_of_e5 : forall T s y, ypE5 s y -> ypK T s y.
Proof. intros T s y (A & B & _). apply yp_same; assumption. Qed.

Lemma yp_pristine : forall cs s y, ypK (fun c => In c cs) s y -> prim_pristine_except s cs -> prim_pristine_except y cs.
Proof.
  intros cs s y K HP c Hc Hn. destruct (K c Hc Hn) as [E1 E2]. unfold pristine_class. rewrite E1, E2.
  exact (HP c Hc Hn).
Qed.

Lemma yp_pristine_cons : forall a cs s, prim_pristine_except s cs -> prim_pristine_except s (a :: cs).
Proof. intros a cs s HP c Hc Hn. apply HP; [exact Hc | intros H; apply Hn; right; exact H]. Qed.

Lemma yp_kb_nonneg : 0 <= kBatchClass.
Proof. unfold kBatchClass. lia. Qed.

(* ================================================================ cgif's steps, any class *)
Lemma yp_ensure_free_array : forall (T : Z -> Prop) c need b s, T c ->
  apost (ensure_free_array c need b s) (fun r => ypK T s (snd r)).
Proof.
  intros T c need b s Hc. unfold ensure_free_array.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_if; intros _; [apply apost_ret; apply yp_refl|].
  apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
  apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
  apply apost_if; intros _.
  - apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd]. apply yp_upd_reg. exact Hc.
  - apply apost_bind.
    apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd];
      (apply apost_if; intros _; [apply apost_spin | apply apost_ret]); cbn [snd];
      try (apply yp_upd_reg; exact Hc); apply yp_refl.
Qed.

Lemma yp_return_to_allocator : forall (T : Z -> Prop) c offs s, T c ->
  apost (return_to_allocator c offs s) (fun r => ypK T s (snd r)).
Proof.
  intros T c offs s Hc. unfold return_to_allocator.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_bind. eapply apost_mono; [|apply (yp_ensure_free_array T c _ true s Hc)].
  intros [u1 s1] F1. cbn [fst snd] in F1 |- *.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_set_region. cbn [snd]. exact (yp_trans _ _ _ _ F1 (yp_upd_reg T c _ s1 Hc)).
Qed.

Lemma yp_cache_dealloc : forall (T : Z -> Prop) c off s, T c ->
  apost (cache_dealloc c off s) (fun r => ypK T s (snd r)).
Proof.
  intros T c off s Hc. unfold cache_dealloc, init_cache_if_needed.
  apply apost_bind. apply apost_bind. apply apost_get. cbn [fst snd].
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _; [apply apost_ret; apply yp_refl | apply apost_put; apply yp_init]. }
  intros [[] s1] F1. cbn [fst snd] in F1 |- *.
  apply apost_bind. apply apost_get_pc. cbn [fst snd].
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _.
      - apply apost_bind. eapply apost_mono; [|apply (yp_return_to_allocator T c _ s1 Hc)].
        intros [u2 s2] F2. cbn [fst snd] in F2 |- *.
        apply apost_set_pc. cbn [snd]. exact (yp_trans _ _ _ _ (yp_trans _ _ _ _ F1 F2) (yp_upd_pc T c _ s2 Hc)).
      - apply apost_ret. cbn [snd]. exact F1. }
  intros [[] s3] F3. cbn [fst snd] in F3 |- *.
  apply apost_bind. apply apost_get_pc. cbn [fst snd].
  apply apost_set_pc. cbn [snd]. exact (yp_trans _ _ _ _ F3 (yp_upd_pc T c _ s3 Hc)).
Qed.

Lemma yp_cache_alloc : forall (T : Z -> Prop) c s, 0 <= c -> T c ->
  apost (cache_alloc c s) (fun r => ypK T s (snd r)).
Proof.
  intros T c s Hc0 Hc. unfold cache_alloc, init_cache_if_needed, refill_if_empty.
  apply apost_bind. apply apost_bind. apply apost_get. cbn [fst snd].
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _; [apply apost_ret; apply yp_refl | apply apost_put; apply yp_init]. }
  intros [[] s1] F1. cbn [fst snd] in F1 |- *.
  apply apost_bind. apply apost_bind. apply apost_get_pc. cbn [fst snd].
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ destruct (pc_chunks (cache s1 c)).
      - apply apost_bind. eapply apost_mono; [|apply (get_from_allocator_frame c _ s1 Hc0)].
        intros [got s2] G2. cbn [fst snd] in G2 |- *.
        pose proof (yp_trans _ _ _ _ F1 (yp_of_frame T c _ _ Hc G2)) as F2.
        destruct got as [tops|].
        + apply apost_set_pc. cbn [snd]. exact (yp_trans _ _ _ _ F2 (yp_upd_pc T c _ s2 Hc)).
        + apply apost_ret. cbn [snd]. exact F2.
      - apply apost_ret. cbn [snd]. exact F1. }
  intros [[] s2] F2. cbn [fst snd] in F2 |- *.
  apply apost_bind. apply apost_get_pc. cbn [fst snd].
  destruct (pc_chunks (cache s2 c)); [apply apost_ret; cbn [snd]; exact F2|].
  apply apost_bind. apply apost_set_pc. cbn [fst snd]. apply apost_ret. cbn [snd].
  exact (yp_trans _ _ _ _ F2 (yp_upd_pc T c _ s2 Hc)).
Qed.

Lemma yp_sec_dealloc : forall (T : Z -> Prop) r s, apost (sec_dealloc r s) (fun x => ypK T s (snd x)).
Proof.
  intros T r s. unfold sec_dealloc.
  apply apost_bind. apply apost_get. cbn [fst snd].
  destruct (nth_error (st_secs s) r) as [sm|]; destruct (index_of (st_sec_arr s) r 0%nat) as [i|];
    cbn [fst snd]; try apply apost_fail.
  apply apost_bind.
  eapply apost_mono with (Q := fun x => snd x = s).
  2:{ apply apost_if; intros _.
      - apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
        apply apost_if; intros _; [apply apost_ret; cbn [snd]; reflexivity | apply apost_spin].
      - apply apost_ret. cbn [snd]. reflexivity. }
  intros [[] s1] E1. cbn [fst snd] in E1 |- *. subst s1.
  apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
  apply apost_modify. cbn [snd]. apply yp_same; reflexivity.
Qed.

Lemma yp_depot_put : forall trc s, apost (depot_put trc s) (fun r => ypE5 s (snd r)).
Proof.
  intros trc s. unfold depot_put.
  apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
  apply apost_if; intros _; [apply apost_ret; cbn [snd]; unfold ypE5; repeat split; reflexivity|].
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
  apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
  apply apost_put. cbn [snd]. unfold ypE5. repeat split; reflexivity.
Qed.

(* ================================================================ malloc_cf *)
Section CFM.
Context {ci : CfImg}.

Lemma yp_errb_report : forall T c s, apost (errb_report_cf c s) (fun r => ypK T s (snd r)).
Proof.
  intros T c s.
  eapply apost_mono; [|exact (apost_of_rpost _ true (fun r => ER s (snd r)) (er_errb_report_cf c s true))].
  intros [u y] H. cbn [snd] in H |- *. unfold ER in H. destruct H as (E1 & E2 & _). apply yp_same; assumption.
Qed.

Lemma yp_set_exh : forall (T : Z -> Prop) c s, T c -> apost (set_exh_cf c s) (fun r => ypK T s (snd r)).
Proof.
  intros T c s Hc. unfold set_exh_cf.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_set_region. cbn [snd]. apply yp_upd_reg. exact Hc.
Qed.

Lemma yp_clear_exh : forall (T : Z -> Prop) c s, T c -> apost (clear_exh_cf c s) (fun r => ypK T s (snd r)).
Proof.
  intros T c s Hc. unfold clear_exh_cf.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_set_region. cbn [snd]. apply yp_upd_reg. exact Hc.
Qed.

Lemma yp_map_more_user_cf : forall (T : Z -> Prop) c need s, T c ->
  apost (map_more_user_cf c need s) (fun r => ypK T s (snd r)).
Proof.
  intros T c need s Hc. unfold map_more_user_cf.
  apply apost_if; intros Hb.
  - apply Z.eqb_eq in Hb.
    eapply apost_mono; [|apply map_more_user_frame; rewrite Hb; exact yp_kb_nonneg].
    intros r F. exact (yp_of_frame T c s (snd r) Hc F).
  - apply apost_bind. apply apost_get_region. cbn [fst snd].
    apply apost_if; intros _; [|apply apost_ret; apply yp_refl].
    apply apost_if; intros _.
    + apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
      apply apost_if; intros _.
      * apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd].
        apply yp_upd_reg. exact Hc.
      * apply apost_bind.
        apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd];
          apply apost_ret; cbn [snd]; [apply yp_upd_reg; exact Hc | apply yp_refl].
    + apply apost_bind. eapply apost_mono; [|apply (yp_errb_report T c s)].
      intros [u1 s1] F1. cbn [fst snd] in F1 |- *.
      apply apost_bind. eapply apost_mono; [|apply (yp_set_exh T c s1 Hc)].
      intros [u2 s2] F2. cbn [fst snd] in F2 |- *.
      apply apost_ret. cbn [snd]. exact (yp_trans _ _ _ _ F1 F2).
Qed.

Lemma yp_populate_cf : forall (T : Z -> Prop) c need s, T c ->
  apost (populate_cf c need s) (fun r => ypK T s (snd r)).
Proof.
  intros T c need s Hc. unfold populate_cf.
  apply apost_if; intros Hb.
  - apply Z.eqb_eq in Hb.
    eapply apost_mono; [|apply populate_frame; rewrite Hb; exact yp_kb_nonneg].
    intros r F. exact (yp_of_frame T c s (snd r) Hc F).
  - apply apost_bind. eapply apost_mono; [|apply (yp_map_more_user_cf T c need s Hc)].
    intros [ok s1] F1. cbn [fst snd] in F1 |- *.
    apply apost_if; intros _; [apply apost_ret; cbn [snd]; exact F1|].
    apply apost_bind. apply apost_get_region. cbn [fst snd].
    apply apost_bind. eapply apost_mono; [|apply (yp_ensure_free_array T c _ false s1 Hc)].
    intros [ok2 s2] F2. cbn [fst snd] in F2 |- *.
    apply apost_if; intros _; [apply apost_ret; cbn [snd]; exact (yp_trans _ _ _ _ F1 F2)|].
    apply apost_bind. apply apost_get_region. cbn [fst snd].
    apply apost_bind. apply apost_set_region. cbn [fst snd].
    apply apost_bind. eapply apost_mono; [|apply (yp_clear_exh T c _ Hc)].
    intros [u3 s3] F3. cbn [fst snd] in F3 |- *.
    apply apost_ret. cbn [snd].
    exact (yp_trans _ _ _ _ (yp_trans _ _ _ _ F1 F2) (yp_trans _ _ _ _ (yp_upd_reg T c _ s2 Hc) F3)).
Qed.

Lemma yp_gfa_cf : forall (T : Z -> Prop) c n s, T c ->
  apost (get_from_allocator_cf c n s) (fun r => ypK T s (snd r)).
Proof.
  intros T c n s Hc. unfold get_from_allocator_cf.
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _; [apply (yp_populate_cf T c _ s Hc) | apply apost_ret; apply yp_refl]. }
  intros [ok s1] F1. cbn [fst snd] in F1 |- *.
  apply apost_if; intros _; [apply apost_ret; cbn [snd]; exact F1|].
  apply apost_bind. apply apost_get_region. cbn [fst snd].
  apply apost_if; intros _; [apply apost_ret; cbn [snd]; exact F1|].
  destruct (fa_pop_n _ _ _ _ _) as [[tops rest]|]; [|apply apost_fail].
  apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd].
  exact (yp_trans _ _ _ _ F1 (yp_upd_reg T c _ s1 Hc)).
Qed.

Lemma yp_cache_alloc_cf : forall (T : Z -> Prop) c s, T c ->
  apost (cache_alloc_cf c s) (fun r => ypK T s (snd r)).
Proof.
  intros T c s Hc. unfold cache_alloc_cf, init_cache_if_needed, refill_if_empty_cf.
  apply apost_bind. apply apost_bind. apply apost_get. cbn [fst snd].
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _; [apply apost_ret; apply yp_refl | apply apost_put; apply yp_init]. }
  intros [[] s1] F1. cbn [fst snd] in F1 |- *.
  apply apost_bind. apply apost_bind. apply apost_get_pc. cbn [fst snd].
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ destruct (pc_chunks (cache s1 c)).
      - apply apost_bind. eapply apost_mono; [|apply (yp_gfa_cf T c _ s1 Hc)].
        intros [got s2] G2. cbn [fst snd] in G2 |- *.
        pose proof (yp_trans _ _ _ _ F1 G2) as F2.
        destruct got as [tops|].
        + apply apost_set_pc. cbn [snd]. exact (yp_trans _ _ _ _ F2 (yp_upd_pc T c _ s2 Hc)).
        + apply apost_ret. cbn [snd]. exact F2.
      - apply apost_ret. cbn [snd]. exact F1. }
  intros [[] s2] F2. cbn [fst snd] in F2 |- *.
  apply apost_bind. apply apost_get_pc. cbn [fst snd].
  destruct (pc_chunks (cache s2 c)); [apply apost_ret; cbn [snd]; exact F2|].
  apply apost_bind. apply apost_set_pc. cbn [fst snd]. apply apost_ret. cbn [snd].
  exact (yp_trans _ _ _ _ F2 (yp_upd_pc T c _ s2 Hc)).
Qed.

(* malloc_cf touches at most its own class, and only when the request is primary. *)
Lemma yp_malloc_cf : forall (T : Z -> Prop) n trc s, (from_primary n = true -> T (chunk_class n)) ->
  apost (malloc_cf n trc s) (fun r => ypK T s (snd r)).
Proof.
  intros T n trc s HT. unfold malloc_cf.
  apply apost_bind. apply apost_tick. cbn [fst snd].
  assert (F0 : ypK T s (set_nev (st_nev s + 1) s)) by (apply yp_same; reflexivity).
  apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ destruct (from_primary n) eqn:Hp.
      - apply apost_bind. eapply apost_mono; [|apply (yp_cache_alloc_cf T (chunk_class n) _ (HT eq_refl))].
        intros [o s1] F1. cbn [fst snd] in F1 |- *. apply apost_ret. cbn [snd]. exact (yp_trans _ _ _ _ F0 F1).
      - eapply apost_mono; [|apply (sec_alloc_sameq n _ _ (yp_sameq_refl _))].
        intros [ob s1] H1. cbn [snd] in H1 |- *. exact (yp_trans _ _ _ _ F0 (yp_of_sameq T _ _ H1)). }
  intros [ob s1] F1. cbn [fst snd] in F1 |- *.
  destruct ob as [beg|]; [|apply apost_ret; cbn [snd]; exact F1].
  apply apost_bind. eapply apost_mono; [|apply yp_depot_put]. intros [[] s2] E2. cbn [fst snd] in E2 |- *.
  pose proof (yp_trans _ _ _ _ F1 (yp_of_e5 T _ _ E2)) as F2. clear F1 E2.
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypK T s (snd r)).
  2:{ apply apost_if; intros _.
      - apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
        apply apost_if; intros _; [apply apost_ret; cbn [snd]; exact F2 | apply apost_spin].
      - apply apost_ret. cbn [snd]. exact F2. }
  intros [[] s3] F3. cbn [fst snd] in F3 |- *.
  apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret. cbn [snd].
  eapply yp_trans; [exact F3|]. apply yp_same; reflexivity.
Qed.

(* malloc_cf never touches the quarantine. *)
Theorem malloc_cf_keeps_quar_bytes : forall n trc S evs r S',
  apath (malloc_cf n trc S) evs (r, S') -> quar_bytes S' = quar_bytes S.
Proof.
  intros n trc S evs r S' Hy.
  pose proof (apost_apath _ _ _ _ (apost_of_rpost _ true (fun x => MQ S (snd x)) (malloc_cf_mq n trc S true)) Hy) as HM.
  cbn [snd] in HM. unfold MQ in HM. destruct HM as (Q1 & Q2 & _).
  unfold quar_bytes. rewrite Q1, Q2. reflexivity.
Qed.

(* The general form: a primary request's class must be among the classes already given up. *)
Theorem malloc_cf_keeps_pristine_gen : forall n trc S evs r S' cs,
  (from_primary n = true -> In (chunk_class n) cs) ->
  apath (malloc_cf n trc S) evs (r, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' cs /\ quar_bytes S' = quar_bytes S.
Proof.
  intros n trc S evs r S' cs Hcs Hy HP.
  pose proof (apost_apath _ _ _ _ (yp_malloc_cf (fun c => In c cs) n trc S Hcs) Hy) as K. cbn [snd] in K.
  split; [exact (yp_pristine cs S S' K HP) | exact (malloc_cf_keeps_quar_bytes n trc S evs r S' Hy)].
Qed.

(* cgif's pristine_malloc_sec (YG0k.v:395), for malloc_cf: no In kBatchClass cs needed. *)
Theorem malloc_cf_sec_keeps_pristine : forall n trc S evs r S' cs,
  from_primary n = false -> apath (malloc_cf n trc S) evs (r, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' cs /\ quar_bytes S' = quar_bytes S.
Proof. intros n trc S evs r S' cs Hp. apply malloc_cf_keeps_pristine_gen. intros H. congruence. Qed.

Theorem malloc_cf_keeps_pristine_except : forall n trc S evs r S' cs,
  (from_primary n = false \/ chunk_class n = kBatchClass) -> In kBatchClass cs ->
  apath (malloc_cf n trc S) evs (r, S') -> prim_pristine_except S cs -> prim_pristine_except S' cs.
Proof.
  intros n trc S evs r S' cs Hn Hb Hy HP.
  refine (proj1 (malloc_cf_keeps_pristine_gen n trc S evs r S' cs _ Hy HP)).
  intros Hp. destruct Hn as [Hn|Hn]; [congruence | rewrite Hn; exact Hb].
Qed.

End CFM.

(* ================================================================ free_cf *)
(* every primary chunk of a chunk list is of a class in T *)
Definition ypCL (T : Z -> Prop) (l : list chunk) : Prop :=
  forall k off, In k l -> ck_beg k = PPrim off -> T (prim_class off).
Definition ypC (T : Z -> Prop) (s : astate) : Prop := ypCL T (st_chunks s).
(* the chunk list only shrinks *)
Definition ypI (s y : astate) : Prop := forall k, In k (st_chunks y) -> In k (st_chunks s).

Lemma yp_C_inc : forall T s y, ypC T s -> ypI s y -> ypC T y.
Proof. intros T s y HC HI k off Hk Hb. exact (HC k off (HI k Hk) Hb). Qed.

Lemma yp_upd_chunk_in : forall l k x, In x (upd_chunk l k) -> x = k \/ In x l.
Proof.
  induction l as [|k0 t IH]; intros k x H; cbn [upd_chunk] in H.
  - destruct H as [<-|[]]. left. reflexivity.
  - destruct (sptr_eqb (ck_beg k0) (ck_beg k)).
    + destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
    + destruct H as [<-|H]; [right; left; reflexivity|].
      destruct (IH k x H) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma yp_CL_upd : forall T l k0 st, ypCL T l -> In k0 l -> ypCL T (upd_chunk l (mkChunk (ck_beg k0) (ck_req k0) st)).
Proof.
  intros T l k0 st H Hk x off Hx Hb. destruct (yp_upd_chunk_in _ _ _ Hx) as [E|Hx'].
  - subst x. cbn [ck_beg] in Hb. exact (H k0 off Hk Hb).
  - exact (H x off Hx' Hb).
Qed.

Lemma yp_enqueue : forall k x, apost (enqueue k x) (fun r =>
  ypK (fun c => c = kBatchClass) x (snd r) /\ st_chunks (snd r) = st_chunks x /\ st_qglobal (snd r) = st_qglobal x /\
  qc_bytes (st_qthread x) + ck_n k <= qc_bytes (st_qthread (snd r)) <= qc_bytes (st_qthread x) + ck_n k + kBatchBytes).
Proof.
  intros k x. unfold enqueue.
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypK (fun c => c = kBatchClass) x (snd r) /\ CQ x (snd r)).
  2:{ apply apost_if; intros _.
      - apply apost_bind.
        eapply apost_mono; [|apply yp_and;
          [apply (yp_cache_alloc (fun c => c = kBatchClass) kBatchClass x yp_kb_nonneg eq_refl)
          | apply (apost_of_rpost _ true (fun r => CQ x (snd r)) (cq_cache_alloc kBatchClass x true))]].
        intros [ob s4] [F4 C4]. cbn [fst snd] in F4, C4 |- *.
        destruct ob as [off|]; [apply apost_ret; cbn [snd]; split; assumption | apply apost_spin].
      - apply apost_ret. cbn [snd]. split; [apply yp_refl | unfold CQ; repeat split; reflexivity]. }
  intros [nb s4] [F4 C4]. cbn [fst snd] in F4, C4 |- *. unfold CQ in C4. destruct C4 as (C1 & C2 & C3).
  apply apost_modify. cbn [snd].
  split; [eapply yp_trans; [exact F4 | apply yp_same; reflexivity]|].
  cbn [st_chunks st_qglobal st_qthread set_qthread]. split; [exact C1|]. split; [exact C3|].
  rewrite C2. unfold qc_push. destruct nb; cbn [qc_bytes]; unfold kBatchBytes; lia.
Qed.

Lemma yp_recycle_chunk : forall T k s, ypC T s ->
  apost (recycle_chunk k s) (fun r => ypK T s (snd r) /\ ypI s (snd r)).
Proof.
  intros T k s HC. unfold recycle_chunk.
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_bind. apply apost_mcheck. intros Hm. cbn [fst snd].
  apply (proj1 (mem_chunk_spec _ _)) in Hm.
  apply apost_bind. apply apost_put. cbn [fst snd].
  assert (F1 : ypK T s (set_chunks (del_chunk (st_chunks s) (ck_beg k)) s)) by (apply yp_same; reflexivity).
  assert (I1 : ypI s (set_chunks (del_chunk (st_chunks s) (ck_beg k)) s)).
  { intros k' Hk'. cbn [st_chunks set_chunks] in Hk'. exact (del_chunk_incl _ _ _ Hk'). }
  revert F1 I1. generalize (set_chunks (del_chunk (st_chunks s) (ck_beg k)) s) as s1. intros s1 F1 I1.
  destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [fst snd]; try apply apost_fail.
  - eapply apost_mono; [|apply yp_and;
      [apply (yp_cache_dealloc T (prim_class off) off s1 (HC k off Hm Eb))
      | apply (apost_of_rpost _ true (fun x => CQ s1 (snd x)) (cq_cache_dealloc (prim_class off) off s1 true))]].
    intros [u2 s2] [F2 C2]. cbn [snd] in F2, C2 |- *. unfold CQ in C2. destruct C2 as (C2 & _ & _).
    split; [exact (yp_trans _ _ _ _ F1 F2) | intros k' Hk'; apply I1; rewrite <- C2; exact Hk'].
  - eapply apost_mono; [|apply yp_and;
      [apply (yp_sec_dealloc T r s1)
      | apply (apost_of_rpost _ true (fun x => CQ s1 (snd x)) (cq_sec_dealloc r s1 true))]].
    intros [u2 s2] [F2 C2]. cbn [snd] in F2, C2 |- *. unfold CQ in C2. destruct C2 as (C2 & _ & _).
    split; [exact (yp_trans _ _ _ _ F1 F2) | intros k' Hk'; apply I1; rewrite <- C2; exact Hk'].
Qed.

Lemma yp_recycle_items : forall T fuel items s, ypC T s ->
  apost (recycle_items fuel items s) (fun r => ypK T s (snd r) /\ ypI s (snd r)).
Proof.
  intros T fuel. induction fuel as [|f IH]; intros items s HC; destruct items as [|k t]; cbn [recycle_items].
  - apply apost_ret. cbn [snd]. split; [apply yp_refl | intros k' H; exact H].
  - apply apost_fail.
  - apply apost_ret. cbn [snd]. split; [apply yp_refl | intros k' H; exact H].
  - apply apost_bind. eapply apost_mono; [|apply (yp_recycle_chunk T k s HC)].
    intros [u1 s1] [F1 I1]. cbn [fst snd] in F1, I1 |- *.
    eapply apost_mono; [|apply (IH t s1 (yp_C_inc _ _ _ HC I1))].
    intros [u2 s2] [F2 I2]. cbn [snd] in F2, I2 |- *.
    split; [exact (yp_trans _ _ _ _ F1 F2) | intros k' H; exact (I1 k' (I2 k' H))].
Qed.

Lemma yp_do_recycle : forall T fuel bs s, ypC T s ->
  apost (do_recycle fuel bs s) (fun r => ypK (fun c => c = kBatchClass \/ T c) s (snd r) /\ ypI s (snd r)).
Proof.
  intros T fuel. induction fuel as [|f IH]; intros bs s HC; destruct bs as [|b t]; cbn [do_recycle].
  - apply apost_ret. cbn [snd]. split; [apply yp_refl | intros k' H; exact H].
  - apply apost_fail.
  - apply apost_ret. cbn [snd]. split; [apply yp_refl | intros k' H; exact H].
  - apply apost_bind. eapply apost_mono; [|apply (yp_recycle_items T _ (b_items b) s HC)].
    intros [u1 s1] [F1 I1]. cbn [fst snd] in F1, I1 |- *.
    apply apost_bind.
    eapply apost_mono; [|apply yp_and;
      [apply (yp_cache_dealloc (fun c => c = kBatchClass \/ T c) kBatchClass (b_self b) s1 (or_introl eq_refl))
      | apply (apost_of_rpost _ true (fun x => CQ s1 (snd x)) (cq_cache_dealloc kBatchClass (b_self b) s1 true))]].
    intros [u2 s2] [F2 C2]. cbn [fst snd] in F2, C2 |- *. unfold CQ in C2. destruct C2 as (C2 & _ & _).
    assert (I2 : ypI s s2) by (intros k' H; apply I1; rewrite <- C2; exact H).
    eapply apost_mono; [|apply (IH t s2 (yp_C_inc _ _ _ HC I2))].
    intros [u3 s3] [F3 I3]. cbn [snd] in F3, I3 |- *.
    split; [|intros k' H; exact (I2 k' (I3 k' H))].
    eapply yp_trans; [eapply yp_mono; [|exact F1]; intros c Hc; right; exact Hc|].
    exact (yp_trans _ _ _ _ F2 F3).
Qed.

(* The drain, with the real MergeBatches: it touches kBatchClass and the classes of the chunks it recycles. *)
Lemma yp_drain : forall T s, ypC T s ->
  apost (maybe_drain_cf s) (fun r => ypK (fun c => c = kBatchClass \/ T c) s (snd r)).
Proof.
  intros T s HC. rewrite YG03dcf.maybe_drain_cf_eq.
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_if; intros _; [apply apost_ret; apply yp_refl|].
  apply apost_bind. apply apost_put. cbn [fst snd].
  apply apost_if; intros _; [apply apost_ret; apply yp_same; reflexivity|].
  match goal with |- context [YG03dcf.merge_choice_cf ?g] => destruct (YG03dcf.merge_choice_cf g) as [gm ex] end.
  unfold YG03dcf.drain_tail_cf. cbn [fst snd].
  match goal with |- context [pop_batches ?f ?q ?a] => destruct (pop_batches f q a) as [g' popped] end.
  cbn [fst snd].
  apply apost_bind. apply apost_modify. cbn [fst snd].
  eapply apost_mono; [|apply (yp_do_recycle T); exact HC].
  intros [u y] [F _]. cbn [snd] in F |- *.
  eapply yp_trans; [|exact F]. apply yp_same; reflexivity.
Qed.

(* cgif's maybe_drain_effect (YG0k.v:332): within kQuarantineMax the drain recycles nothing. *)
Lemma yp_drain_nodrain : forall s, quar_bytes s <= kQuarantineMax ->
  apost (maybe_drain_cf s) (fun r => st_regions (snd r) = st_regions s /\ st_cache (snd r) = st_cache s /\
    quar_bytes (snd r) = quar_bytes s).
Proof.
  intros s Hq. rewrite YG03dcf.maybe_drain_cf_eq.
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_if; intros Hb; [apply apost_ret; cbn [snd]; repeat split; reflexivity|].
  apply apost_bind. apply apost_put. cbn [fst snd].
  apply apost_if; intros Hb2.
  - apply apost_ret. cbn [snd st_regions st_cache set_qglobal set_qthread]. split; [reflexivity|]. split; [reflexivity|].
    unfold quar_bytes. cbn [st_qglobal st_qthread set_qglobal set_qthread qc_bytes qc0]. lia.
  - exfalso. apply Z.leb_gt in Hb2. cbn [qc_bytes] in Hb2. unfold quar_bytes in Hq. lia.
Qed.

(* free_cf's text after `match p with PNull => ret tt | _ =>` (YG00cf.free_cf), as a function of p; with free_cf's
   size test (Quarantine::Put: a chunk above kQuarantineMax is recycled at once; a Theorem Labs lane's change 2026-10-30). *)
Definition free_tail_cf (p : sptr) (trace : list Z) : M unit :=
  s <- get ;;
  match find_user (st_chunks s) p with
  | None => fail (FModel 11)
  | Some k =>
    (if match ck_state k with CAllocated => true | _ => false end then ret tt else fail (FModel 12)) ;;
    depot_put trace ;;
    let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
    modify (fun s => set_chunks (upd_chunk (st_chunks s) k') s) ;;
    (if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') ;;
    maybe_drain_cf
  end.

Lemma yp_free_head : forall p trc S (Q : unit * astate -> Prop),
  (p = PNull -> forall s1, ypE5 S s1 -> Q (tt, s1)) ->
  (p <> PNull -> forall s1, ypE5 S s1 -> apost (free_tail_cf p trc s1) Q) ->
  apost (free_cf p trc S) Q.
Proof.
  intros p trc S Q H0 H1. unfold free_cf.
  apply apost_bind. apply apost_tick. cbn [fst snd].
  apply apost_bind. apply apost_get. cbn [fst snd].
  apply apost_bind.
  eapply apost_mono with (Q := fun r => ypE5 S (snd r)).
  2:{ apply apost_if; intros _; [apply apost_ret | apply apost_modify]; cbn [snd]; unfold ypE5; repeat split; reflexivity. }
  intros [[] s1] E1. cbn [fst snd] in E1 |- *.
  destruct p as [|off|r o|cid pos]; cbn [fst snd].
  - apply apost_ret. exact (H0 eq_refl s1 E1).
  - exact (H1 ltac:(discriminate) s1 E1).
  - exact (H1 ltac:(discriminate) s1 E1).
  - exact (H1 ltac:(discriminate) s1 E1).
Qed.

Lemma yp_free_tail : forall T p trc S s1, ypC T S -> ypE5 S s1 ->
  apost (free_tail_cf p trc s1) (fun r => ypK (fun c => c = kBatchClass \/ T c) S (snd r)).
Proof.
  intros T p trc S s1 HC (R1 & Ca1 & K1 & _ & _). unfold free_tail_cf.
  apply apost_bind. apply apost_get. cbn [fst snd].
  destruct (find_user (st_chunks s1) p) as [k|] eqn:Hf; cbn [fst snd]; [|apply apost_fail].
  apply apost_bind. apply apost_if; intros _; [apply apost_ret | apply apost_fail]. cbn [fst snd].
  apply apost_bind. eapply apost_mono; [|apply yp_depot_put].
  intros [[] s2] (R2 & Ca2 & K2 & _ & _). cbn [fst snd] in R2, Ca2, K2 |- *.
  apply apost_bind. apply apost_modify. cbn [fst snd].
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - apply apost_bind. eapply apost_mono; [|apply yp_enqueue].
    intros [[] s4] (F4 & C4 & _ & _). cbn [fst snd] in F4, C4 |- *.
    cbn [st_chunks set_chunks] in C4.
    assert (HC4 : ypC T s4).
    { unfold ypC. rewrite C4, K2, K1. apply yp_CL_upd; [exact HC|].
      rewrite <- K1. exact (proj1 (find_user_spec _ _ _ Hf)). }
    eapply apost_mono; [|apply (yp_drain T s4 HC4)]. intros [u5 s5] F5. cbn [snd] in F5 |- *.
    eapply yp_trans; [|exact F5].
    eapply yp_trans; [|eapply yp_mono; [|exact F4]; intros c Hc; left; exact Hc].
    apply yp_same; cbn [st_regions st_cache set_chunks]; congruence.
  - (* the recycle side: the chunk leaves at once; recycle_chunk keeps ypK T and shrinks the chunk list *)
    assert (HC3 : ypC T (set_chunks (upd_chunk (st_chunks s2) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s2)).
    { unfold ypC. cbn [st_chunks set_chunks]. rewrite K2, K1. apply yp_CL_upd; [exact HC|].
      rewrite <- K1. exact (proj1 (find_user_spec _ _ _ Hf)). }
    apply apost_bind. eapply apost_mono; [|apply (yp_recycle_chunk T _ _ HC3)].
    intros [[] s4] (F4 & I4). cbn [fst snd] in F4, I4 |- *.
    eapply apost_mono; [|apply (yp_drain T s4 (yp_C_inc T _ s4 HC3 I4))]. intros [u5 s5] F5. cbn [snd] in F5 |- *.
    eapply yp_trans; [|exact F5].
    eapply yp_trans; [|eapply yp_mono; [|exact F4]; intros c Hc; right; exact Hc].
    apply yp_same; cbn [st_regions st_cache set_chunks]; congruence.
Qed.

Lemma yp_free_tail_nodrain : forall p k trc S s1,
  find_user (st_chunks S) p = Some k -> ck_n k <= kQuarantineMax ->
  quar_bytes S + ck_n k + kBatchBytes <= kQuarantineMax -> ypE5 S s1 ->
  apost (free_tail_cf p trc s1) (fun r => ypK (fun c => c = kBatchClass) S (snd r) /\
    quar_bytes S + ck_n k <= quar_bytes (snd r) <= quar_bytes S + ck_n k + kBatchBytes).
Proof.
  intros p k trc S s1 Hf0 Hsz Hq (R1 & Ca1 & K1 & T1 & G1). unfold free_tail_cf.
  apply apost_bind. apply apost_get. cbn [fst snd].
  destruct (find_user (st_chunks s1) p) as [k1|] eqn:Hf; cbn [fst snd]; [|apply apost_fail].
  rewrite K1, Hf0 in Hf. injection Hf as E. subst k1.
  apply apost_bind. apply apost_if; intros _; [apply apost_ret | apply apost_fail]. cbn [fst snd].
  apply apost_bind. eapply apost_mono; [|apply yp_depot_put].
  intros [[] s2] (R2 & Ca2 & K2 & T2 & G2). cbn [fst snd] in R2, Ca2, K2, T2, G2 |- *.
  apply apost_bind. apply apost_modify. cbn [fst snd].
  (* the enqueue side of free_cf's size test (Hsz) *)
  match goal with |- context [if ?c then _ else _] => destruct c eqn:QS end;
    [|exfalso; apply Z.leb_gt in QS; unfold ck_n in QS, Hsz; cbn [ck_req] in QS; lia].
  apply apost_bind. eapply apost_mono; [|apply yp_enqueue].
  intros [[] s4] (F4 & C4 & G4 & Q4). cbn [fst snd] in F4, C4, G4, Q4 |- *.
  assert (Hq4 : quar_bytes S + ck_n k <= quar_bytes s4 <= quar_bytes S + ck_n k + kBatchBytes).
  { cbn [st_qthread st_qglobal set_chunks] in G4, Q4. rewrite T2, T1 in Q4. rewrite G2, G1 in G4.
    unfold quar_bytes. rewrite G4. unfold ck_n in Q4 |- *. cbn [ck_req] in Q4. destruct Q4 as [Qa Qb]. lia. }
  eapply apost_mono; [|apply (yp_drain_nodrain s4 ltac:(lia))].
  intros [u5 s5] (R5 & Ca5 & Q5). cbn [snd] in R5, Ca5, Q5 |- *.
  split; [|rewrite Q5; exact Hq4].
  apply (yp_trans _ _ s4); [|apply yp_same; assumption].
  eapply yp_trans; [|exact F4].
  apply yp_same; cbn [st_regions st_cache set_chunks]; congruence.
Qed.

Lemma yp_free_cf : forall T p trc S, ypC T S ->
  apost (free_cf p trc S) (fun r => ypK (fun c => c = kBatchClass \/ T c) S (snd r)).
Proof.
  intros T p trc S HC. apply yp_free_head.
  - intros _ s1 (R1 & Ca1 & _). cbn [snd]. apply yp_same; assumption.
  - intros _ s1 E1. exact (yp_free_tail T p trc S s1 HC E1).
Qed.

(* cgif's pristine_free_null (YG0k.v:404), for free_cf. *)
Theorem free_cf_null_keeps_pristine : forall trc S evs S' cs,
  apath (free_cf PNull trc S) evs (tt, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' cs /\ quar_bytes S' = quar_bytes S.
Proof.
  intros trc S evs S' cs Hy HP.
  assert (X : apost (free_cf PNull trc S) (fun r => ypE5 S (snd r))).
  { apply yp_free_head; [intros _ s1 E1; exact E1 | intros Hn; exfalso; apply Hn; reflexivity]. }
  pose proof (apost_apath _ _ _ _ X Hy) as (A & B & _ & C & D). cbn [snd] in A, B, C, D.
  split; [|unfold quar_bytes; rewrite C, D; reflexivity].
  intros c Hc Hcs. unfold pristine_class, reg, cache. rewrite A, B. exact (HP c Hc Hcs).
Qed.

(* (a) Any free, the drain included, when every primary chunk of the entry state is of a class given up. *)
Theorem free_cf_keeps_pristine_chk : forall p trc S evs S' cs,
  (forall k off, In k (st_chunks S) -> ck_beg k = PPrim off -> 1 <= prim_class off <= 31 ->
     In (prim_class off) (kBatchClass :: cs)) ->
  apath (free_cf p trc S) evs (tt, S') -> prim_pristine_except S cs -> prim_pristine_except S' (kBatchClass :: cs).
Proof.
  intros p trc S evs S' cs Hch Hy HP.
  pose proof (apost_apath _ _ _ _ (yp_free_cf (fun c => 1 <= c <= 31 -> In c (kBatchClass :: cs)) p trc S Hch) Hy) as K.
  cbn [snd] in K.
  apply (yp_pristine (kBatchClass :: cs) S S'); [|apply yp_pristine_cons; exact HP].
  eapply yp_mono_range; [|exact K]. intros c Hc [E|H]; [left; symmetry; exact E | exact (H Hc)].
Qed.

(* (c) cgif's pristine_free_norecycle (YG0k.v:418) without Wf: within kQuarantineMax nothing is recycled. The chunk
   is on free_cf's enqueue side (ck_n k <= kQuarantineMax; a Theorem Labs lane's change 2026-10-30). *)
Theorem free_cf_keeps_pristine_norecycle : forall p k trc S evs S' cs,
  p <> PNull -> find_user (st_chunks S) p = Some k -> ck_n k <= kQuarantineMax ->
  quar_bytes S + ck_n k + kBatchBytes <= kQuarantineMax ->
  apath (free_cf p trc S) evs (tt, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' (kBatchClass :: cs) /\ quar_bytes S + ck_n k <= quar_bytes S' <= quar_bytes S + ck_n k + kBatchBytes.
Proof.
  intros p k trc S evs S' cs Hp Hf Hsz Hq Hy HP.
  assert (X : apost (free_cf p trc S) (fun r => ypK (fun c => c = kBatchClass) S (snd r) /\
    quar_bytes S + ck_n k <= quar_bytes (snd r) <= quar_bytes S + ck_n k + kBatchBytes)).
  { apply yp_free_head; [intros Ep; contradiction | intros _ s1 E1; exact (yp_free_tail_nodrain p k trc S s1 Hf Hsz Hq E1)]. }
  pose proof (apost_apath _ _ _ _ X Hy) as [K Hqb]. cbn [snd] in K, Hqb.
  split; [|exact Hqb].
  apply (yp_pristine (kBatchClass :: cs) S S'); [|apply yp_pristine_cons; exact HP].
  eapply yp_mono; [|exact K]. intros c Hc. left. symmetry. exact Hc.
Qed.

(* ================================================================ under Wf_cf *)
Section WF.
Context {cp : CfParams}.

(* A pristine class has no chunk: a primary chunk of class c lies below rg_alloc_user (reg S c). *)
Lemma yp_chk_of_wf : forall U pp cc bb S cs, WfP_cf U pp cc bb S -> prim_pristine_except S cs ->
  ypC (fun c => In c cs) S.
Proof.
  intros U pp cc bb S cs W HP k off Hk Hb.
  pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [_ CK]. rewrite Hb in CK.
  destruct CK as (CKp & CKc & _).
  pose proof (chunk_class_range (ck_req k) CKp) as Hr. rewrite <- CKc in Hr.
  destruct (in_dec Z.eq_dec (prim_class off) cs) as [Hin|Hni]; [exact Hin|exfalso].
  destruct (HP (prim_class off) ltac:(lia) Hni) as (_ & A0 & _ & _).
  pose proof (wfc_classes _ _ _ _ _ W (prim_class off) ltac:(lia)) as CL.
  pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (off - region_off (prim_class off))) as E.
  specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left;
    exact (In_chunk_offs S k off Hk Hb))).
  destruct E as [E1 _]. lia.
Qed.

Theorem free_cf_keeps_pristine_except_wfp : forall U pp cc bb p trc S evs S' cs,
  WfP_cf U pp cc bb S -> apath (free_cf p trc S) evs (tt, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' (kBatchClass :: cs).
Proof.
  intros U pp cc bb p trc S evs S' cs W Hy HP.
  apply (free_cf_keeps_pristine_chk p trc S evs S' cs); [|exact Hy | exact HP].
  intros k off Hk Hb _. right. exact (yp_chk_of_wf U pp cc bb S cs W HP k off Hk Hb).
Qed.

(* (b) Any free_cf (PNull, a secondary block, a kBatchClass block, or any other live block), the drain
   included, gives up kBatchClass and nothing else. *)
Theorem free_cf_keeps_pristine_except : forall U p trc S evs S' cs,
  Wf_cf U S -> apath (free_cf p trc S) evs (tt, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' (kBatchClass :: cs).
Proof. intros U p trc S evs S' cs W. exact (free_cf_keeps_pristine_except_wfp U 0 0 0 p trc S evs S' cs W). Qed.

(* (c) cgif's pristine_free_norecycle (YG0k.v:418), statement for statement, for free_cf. The block is on free_cf's
   enqueue side: Wf_cf makes the quarantine's bytes non-negative (its batches' bytes sum non-negative requests), so
   the bytes premise gives req_size n <= kQuarantineMax. *)
Theorem pristine_free_norecycle_cf : forall U p n trc S evs S' cs,
  Wf_cf U S -> In (p, n) (blocks S) -> quar_bytes S + req_size n + kBatchBytes <= kQuarantineMax ->
  apath (free_cf p trc S) evs (tt, S') -> prim_pristine_except S cs ->
  prim_pristine_except S' (kBatchClass :: cs) /\ quar_bytes S <= quar_bytes S' <= quar_bytes S + req_size n + kBatchBytes.
Proof.
  intros U p n trc S evs S' cs W Hin Hq Hy HP.
  assert (HQ0 : 0 <= quar_bytes S).
  { pose proof (wfc_quarantine _ _ _ _ _ W) as WQ.
    assert (HI : Forall (fun k0 => 0 <= ck_req k0) (q_items S)).
    { apply Forall_forall. intros k0 Hk0.
      destruct (proj1 (Forall_forall _ _) (wq_items _ WQ) k0 Hk0) as [Hin0 _].
      exact (proj1 (proj1 (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k0 Hin0))). }
    unfold q_items, all_batches in HI. rewrite flat_map_app in HI. apply Forall_app in HI as [HIt HIg].
    pose proof (sum_bytes_nonneg _ HIt). pose proof (sum_bytes_nonneg _ HIg).
    unfold quar_bytes. rewrite (wq_bytes_g _ WQ), (wq_bytes_t _ WQ). lia. }
  assert (Hsz : req_size n <= kQuarantineMax) by (unfold kBatchBytes in Hq; lia).
  destruct (find_user_block_cf U 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ W) Hin) as (k & Hf & Hk & _ & _ & Hr).
  pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [Hn _]. rewrite Hr in Hn.
  assert (Hn1 : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  assert (Hck : ck_n k = req_size n) by (unfold ck_n; rewrite Hr; reflexivity).
  destruct (sptr_eq_dec p PNull) as [Ep|Hp].
  - subst p. destruct (free_cf_null_keeps_pristine trc S evs S' cs Hy HP) as [HP' HQ'].
    split; [apply yp_pristine_cons; exact HP' | rewrite HQ'; unfold kBatchBytes; lia].
  - rewrite <- Hck in Hq, Hsz.
    destruct (free_cf_keeps_pristine_norecycle p k trc S evs S' cs Hp Hf Hsz Hq Hy HP) as [HP' HQ'].
    rewrite Hck in HQ'. split; [exact HP' | lia].
Qed.

End WF.

(* ================================================================ refusal *)
(* cgif's malloc_refusal_sec (YG0k.v:16) and malloc_refusal_prim (YG0k.v:38), statement for statement with
   malloc -> malloc_cf and Wf -> Wf_cf. A secondary request's first ask is cgif's sec_alloc KMmapSec. A pristine
   primary class's first ask is KMapUser c 0 kUserMapSize in both arms of populate_cf: kBatchClass keeps cgif's
   map_more_user, and every other class reaches map_more_user_cf's map arm (YG00cf.v:166), never its class-full
   arm (:176), since kUserMapSize <= kFreeArrayOffset. A refusal (answer 0) leaves the state unchanged and
   cache_alloc_cf returns None, so malloc_cf returns PNull. Model lemmas only (rule 24). *)
Definition yrf_offer {A} (t : itree astate A) (P : A -> Prop) : Prop :=
  exists q snap k, t = IAsk q snap k /\ krefusable q = true /\ aok snap q 0 /\ exists a, k 0 = IRet a /\ P a.

Lemma yrf_offer_refusal : forall t, yrf_offer t (fun r => fst r = PNull) -> refusal_offered t.
Proof.
  intros t (q & snap & k & E & Hq & Ha & [p s'] & Hk & Hp). cbn [fst] in Hp. subst p.
  exists q, snap, k. split; [exact E|]. split; [exact Hq|]. split; [exact Ha|]. exists s'. exact Hk.
Qed.

Lemma yrf_bind_ret_eq {A B} : forall (m : M A) (k : A -> M B) s a s1, m s = IRet (a, s1) -> bind m k s = k a s1.
Proof.
  intros m k s a s1 E. change (bind m k s) with (ibind (m s) (fun '(a0, s') => k a0 s')). rewrite E. reflexivity.
Qed.

Lemma yrf_bind_ret {A B} : forall (m : M A) (k : A -> M B) s a s1 (P : B * astate -> Prop),
  m s = IRet (a, s1) -> yrf_offer (k a s1) P -> yrf_offer (bind m k s) P.
Proof. intros m k s a s1 P E H. rewrite (yrf_bind_ret_eq m k s a s1 E). exact H. Qed.

Lemma yrf_bind {A B} : forall (m : M A) (k : A -> M B) s (P : A * astate -> Prop) (Q : B * astate -> Prop),
  yrf_offer (m s) P -> (forall a s1, P (a, s1) -> exists b, k a s1 = IRet b /\ Q b) -> yrf_offer (bind m k s) Q.
Proof.
  intros m k s P Q (q & snap & c & E & Hq & Ha & [a0 s0] & Hc & HP) Hk.
  destruct (Hk a0 s0 HP) as (b & Eb & HQ).
  exists q, snap, (fun z => ibind (c z) (fun '(a, s') => k a s')).
  split; [change (bind m k s) with (ibind (m s) (fun '(a, s') => k a s')); rewrite E; reflexivity|].
  split; [exact Hq|]. split; [exact Ha|].
  exists b. split; [cbv beta; rewrite Hc; exact Eb | exact HQ].
Qed.

Lemma yrf_askz : forall q s, krefusable q = true -> aok s q 0 -> yrf_offer (askz q s) (fun r => r = (0, s)).
Proof.
  intros q s Hq Ha. exists q, s, (fun z => IRet (z, s)).
  split; [reflexivity|]. split; [exact Hq|]. split; [exact Ha|]. exists (0, s). split; reflexivity.
Qed.

Section REFUSAL.
Context {ci : CfImg}.

(* populate_cf on a class with nothing mapped and nothing carved: the first ask is KMapUser c 0 kUserMapSize,
   and its refusal returns false with the state unchanged. *)
Lemma yrf_populate_cf : forall c N s,
  rg_mapped_user (reg s c) = 0 -> rg_alloc_user (reg s c) = 0 -> 1 <= N * class_size c <= kUserMapSize ->
  yrf_offer (populate_cf c N s) (fun r => r = (false, s)).
Proof.
  intros c N s M0 A0 NS.
  assert (RU : round_up (0 + N * class_size c - 0) kUserMapSize = kUserMapSize).
  { unfold round_up, kUserMapSize in *.
    replace ((0 + N * class_size c - 0 + 262144 - 1) / 262144) with 1; [reflexivity|].
    apply Z.div_unique with (r := 0 + N * class_size c - 0 - 1); lia. }
  unfold populate_cf. destruct (c =? kBatchClass) eqn:Eb; cbv iota.
  - unfold populate.
    apply (yrf_bind _ _ _ (fun r => r = (false, s)));
      [|intros a s1 E; injection E as Ea Es; subst a s1; eexists; split; reflexivity].
    unfold map_more_user. apply (yrf_bind_ret _ _ s (reg s c) s); [reflexivity|]. cbv beta zeta.
    rewrite M0, A0. replace (0 <? 0 + N * class_size c) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite RU. cbv iota.
    apply (yrf_bind_ret _ _ s tt s); [reflexivity|]. cbv beta.
    apply (yrf_bind _ _ _ (fun r => r = (0, s))); [apply yrf_askz; [reflexivity | cbn; left; reflexivity]|].
    intros a s1 E; injection E as Ea Es; subst a s1. eexists; split; reflexivity.
  - apply (yrf_bind _ _ _ (fun r => r = (false, s)));
      [|intros a s1 E; injection E as Ea Es; subst a s1; eexists; split; reflexivity].
    unfold map_more_user_cf. rewrite Eb. cbv iota.
    apply (yrf_bind_ret _ _ s (reg s c) s); [reflexivity|]. cbv beta zeta.
    rewrite M0, A0. replace (0 <? 0 + N * class_size c) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite RU. replace (0 + kUserMapSize <=? kFreeArrayOffset) with true by reflexivity. cbv iota.
    apply (yrf_bind _ _ _ (fun r => r = (0, s))); [apply yrf_askz; [reflexivity | cbn; left; reflexivity]|].
    intros a s1 E; injection E as Ea Es; subst a s1. eexists; split; reflexivity.
Qed.

Lemma yrf_gfa_cf : forall c N s,
  rg_mapped_user (reg s c) = 0 -> rg_alloc_user (reg s c) = 0 -> rg_free (reg s c) = [] ->
  1 <= N -> 1 <= N * class_size c <= kUserMapSize ->
  yrf_offer (get_from_allocator_cf c N s) (fun r => r = (None, s)).
Proof.
  intros c N s M0 A0 F0 HN NS. unfold get_from_allocator_cf.
  apply (yrf_bind_ret _ _ s (reg s c) s); [reflexivity|]. cbv beta.
  rewrite F0. change (fa_len []) with 0. replace (0 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Z.sub_0_r. cbv iota.
  apply (yrf_bind _ _ _ (fun r => r = (false, s))); [exact (yrf_populate_cf c N s M0 A0 NS)|].
  intros a s1 E; injection E as Ea Es; subst a s1. eexists; split; reflexivity.
Qed.

Lemma yrf_refill_cf : forall c s,
  rg_mapped_user (reg s c) = 0 -> rg_alloc_user (reg s c) = 0 -> rg_free (reg s c) = [] ->
  pc_chunks (cache s c) = [] -> pc_max (cache s c) = max_cached c ->
  1 <= max_cached c / 2 -> 1 <= max_cached c / 2 * class_size c <= kUserMapSize ->
  yrf_offer (refill_if_empty_cf c s) (fun r => r = (tt, s)).
Proof.
  intros c s M0 A0 F0 C0 X0 HN NS. unfold refill_if_empty_cf.
  apply (yrf_bind_ret _ _ s (cache s c) s); [reflexivity|]. cbv beta.
  rewrite C0, X0. cbv iota.
  apply (yrf_bind _ _ _ (fun r => r = (None, s))); [exact (yrf_gfa_cf c (max_cached c / 2) s M0 A0 F0 HN NS)|].
  intros a s1 E; injection E as Ea Es; subst a s1. eexists; split; reflexivity.
Qed.

Lemma yrf_cache_alloc_cf : forall c s, 0 <= c <= 31 ->
  rg_mapped_user (reg s c) = 0 -> rg_alloc_user (reg s c) = 0 -> rg_free (reg s c) = [] ->
  pc_chunks (cache s c) = [] -> (st_cache_inited s = true -> pc_max (cache s c) = max_cached c) ->
  1 <= max_cached c / 2 -> 1 <= max_cached c / 2 * class_size c <= kUserMapSize ->
  yrf_offer (cache_alloc_cf c s) (fun r => fst r = None).
Proof.
  intros c s Hc M0 A0 F0 C0 X0 HN NS.
  assert (I : exists s2, init_cache_if_needed s = IRet (tt, s2) /\ reg s2 c = reg s c /\
    pc_chunks (cache s2 c) = [] /\ pc_max (cache s2 c) = max_cached c).
  { destruct (st_cache_inited s) eqn:CI.
    - exists s. split; [|split; [reflexivity | split; [exact C0 | exact (X0 eq_refl)]]].
      unfold init_cache_if_needed, bind, get. cbn [ibind]. rewrite CI. reflexivity.
    - exists (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
      split; [unfold init_cache_if_needed, bind, get; cbn [ibind]; rewrite CI; reflexivity|].
      rewrite (cache_after_init s c Hc). cbn [pc_chunks pc_max].
      split; [reflexivity|]. split; [exact C0 | reflexivity]. }
  destruct I as (s2 & E2 & R2 & C2 & X2).
  unfold cache_alloc_cf. apply (yrf_bind_ret _ _ s tt s2); [exact E2|]. cbv beta.
  apply (yrf_bind _ _ _ (fun r => r = (tt, s2))).
  - apply yrf_refill_cf; [rewrite R2; exact M0 | rewrite R2; exact A0 | rewrite R2; exact F0 | exact C2 | exact X2 | exact HN | exact NS].
  - intros a s1 E; injection E as Ea Es; subst a s1. exists (None, s2). split; [|reflexivity].
    cbv beta. rewrite (yrf_bind_ret_eq (get_pc c) _ s2 (cache s2 c) s2 eq_refl). cbv beta.
    rewrite C2. reflexivity.
Qed.

Lemma malloc_refusal_sec_cf : forall n trc S,
  from_primary n = false -> n < kMaxAllowedMalloc - kPage -> refusal_offered (malloc_cf n trc S).
Proof.
  intros n trc S Hp Hn. unfold refusal_offered, malloc_cf. rewrite Hp.
  replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  unfold bind, tick, mcheck, sec_alloc, bind, askz, modify, ret. cbn [ibind].
  eexists. eexists. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; left; reflexivity|].
  eexists. cbn [ibind Z.eqb]. reflexivity.
Qed.

Section d.
Context {cp : CfParams}.
Variable U : Univ.
Lemma malloc_refusal_prim_cf : forall n trc S cs,
  Wf_cf U S -> prim_pristine_except S cs ->
  0 <= n -> n < kMaxAllowedMalloc - kPage -> from_primary n = true -> ~ In (chunk_class n) cs ->
  refusal_offered (malloc_cf n trc S).
Proof.
  intros n trc S cs W HP Hn0 Hn Hp Hcs.
  pose proof (primary_geometry n Hn0 Hp) as (Hc & _ & Hsz & _ & Hpos).
  set (c := chunk_class n) in *.
  destruct (HP c ltac:(lia) Hcs) as (M0 & A0 & F0 & C0).
  assert (MC : 1 <= max_cached c / 2 <= 8).
  { unfold max_cached. rewrite (Z.mul_comm 2), Z.div_mul by lia. pose proof (Z.div_pos 1024 (class_size c) ltac:(lia) Hpos). lia. }
  assert (NS : 1 <= max_cached c / 2 * class_size c <= kUserMapSize).
  { unfold max_cached. rewrite (Z.mul_comm 2), Z.div_mul by lia.
    unfold kUserMapSize, kMaxSize in *.
    destruct (Z_lt_le_dec 1024 (class_size c)).
    - rewrite (Z.div_small 1024 (class_size c)) by lia. change (Z.max 1 (Z.min 8 0)) with 1. lia.
    - assert (1 <= 1024 / class_size c) by (apply Z.div_le_lower_bound; lia).
      pose proof (Z.mul_div_le 1024 (class_size c) ltac:(lia)). nia. }
  pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c ltac:(lia))) as XC.
  apply yrf_offer_refusal. unfold malloc_cf.
  apply (yrf_bind_ret _ _ S tt (set_nev (st_nev S + 1) S)); [reflexivity|]. cbv beta.
  replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  apply (yrf_bind_ret _ _ _ tt (set_nev (st_nev S + 1) S)); [reflexivity|]. cbv beta.
  rewrite Hp. cbv iota.
  apply (yrf_bind _ _ _ (fun r => fst r = None)).
  - apply (yrf_bind _ _ _ (fun r => fst r = None)).
    + apply (yrf_cache_alloc_cf c); [lia | exact M0 | exact A0 | exact F0 | exact C0 | | lia | exact NS].
      intros CI. change (st_cache_inited S = true) in CI. rewrite CI in XC. exact (proj1 XC).
    + intros a s1 Ea. cbn [fst] in Ea. subst a. eexists; split; reflexivity.
  - intros a s1 Ea. cbn [fst] in Ea. subst a. eexists; split; reflexivity.
Qed.
End d.
End REFUSAL.
