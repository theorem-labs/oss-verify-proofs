(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma get_set_region_eq : forall s c r, get_region (set_region c r s) c = r.
Proof. intros. unfold get_region, set_region; cbn [as_regions]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_set_region_ne : forall s c c' r, c <> c' -> get_region (set_region c r s) c' = get_region s c'.
Proof. intros. unfold get_region, set_region; cbn [as_regions]. rewrite lookup_insert_ne by auto. reflexivity. Qed.
Lemma get_set_cache_eq : forall s c l, get_cache (set_cache c l s) c = l.
Proof. intros. unfold get_cache, set_cache; cbn [as_cache]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_set_cache_ne : forall s c c' l, c <> c' -> get_cache (set_cache c l s) c' = get_cache s c'.
Proof. intros. unfold get_cache, set_cache; cbn [as_cache]. rewrite lookup_insert_ne by auto. reflexivity. Qed.

Lemma as_regions_upd_ts_set_region : forall f c r s, as_regions (upd_ts f (set_region c r s)) = <[c := r]> (as_regions s).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma get_region_upd_ts : forall f s c, get_region (upd_ts f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_ts : forall f s c, get_cache (upd_ts f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_cache_mapped : forall f s c, get_region (upd_cache_mapped f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_cache_mapped : forall f s c, get_cache (upd_cache_mapped f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_cache_allocated : forall f s c, get_region (upd_cache_allocated f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_cache_allocated : forall f s c, get_cache (upd_cache_allocated f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_cache_stale : forall f s c, get_region (upd_cache_stale f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_cache_stale : forall f s c, get_cache (upd_cache_stale f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_oom : forall v s c, get_region (upd_oom v s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_oom : forall v s c, get_cache (upd_oom v s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_keys : forall f g s c, get_region (upd_keys f g s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_keys : forall f g s c, get_cache (upd_keys f g s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_chunks : forall f s c, get_region (upd_chunks f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_chunks : forall f s c, get_cache (upd_chunks f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_dead : forall f s c, get_region (upd_dead f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_dead : forall f s c, get_cache (upd_dead f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_tq : forall f s c, get_region (upd_tq f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_tq : forall f s c, get_cache (upd_tq f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_gq : forall f s c, get_region (upd_gq f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_gq : forall f s c, get_cache (upd_gq f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_sec : forall f s c, get_region (upd_sec f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_sec : forall f s c, get_cache (upd_sec f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_sec_stale : forall f s c, get_region (upd_sec_stale f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_sec_stale : forall f s c, get_cache (upd_sec_stale f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_sec_stats : forall f s c, get_region (upd_sec_stats f s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_sec_stats : forall f s c, get_cache (upd_sec_stats f s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_glob : forall f g s c, get_region (upd_glob f g s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_glob : forall f g s c, get_cache (upd_glob f g s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_ia_inited : forall v s c, get_region (upd_ia_inited v s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_ia_inited : forall v s c, get_cache (upd_ia_inited v s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_ptr_committed : forall v s c, get_region (upd_ptr_committed v s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_ptr_committed : forall v s c, get_cache (upd_ptr_committed v s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_upd_cache_inited : forall v s c, get_region (upd_cache_inited v s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_upd_cache_inited : forall v s c, get_cache (upd_cache_inited v s) c = get_cache s c.
Proof. reflexivity. Qed.
Lemma get_region_set_cache : forall c' l s c, get_region (set_cache c' l s) c = get_region s c.
Proof. reflexivity. Qed.
Lemma get_cache_set_region : forall c' r s c, get_cache (set_region c' r s) c = get_cache s c.
Proof. reflexivity. Qed.
End RC__1.
#[export] Hint Rewrite get_region_upd_ts get_cache_upd_ts get_region_upd_cache_mapped get_cache_upd_cache_mapped get_region_upd_cache_allocated get_cache_upd_cache_allocated get_region_upd_cache_stale get_cache_upd_cache_stale get_region_upd_oom get_cache_upd_oom get_region_upd_keys get_cache_upd_keys get_region_upd_chunks get_cache_upd_chunks get_region_upd_dead get_cache_upd_dead get_region_upd_tq get_cache_upd_tq get_region_upd_gq get_cache_upd_gq get_region_upd_sec get_cache_upd_sec get_region_upd_sec_stale get_cache_upd_sec_stale get_region_upd_sec_stats get_cache_upd_sec_stats get_region_upd_glob get_cache_upd_glob get_region_upd_ia_inited get_cache_upd_ia_inited get_region_upd_ptr_committed get_cache_upd_ptr_committed get_region_upd_cache_inited get_cache_upd_cache_inited get_region_set_cache get_cache_set_region get_set_region_eq get_set_cache_eq : asimp.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition same_core (s s' : astate) : Prop :=
  as_regions s' = as_regions s /\ as_cache s' = as_cache s /\ as_cache_inited s' = as_cache_inited s
  /\ as_chunks s' = as_chunks s /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s
  /\ as_sec s' = as_sec s /\ as_ptr_committed s' = as_ptr_committed s
  /\ as_keys s' = as_keys s /\ as_frames s' = as_frames s /\ as_ndepot_ins s' = as_ndepot_ins s.

Section WF.
Variable E : aenv.
Variable P : list Z.        (* [comment removed for export] *)
Variable D : list batch.    (* [comment removed for export] *)
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
Lemma AWf_same_core : forall s s', same_core s s' -> AWF s -> AWF s'.
Proof.
  intros s s' (HR & HC & HI & HK & HT & HG & HS & HP & HKy & HF & HN) H.
  unfold AWf, wf_regions, wf_cache, wf_chunks, wf_chunk, wf_quarantine, wf_batch, wf_dbatch, wf_secondary, wf_depot in *.
  unfold carved, in_free, in_cache, is_batch, all_batches, is_chunk_block, chunk_used_size, tq_bytes, gq_bytes, n_chunks, rg_num_freed in *.
  unfold region_of in *. unfold get_region, get_cache in *.
  rewrite ?HR, ?HC, ?HI, ?HK, ?HT, ?HG, ?HS, ?HP, ?HKy, ?HF, ?HN. exact H.
Qed.

(* [comment removed for export] *)
Definition same_alloc (s s' : astate) : Prop :=
  as_regions s' = as_regions s /\ as_cache s' = as_cache s /\ as_cache_inited s' = as_cache_inited s
  /\ as_chunks s' = as_chunks s /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s
  /\ as_sec s' = as_sec s /\ as_ptr_committed s' = as_ptr_committed s.

Lemma AWf_frame_depot : forall s s', same_alloc s s' -> wf_depot E s' -> AWF s -> AWF s'.
Proof.
  intros s s' (HR & HC & HI & HK & HT & HG & HS & HP) HD H.
  destruct H as (WE & WR & WC & WK & WQ & WS & WD).
  unfold AWf. split; [exact WE|].
  unfold wf_regions, wf_cache, wf_chunks, wf_chunk, wf_quarantine, wf_batch, wf_dbatch, wf_secondary in *.
  unfold carved, in_free, in_cache, is_batch, all_batches, is_chunk_block, chunk_used_size, tq_bytes, gq_bytes, n_chunks, rg_num_freed in *.
  unfold region_of in *. unfold get_region, get_cache in *.
  rewrite ?HR, ?HC, ?HI, ?HK, ?HT, ?HG, ?HS, ?HP. repeat (split; [assumption|]). exact HD.
Qed.

(* [comment removed for export] *)
Lemma same_core_upd_ts : forall f s, same_core s (upd_ts f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_oom : forall v s, same_core s (upd_oom v s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_ia : forall v s, same_core s (upd_ia_inited v s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_cache_allocated : forall f s, same_core s (upd_cache_allocated f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_cache_mapped : forall f s, same_core s (upd_cache_mapped f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_cache_stale : forall f s, same_core s (upd_cache_stale f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_sec_stale : forall f s, same_core s (upd_sec_stale f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_sec_stats : forall f s, same_core s (upd_sec_stats f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_glob : forall f g s, same_core s (upd_glob f g s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_upd_dead : forall f s, same_core s (upd_dead f s).
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_refl : forall s, same_core s s.
Proof. intros; repeat split; reflexivity. Qed.
Lemma same_core_trans : forall a b c, same_core a b -> same_core b c -> same_core a c.
Proof. intros a b c H1 H2. unfold same_core in *. intuition congruence. Qed.

Lemma preserves_same_core : forall f, (forall s, same_core s (f s)) -> preserves AWF (aupd f).
Proof. intros f Hf. apply hoare_upd. intros s Hs. eapply AWf_same_core; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fold_keys_app : forall (l1 l2 : list (list Z)),
  fold_right (fun k acc => zlen k + 1 + acc) 0 (l1 ++ l2)
  = fold_right (fun k acc => zlen k + 1 + acc) 0 l1 + fold_right (fun k acc => zlen k + 1 + acc) 0 l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.

Lemma fold_keys_nonneg : forall (l : list (list Z)), 0 <= fold_right (fun k acc => zlen k + 1 + acc) 0 l.
Proof. induction l; cbn; [lia|]. unfold zlen in *. lia. Qed.

Lemma index_of_none_notin : forall h l i, index_of h l i = None -> ~ In h (map depot_hash l).
Proof.
  induction l as [|k' l IH]; intros i H; cbn in *; [tauto|].
  destruct (depot_hash k' =? h) eqn:EQ; [discriminate|]. apply Z.eqb_neq in EQ. intros [<-|Hin]; [congruence|]. eapply IH; eauto.
Qed.

Lemma NoDup_app_fresh : forall (l : list Z) k, List.NoDup l -> ~ In k l -> List.NoDup (l ++ [k]).
Proof.
  induction l as [|x l IH]; intros k ND NI; cbn.
  - constructor; [intros []| constructor].
  - inversion ND; subst. constructor.
    + rewrite in_app_iff. intros [H|[H|[]]]; [contradiction|]. subst. apply NI. left; reflexivity.
    + apply IH; [assumption|]. intros H; apply NI; right; exact H.
Qed.

Lemma sum_sublist_le : forall (l m : list (list Z)),
  List.NoDup l -> (forall k, In k l -> In k m) ->
  fold_right (fun k acc => zlen k + 1 + acc) 0 l <= fold_right (fun k acc => zlen k + 1 + acc) 0 m.
Proof.
  induction l as [|x l IH]; intros m ND SUB; cbn.
  - apply fold_keys_nonneg.
  - inversion ND; subst.
    assert (Hx : In x m) by (apply SUB; left; reflexivity).
    apply in_split in Hx as (m1 & m2 & ->).
    rewrite fold_keys_app. cbn.
    specialize (IH (m1 ++ m2) ltac:(assumption)).
    rewrite fold_keys_app in IH.
    assert (forall k, In k l -> In k (m1 ++ m2)).
    { intros k Hk. assert (In k (m1 ++ x :: m2)) as Hin by (apply SUB; right; exact Hk).
      rewrite in_app_iff in Hin |- *. destruct Hin as [Hin|[<-|Hin]]; [left; exact Hin| contradiction| right; exact Hin]. }
    specialize (IH H). unfold zlen in *. lia.
Qed.

Lemma index_of_ge : forall h l i j, index_of h l i = Some j -> i <= j.
Proof.
  intros h l. induction l as [|k' l IH]; intros i j H; cbn in H; [discriminate|].
  destruct (depot_hash k' =? h); [injection H; lia|]. specialize (IH _ _ H). lia.
Qed.

(* [comment removed for export] *)
Definition depot_ok (s : astate) (key : list Z) : Prop := zlen key + 1 <= 2^16 /\ depot_n_ids E s + 2 < 2^31.

Lemma call_mmap_ordie_frame : forall (PP : astate -> Prop) len fl,
  hoare PP (call_mmap_ordie E len fl) (fun s' _ => PP s').
Proof.
  intros PP0 len fl. unfold call_mmap_ordie. apply hoare_get_bind. intros s Hs.
  eapply hoare_bind with (Q := fun s' _ => s' = s); [apply hoare_call; auto|].
  intros [r|e]; cbn; [| apply hoare_spin].
  match goal with |- hoare _ (if ?b then _ else _) _ => destruct b end; [|apply hoare_undef; exact I].
  match goal with |- hoare _ (if ?b then _ else _) _ => destruct b end; [|apply hoare_undef; exact I].
  apply hoare_ret. intros s0 ->. exact Hs.
Qed.

(* [comment removed for export] *)
Lemma AWf_depot_only : forall s s', same_alloc s s' -> as_keys s' = as_keys s -> as_frames s <= as_frames s' ->
  as_ndepot_ins s <= as_ndepot_ins s' -> AWF s -> AWF s'.
Proof.
  intros s s' SA HK HF HN WF. eapply AWf_frame_depot; [exact SA| | exact WF].
  destruct WF as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3)). unfold wf_depot. rewrite HK. split; [exact D1|]. split; lia.
Qed.

Lemma store_alloc_once_spec : forall s0 count, 1 <= count <= 2^16 -> AWF s0 ->
  hoare (fun s => s = s0) (store_alloc_once E count)
    (fun s' r => AWF s' /\ same_alloc s0 s' /\ as_keys s' = as_keys s0 /\ as_ndepot_ins s' = as_ndepot_ins s0
                 /\ as_frames s' = as_frames s0 + count
                 /\ (r = None -> (as_frames s0) / kStoreBlockFrames <> (as_frames s0 + count - 1) / kStoreBlockFrames)).
Proof.
  intros s0 count Hc WF. unfold store_alloc_once. apply hoare_get_bind. intros s ->.
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->). set (s1 := upd_keys _ _ s0).
  assert (SA1 : same_alloc s0 s1) by (unfold same_alloc; repeat split; reflexivity).
  assert (WF1 : AWF s1) by (eapply AWf_depot_only; [exact SA1| reflexivity| cbn; lia| cbn; lia| exact WF]).
  destruct (as_frames s0 / kStoreBlockFrames =? (as_frames s0 + count - 1) / kStoreBlockFrames) eqn:FIT.
  - apply hoare_get_bind. intros s ->.
    eapply hoare_bind with (Q := fun s2 _ => AWF s2 /\ same_alloc s0 s2 /\ as_keys s2 = as_keys s0 /\ as_ndepot_ins s2 = as_ndepot_ins s0 /\ as_frames s2 = as_frames s0 + count).
    { match goal with |- hoare _ (if ?b then _ else _) _ => destruct b end.
      - eapply hoare_bind; [apply (call_mmap_ordie_frame (fun s => s = s1))|]. intros r. apply hoare_pre. intros s ->.
        apply hoare_upd. intros s ->. split; [| split; [unfold same_alloc; repeat split; reflexivity| cbn; repeat split; reflexivity]].
        eapply AWf_same_core; [| exact WF1]. unfold same_core; repeat split; reflexivity.
      - apply hoare_ret. intros s ->. split; [exact WF1|]. split; [exact SA1|]. cbn; repeat split; reflexivity. }
    intros []. apply hoare_ret. intros s (A & B & C & DD & F). split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact DD|]. split; [exact F|]. discriminate.
  - apply hoare_upd_bind. apply hoare_ret. intros s (sx & -> & ->). apply Z.eqb_neq in FIT.
    split; [eapply AWf_same_core; [| exact WF1]; unfold same_core; repeat split; reflexivity|].
    split; [unfold same_alloc; repeat split; reflexivity|]. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros _. exact FIT.
Qed.

Lemma store_alloc_spec : forall s0 count, 1 <= count <= 2^16 -> AWF s0 ->
  hoare (fun s => s = s0) (store_alloc E count)
    (fun s' _ => AWF s' /\ same_alloc s0 s' /\ as_keys s' = as_keys s0 /\ as_ndepot_ins s' = as_ndepot_ins s0 /\ as_frames s0 <= as_frames s').
Proof.
  intros s0 count Hc WF. unfold store_alloc.
  eapply hoare_bind; [apply (store_alloc_once_spec s0 count Hc WF)|]. intros r. apply hoare_pre. intros s1 (WF1 & SA1 & K1 & N1 & F1 & STR).
  destruct r as [st|].
  { apply hoare_ret. intros s ->. split; [exact WF1|]. split; [exact SA1|]. split; [exact K1|]. split; [exact N1| lia]. }
  specialize (STR eq_refl).
  eapply hoare_bind; [apply (store_alloc_once_spec s1 count Hc WF1)|]. intros r2. apply hoare_pre. intros s2 (WF2 & SA2 & K2 & N2 & F2 & STR2).
  destruct r2 as [st|].
  - apply hoare_ret. intros s ->. split; [exact WF2|].
    split; [destruct SA1 as (A1&A2&A3&A4&A5&A6&A7&A8); destruct SA2 as (B1&B2&B3&B4&B5&B6&B7&B8); unfold same_alloc; repeat split; congruence|].
    split; [congruence|]. split; [congruence| lia].
  - exfalso. apply (STR2 eq_refl). rewrite F1. unfold kStoreBlockFrames in *.
    set (f := as_frames s0) in *.
    pose proof (Z.div_mod f (2^20) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound f (2^20) ltac:(lia)) as MB.
    set (q := f / 2^20) in *. set (r0 := f mod 2^20) in *.
    assert (ST1 : 2^20 <= r0 + count).
    { destruct (Z.le_gt_cases (2^20) (r0 + count)); [assumption|]. exfalso. apply STR.
      replace f with (r0 + q * 2^20) by lia. replace (r0 + q * 2^20 + count - 1) with ((r0 + count - 1) + q * 2^20) by lia.
      rewrite !Z.div_add by lia. rewrite !Z.div_small by lia. reflexivity. }
    replace (f + count) with ((r0 + count - 2^20) + (q + 1) * 2^20) by lia.
    replace (r0 + count - 2^20 + (q + 1) * 2^20 + count - 1) with ((r0 + 2 * count - 2^20 - 1) + (q + 1) * 2^20) by lia.
    rewrite !Z.div_add by lia. rewrite !Z.div_small by lia. reflexivity.
Qed.

Lemma depot_put_wf : forall s0 key,
  depot_ok s0 key -> AWF s0 ->
  hoare (fun s => s = s0) (depot_put E key)
    (fun s' id => AWF s' /\ same_alloc s0 s' /\ 1 <= id /\ depot_n_ids E s' <= depot_n_ids E s0 + 1).
Proof.
  intros s0 key [KL IDB] Hs. unfold depot_put. apply hoare_get_bind. intros s ->.
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->). set (s1 := upd_ndepot _ s0).
  assert (SA1 : same_alloc s0 s1) by (unfold same_alloc; repeat split; reflexivity).
  assert (WF1 : AWF s1) by (eapply AWf_depot_only; [exact SA1| reflexivity| cbn; lia| cbn; lia| exact Hs]).
  destruct (depot_lookup E s0 key) as [id|] eqn:HL.
  - apply hoare_ret. intros s ->. split; [exact WF1|]. split; [exact SA1|].
    split; [unfold depot_lookup in HL; exact (index_of_ge _ _ _ _ HL)| subst s1; unfold depot_n_ids; cbn; lia].
  - unfold acheck. replace (depot_n_ids E s0 + 1 <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
    eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s1); auto|]. intros []. apply hoare_pre. intros s ->.
    eapply hoare_bind with (Q := fun s2 _ => AWF s2 /\ same_alloc s0 s2 /\ as_keys s2 = as_keys s0 /\ as_ndepot_ins s2 = as_ndepot_ins s0 + 1 /\ as_frames s2 = as_frames s0).
    { match goal with |- hoare _ (if ?b then _ else _) _ => destruct b end.
      - eapply hoare_bind; [apply (call_mmap_ordie_frame (fun s => s = s1))|]. intros r. apply hoare_pre. intros s ->.
        apply hoare_upd. intros s ->. split; [eapply AWf_same_core; [| exact WF1]; unfold same_core; repeat split; reflexivity|].
        split; [unfold same_alloc; repeat split; reflexivity| cbn; repeat split; reflexivity].
      - apply hoare_ret. intros s ->. split; [exact WF1|]. split; [exact SA1| cbn; repeat split; reflexivity]. }
    intros []. apply hoare_pre. intros s2 (WF2 & SA2 & K2 & N2 & F2).
    eapply hoare_bind; [apply (store_alloc_spec s2 (zlen key + 1) ltac:(unfold zlen in *; lia) WF2)|].
    intros st. apply hoare_pre. intros s3 (WF3 & SA3 & K3 & N3 & F3).
    apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
    pose proof WF3 as X. destruct X as (WE & WR & WC & WK & WQ & WS & (D1 & D2 & D3)).
    assert (NI : ~ In (depot_hash key) (map depot_hash (ae_keys0 E ++ as_keys s0))) by (eapply index_of_none_notin; unfold depot_lookup in HL; exact HL).
    split; [| split; [| split; [unfold depot_n_ids; lia| unfold depot_n_ids; cbn; rewrite K3, K2, length_app; cbn; lia]]].
    2:{ destruct SA2 as (A1&A2&A3&A4&A5&A6&A7&A8). destruct SA3 as (B1&B2&B3&B4&B5&B6&B7&B8). unfold same_alloc; cbn; repeat split; congruence. }
    eapply AWf_frame_depot; [| | exact WF3]; [unfold same_alloc; repeat split; reflexivity|].
    unfold wf_depot; cbn. rewrite K3, K2. split; [| split; [unfold zlen in *; rewrite length_app; cbn; rewrite N3, N2; destruct Hs as (_&_&_&_&_&_&(_ & X & _)); unfold zlen in X; lia| lia]].
    rewrite app_assoc, map_app. cbn [map]. apply NoDup_app_fresh; [| exact NI]. destruct Hs as (_&_&_&_&_&_&(X & _)). exact X.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regions_sim (s s' : astate) : Prop :=
  forall c, rg_alloc_user (get_region s' c) = rg_alloc_user (get_region s c)
            /\ rg_free (get_region s' c) = rg_free (get_region s c).

Lemma AWf_frame_regions : forall s s',
  as_cache_inited s = true -> as_cache_inited s' = true ->
  as_cache s' = as_cache s -> as_chunks s' = as_chunks s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  as_sec s' = as_sec s -> as_ptr_committed s' = as_ptr_committed s -> as_keys s' = as_keys s -> as_frames s' = as_frames s ->
  as_ndepot_ins s' = as_ndepot_ins s ->
  regions_sim s s' ->
  wf_regions E s' -> AWF s -> AWF s'.
Proof.
  intros s s' HI HI' HC HK HT HG HS HP HKy HF HN SIM WR' H.
  destruct H as (WE & WR & WC & WCH & WQ & WS & WD).
  assert (CARV : forall c a, carved E s' c a <-> carved E s c a).
  { intros c a. unfold carved, region_of. destruct (SIM c) as [-> _]. tauto. }
  assert (FREE : forall c a, in_free E s' c a <-> in_free E s c a).
  { intros c a. unfold in_free, region_of. destruct (SIM c) as [_ ->]. tauto. }
  split; [exact WE|]. split; [exact WR'|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) destruct WC as (C1 & C2 & C3). unfold wf_cache. rewrite HC, HI'. split; [exact C1|]. split; [discriminate|].
    intros c Hc. unfold get_cache. rewrite HC. destruct (C3 c Hc) as (A & B & C). split; [exact A|]. split; [exact B|].
    intros x Hx. destruct (C x Hx) as (D9 & E0 & F). split; [apply CARV; exact D9|]. split; [exact E0|].
    unfold region_of. destruct (SIM c) as [_ ->]. exact F.
  - (* [comment removed for export] *) destruct WCH as (K1 & K2). unfold wf_chunks. rewrite HK. split; [|exact K2].
    intros cb cm Hcm. destruct (K1 cb cm Hcm) as (A & B & C & D0 & E0). unfold wf_chunk.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    + destruct (cm_prim cm) as [c|].
      * destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6). split; [exact D1|]. split; [exact D2|]. split; [apply CARV; exact D3|].
        split; [intros X; apply D4; apply FREE; exact X|]. split; [unfold in_cache, get_cache; rewrite HC; exact D5|].
        unfold is_batch, all_batches. rewrite HT, HG. exact D6.
      * rewrite HS. exact D0.
    + unfold all_batches. rewrite ?HT, ?HG. exact E0.
  - (* [comment removed for export] *) destruct WQ as (Q1 & QD & Q2 & Q3). unfold wf_quarantine, all_batches. rewrite HT, HG.
    split; [|split; [|split; [exact Q2| exact Q3]]].
    + intros b Hb. destruct (Q1 b Hb) as [WB NB]. split; [|exact NB].
      destruct WB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). unfold wf_batch.
      split; [apply CARV; exact B1|]. split; [intros X; apply B2; apply FREE; exact X|].
      split; [unfold in_cache, get_cache; rewrite HC; exact B3|]. split; [unfold is_chunk_block; rewrite HK; exact B4|].
      split; [exact B5|]. split; [unfold chunk_used_size; rewrite HK; exact B6|]. split; [exact B7|].
      unfold chunk_used_size. rewrite HK. exact B8.
    + intros b Hb. destruct (QD b Hb) as (B1 & B2 & B3 & B4 & B7). unfold wf_dbatch.
      split; [apply CARV; exact B1|]. split; [intros X; apply B2; apply FREE; exact X|].
      split; [unfold in_cache, get_cache; rewrite HC; exact B3|]. split; [unfold is_chunk_block; rewrite HK; exact B4| exact B7].
  - unfold wf_secondary, n_chunks. rewrite HS, HP. exact WS.
  - unfold wf_depot. rewrite HKy, HF, HN. exact WD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma call_mmap_fixed_frame : forall (PP : astate -> Prop) addr len,
  hoare PP (call_mmap_fixed addr len) (fun s' _ => PP s').
Proof.
  intros PP0 addr len. unfold call_mmap_fixed.
  eapply hoare_bind with (Q := fun s' _ => PP0 s'); [apply hoare_call; auto|].
  intros [r|e]; cbn.
  - destruct (r =? addr); [apply hoare_ret; auto| apply hoare_undef; exact I].
  - destruct (e =? ENOMEM); [apply hoare_ret; auto| apply hoare_undef; exact I].
Qed.


Lemma call_munmap_frame : forall (PP : astate -> Prop) addr len,
  hoare PP (call_munmap addr len) (fun s' _ => PP s').
Proof.
  intros PP0 addr len. unfold call_munmap.
  eapply hoare_bind with (Q := fun s' _ => PP0 s'); [apply hoare_call; auto|].
  intros [r|e]; cbn.
  - destruct (r =? 0); [apply hoare_ret; auto| apply hoare_undef; exact I].
  - apply hoare_spin.
Qed.

Lemma call_mmap_anon_frame : forall (PP : astate -> Prop) len,
  hoare PP (call_mmap_anon E len)
        (fun s' r => PP s' /\ forall a, r = Some a ->
            a mod kPageSize = 0 /\ 0 < a /\ a + len <= alloc_ceiling /\ ranges_free (known_ranges E s') a len = true
            /\ app_mem a len /\ in_primary (ae_space_beg E) a = false /\ in_primary (ae_space_beg E) (a + len - 1) = false /\ a + len <= kHighMemEnd + 1).
Proof.
  intros PP0 len. unfold call_mmap_anon. apply hoare_get_bind. intros s Hs.
  eapply hoare_bind with (Q := fun s' _ => s' = s); [apply hoare_call; auto|].
  intros [r|e]; cbn.
  - match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:HB end; [|apply hoare_undef; exact I].
    match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:HB2 end; [|apply hoare_undef; exact I].
    apply hoare_ret. intros s0 ->. split; [exact Hs|]. intros a [= <-].
    apply andb_prop in HB as [HB H4]. apply andb_prop in HB as [HB H3]. apply andb_prop in HB as [H1 H2].
    apply andb_prop in HB2 as [HB2 H8]. apply andb_prop in HB2 as [HB2 H7]. apply andb_prop in HB2 as [H5 H6].
    apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply app_mem_b_iff in H5. apply Z.leb_le in H8.
    apply negb_true_iff in H6. apply negb_true_iff in H7.
    repeat split; assumption.
  - destruct (e =? ENOMEM); [|apply hoare_undef; exact I]. apply hoare_ret. intros s0 ->. split; [exact Hs| intros a; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_seqZ : forall m n k, m <= k < m + n -> In k (seqZ m n).
Proof. intros m n k H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_seqZ. lia. Qed.

Lemma pigeonhole_multiples : forall (l : list Z) (K u : Z),
  0 < u -> 0 <= K -> List.NoDup l ->
  (forall x, In x l -> exists k, 0 <= k < K /\ x = k * u) ->
  Z.of_nat (length l) <= K.
Proof.
  intros l K u Hu HK ND H.
  assert (INCL : incl (map (fun x => x / u) l) (seqZ 0 K)).
  { intros y Hy. apply in_map_iff in Hy as (x & <- & Hx). destruct (H x Hx) as (k & Hk & ->).
    rewrite Z.div_mul by lia. apply In_seqZ. lia. }
  assert (ND' : List.NoDup (map (fun x => x / u) l)).
  { revert ND H. clear INCL. induction l as [|x l IH]; intros ND H; cbn; [constructor|]. inversion ND; subst. constructor.
    - intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
      destruct (H x (or_introl eq_refl)) as (k & Hk & Ex). destruct (H y (or_intror Hiny)) as (k' & Hk' & Ey).
      subst x y. rewrite !Z.div_mul in Hy by lia. subst k'. contradiction.
    - apply IH; [assumption|]. intros z Hz. apply H. right; exact Hz. }
  pose proof (NoDup_incl_length ND' INCL) as L. rewrite length_map, length_seqZ in L. lia.
Qed.


Lemma compact_chunk_id : forall sb c x, compact_of_chunk sb c (chunk_of_compact sb c x) = x.
Proof.
  intros. unfold compact_of_chunk, chunk_of_compact.
  replace (region_beg sb c + 16 * x - region_beg sb c) with (x * 16) by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_ziota : forall k a i, In i (ziota a k) <-> a <= i < a + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros a i; cbn; [lia|]. rewrite IH. lia.
Qed.
Lemma NoDup_ziota : forall k a, List.NoDup (ziota a k).
Proof.
  induction k as [|k IH]; intros a; cbn; constructor; [|apply IH]. rewrite In_ziota. lia.
Qed.
Lemma length_ziota : forall k a, length (ziota a k) = k.
Proof. induction k; intros; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grows (s s' : astate) (c : Z) (fresh : list Z) : Prop :=
  as_cache s' = as_cache s /\ as_cache_inited s' = as_cache_inited s /\ as_chunks s' = as_chunks s
  /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s /\ as_sec s' = as_sec s /\ as_ptr_committed s' = as_ptr_committed s
  /\ as_keys s' = as_keys s /\ as_frames s' = as_frames s /\ as_ndepot_ins s' = as_ndepot_ins s
  /\ (forall c', c' <> c -> get_region s' c' = get_region s c')
  /\ rg_alloc_user (get_region s c) <= rg_alloc_user (get_region s' c)
  /\ rg_free (get_region s' c) = rg_free (get_region s c) ++ fresh
  /\ (forall x, In x fresh -> rg_alloc_user (get_region s c) <= 16 * x).

Lemma carved_mono : forall s s' c a,
  rg_alloc_user (get_region s c) <= rg_alloc_user (get_region s' c) -> carved E s c a -> carved E s' c a.
Proof.
  intros s s' c a LE (k & Hk & Ha & Hb). exists k. unfold region_of in *. split; [exact Hk|]. split; [exact Ha|]. lia.
Qed.

Lemma carved_below : forall s c a, 1 <= c <= kLargestClassID -> carved E s c a ->
  16 * compact_of_chunk (ae_space_beg E) c a + class_size c <= rg_alloc_user (get_region s c).
Proof.
  intros s c a Hc (k & Hk & -> & Hb). unfold compact_of_chunk, region_of in *.
  pose proof (class_size_mod c Hc) as [M R].
  replace (region_beg (ae_space_beg E) c + k * class_size c - region_beg (ae_space_beg E) c) with (k * class_size c) by lia.
  assert ((k * class_size c) mod 16 = 0).
  { rewrite Z.mul_mod by lia. replace (class_size c mod 16) with 0; [rewrite Z.mul_0_r; reflexivity|].
    symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in M; [|lia]. destruct M as [q Hq]. exists (2*q). lia. }
  rewrite <- (Z.div_exact (k * class_size c) 16) in H by lia. nia.
Qed.

Lemma AWf_frame_grows : forall s s' c fresh,
  1 <= c <= kLargestClassID -> as_cache_inited s = true ->
  grows s s' c fresh -> wf_regions E s' -> AWF s -> AWF s'.
Proof.
  intros s s' c fresh Hc HI (HC & HI' & HK & HT & HG & HS & HP & HKy & HF & HN & OTH & LE & FR & FRESH) WR' H.
  destruct H as (WE & WR & WC & WCH & WQ & WS & WD).
  assert (CARV : forall c' a, carved E s c' a -> carved E s' c' a).
  { intros c' a Hca. destruct (Z.eq_dec c' c) as [->|NE].
    - eapply carved_mono; [exact LE| exact Hca].
    - eapply carved_mono; [|exact Hca]. rewrite (OTH c' NE). lia. }
  assert (NFREE : forall c' a, 1 <= c' <= kLargestClassID -> carved E s c' a -> ~ in_free E s c' a -> ~ in_free E s' c' a).
  { intros c' a Hc' Hca NI. unfold in_free, region_of in *. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite FR. rewrite in_app_iff. intros [X|X]; [exact (NI X)|].
      pose proof (carved_below s c a Hc Hca). specialize (FRESH _ X). pose proof (class_size_mod c Hc). lia.
    - rewrite (OTH c' NE). exact NI. }
  split; [exact WE|]. split; [exact WR'|]. split; [|split; [|split; [|split]]].
  - destruct WC as (C1 & C2 & C3). unfold wf_cache. rewrite HC, HI'. split; [exact C1|]. split; [intros X; rewrite X in HI; discriminate|].
    intros c' Hc'. unfold get_cache. rewrite HC. destruct (C3 c' Hc') as (A & B & C). split; [exact A|]. split; [exact B|].
    intros x Hx. destruct (C x Hx) as (D9 & E0 & F). split; [apply CARV; exact D9|]. split; [exact E0|].
    assert (NI : ~ in_free E s' c' (chunk_of_compact (ae_space_beg E) c' x)).
    { apply NFREE; [exact Hc'| exact D9|]. unfold in_free, region_of. rewrite compact_chunk_id. exact F. }
    unfold in_free, region_of in NI. rewrite compact_chunk_id in NI. exact NI.
  - destruct WCH as (K1 & K2). unfold wf_chunks. rewrite HK. split; [|exact K2].
    intros cb cm Hcm. destruct (K1 cb cm Hcm) as (A & B & C & D0 & E0). unfold wf_chunk.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    + destruct (cm_prim cm) as [c'|].
      * destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
        assert (Hc' : 1 <= c' <= kLargestClassID) by (subst c'; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1); lia).
        split; [exact D1|]. split; [exact D2|]. split; [apply CARV; exact D3|].
        split; [apply NFREE; assumption|]. split; [unfold in_cache, get_cache; rewrite HC; exact D5|].
        unfold is_batch, all_batches. rewrite HT, HG. exact D6.
      * rewrite HS. exact D0.
    + unfold all_batches. rewrite ?HT, ?HG. exact E0.
  - destruct WQ as (Q1 & QD & Q2 & Q3). unfold wf_quarantine, all_batches. rewrite HT, HG.
    split; [|split; [|split; [exact Q2| exact Q3]]].
    + intros b Hb. destruct (Q1 b Hb) as [WB NB]. split; [|exact NB].
      destruct WB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). unfold wf_batch.
      split; [apply CARV; exact B1|]. split; [apply NFREE; [unfold kBatchClass, kLargestClassID; lia| exact B1| exact B2]|].
      split; [unfold in_cache, get_cache; rewrite HC; exact B3|]. split; [unfold is_chunk_block; rewrite HK; exact B4|].
      split; [exact B5|]. split; [unfold chunk_used_size; rewrite HK; exact B6|]. split; [exact B7|].
      unfold chunk_used_size. rewrite HK. exact B8.
    + intros b Hb. destruct (QD b Hb) as (B1 & B2 & B3 & B4 & B7). unfold wf_dbatch.
      split; [apply CARV; exact B1|]. split; [apply NFREE; [unfold kBatchClass, kLargestClassID; lia| exact B1| exact B2]|].
      split; [unfold in_cache, get_cache; rewrite HC; exact B3|]. split; [unfold is_chunk_block; rewrite HK; exact B4| exact B7].
  - unfold wf_secondary, n_chunks. rewrite HS, HP. exact WS.
  - unfold wf_depot. rewrite HKy, HF, HN. exact WD.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma grows_refl : forall s c, grows s s c [].
Proof. intros s c. unfold grows. repeat split; try reflexivity; try lia. rewrite app_nil_r; reflexivity. intros x []. Qed.

Lemma ensure_free_array_space_spec : forall s0 c nf,
  1 <= c <= kLargestClassID -> 4 * nf <= kFreeArraySize ->
  AWF s0 -> as_cache_inited s0 = true -> rg_num_freed (get_region s0 c) <= nf ->
  hoare (fun s => s = s0) (ensure_free_array_space E c nf)
        (fun s' ok => AWF s' /\ as_cache_inited s' = true
                      /\ grows s0 s' c []
                      /\ rg_alloc_user (get_region s' c) = rg_alloc_user (get_region s0 c)
                      /\ rg_mapped_user (get_region s' c) = rg_mapped_user (get_region s0 c)
                      /\ rg_mapped_fa (get_region s0 c) <= rg_mapped_fa (get_region s' c)
                      /\ (ok = true -> 4 * nf <= rg_mapped_fa (get_region s' c))).
Proof.
  intros s0 c nf Hc Hnf WF HI HNF. unfold ensure_free_array_space. apply hoare_get_bind. intros s ->.
  match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:HB end.
  - apply Z.ltb_lt in HB.
    unfold acheck. match goal with |- hoare _ (abind (if ?b then _ else _) _) _ => destruct b eqn:HB2 end.
    2:{ exfalso. apply Z.leb_gt in HB2. unfold kFreeArraySize, kFreeArrayMapSize in *.
        pose proof (round_up_lt (4 * nf) (2^18) ltac:(lia)).
        assert (round_up (4 * nf) (2^18) mod 2^18 = 0) by (apply round_up_mod; lia).
        nia. }
    apply Z.leb_le in HB2.
    eapply hoare_bind with (Q := fun s1 _ => s1 = s0); [apply hoare_ret; intros s1 ->; reflexivity|]. intros [].
    eapply hoare_bind with (Q := fun s1 _ => s1 = s0); [apply call_mmap_fixed_frame|].
    intros ok. apply hoare_pre. intros s1 ->. destruct ok.
    + apply hoare_upd_bind. apply hoare_ret. intros s' (s1 & -> & ->).
      set (r0 := get_region s0 c).
      assert (GE : 4 * nf <= round_up (4 * nf) kFreeArrayMapSize) by (apply round_up_ge; reflexivity).
      assert (GR : grows s0 (upd_ts (ts_on_mmap (round_up (4 * nf) kFreeArrayMapSize - rg_mapped_fa r0))
                               (set_region c (mkRegion (rg_mapped_user r0) (rg_alloc_user r0) (rg_free r0) (round_up (4 * nf) kFreeArrayMapSize)
                                                       (rg_n_allocated r0) (rg_n_freed r0)) s0)) c []).
      { unfold grows. repeat split; try reflexivity.
        - intros c' NE. rewrite get_region_upd_ts, get_set_region_ne by auto. reflexivity.
        - rewrite get_region_upd_ts, get_set_region_eq. cbn. subst r0. lia.
        - rewrite get_region_upd_ts, get_set_region_eq. cbn. subst r0. rewrite app_nil_r. reflexivity.
        - intros x []. }
      split; [|split; [cbn; exact HI| split; [exact GR|]]].
      2:{ rewrite !get_region_upd_ts, !get_set_region_eq. cbn. subst r0. repeat split; try reflexivity; try lia. }
      eapply AWf_frame_grows; [exact Hc| exact HI| exact GR| |exact WF].
      destruct WF as (WE & (R1 & R2) & _).
      split.
      * rewrite as_regions_upd_ts_set_region. intros c0 r1 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|].
        rewrite lookup_insert_ne in Hl by auto. eapply R1; exact Hl.
      * intros c0 Hc0. cbn zeta. destruct (Z.eq_dec c c0) as [<-|NE].
        -- unfold region_of. rewrite get_region_upd_ts, get_set_region_eq. cbn.
           specialize (R2 c Hc). unfold region_of in R2. fold r0 in R2. cbn zeta in R2.
           destruct R2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
           unfold rg_num_freed in *.
           assert (P5 : 0 <= round_up (4 * nf) kFreeArrayMapSize) by lia.
           assert (P6 : round_up (4 * nf) kFreeArrayMapSize mod kFreeArrayMapSize = 0) by (apply round_up_mod; reflexivity).
           assert (P8 : 4 * Z.of_nat (length (rg_free r0)) <= round_up (4 * nf) kFreeArrayMapSize). { subst r0. clear -HNF GE. lia. }
           match goal with |- _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ ?G /\ _ /\ _ => assert (P10 : G) end.
           { intros x Hx. destruct (A10 x Hx) as [Cx Mx]. split; [|exact Mx].
             unfold carved, region_of in *. rewrite get_region_upd_ts, get_set_region_eq. cbn. exact Cx. }
           exact (conj A1 (conj A2 (conj A3 (conj A4 (conj P5 (conj P6 (conj HB2 (conj P8 (conj A9 (conj P10 (conj A11 A12))))))))))).
        -- unfold region_of. rewrite get_region_upd_ts, get_set_region_ne by exact NE.
           specialize (R2 c0 Hc0). unfold region_of in R2.
           destruct R2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
           refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj _ (conj A11 A12))))))))))).
           intros x Hx. destruct (A10 x Hx) as [Cx Mx]. split; [|exact Mx].
           unfold carved, region_of in *. rewrite get_region_upd_ts, get_set_region_ne by exact NE. exact Cx.
    + apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [exact HI|]. split; [apply grows_refl|].
      repeat split; try reflexivity; try lia; try discriminate.
  - apply Z.ltb_ge in HB. apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [exact HI|]. split; [apply grows_refl|].
    repeat split; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_mul_le : forall a b, 0 < b -> 0 <= a -> (a / b) * b <= a.
Proof. intros a b Hb Ha. rewrite Z.mul_comm. apply Z.mul_div_le; lia. Qed.

Lemma hint_size_bound : forall c, 1 <= c <= 30 -> hint c * class_size c <= 65536 /\ 0 <= hint c.
Proof.
  intros c Hc. assert (E0 : exists k, (k < 31)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E0 as (k & Hk & ->). do 31 (destruct k as [|k]; [vm_compute; split; [discriminate|discriminate] || (cbv; lia) |]). lia.
Qed.

Lemma round_up_small : forall x a, 0 < a -> 0 < x <= a -> round_up x a = a.
Proof.
  intros x a Ha Hx. pose proof (round_up_ge x a Ha). pose proof (round_up_lt x a Ha).
  pose proof (round_up_mod x a Ha). apply Z.mod_divide in H1; [|lia]. destruct H1 as [q Hq].
  rewrite Hq in *. assert (q = 1) by nia. subst q. lia.
Qed.

Lemma mod_add_multiple : forall a b m, 0 < m -> a mod m = 0 -> b mod m = 0 -> (a + b) mod m = 0.
Proof. intros. rewrite Z.add_mod by lia. rewrite H0, H1. reflexivity. Qed.

Lemma as_regions_set3 : forall h f c r s, as_regions (upd_cache_mapped h (upd_ts f (set_region c r s))) = <[c := r]> (as_regions s).
Proof. reflexivity. Qed.
Lemma as_regions_set_region : forall c r s, as_regions (set_region c r s) = <[c := r]> (as_regions s).
Proof. reflexivity. Qed.
End WF.
End RC__2.
