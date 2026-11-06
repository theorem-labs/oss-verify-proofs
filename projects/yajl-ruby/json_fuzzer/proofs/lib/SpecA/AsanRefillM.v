(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanHoare AsanWf1 AsanRealloc AsanRepRefill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RM.
Variable E : aenv.

(* [comment removed for export] *)
Definition popf (c : Z) (a b : astate) : Prop :=
     as_cache_inited b = as_cache_inited a /\ as_cache b = as_cache a /\ as_cache_stale b = as_cache_stale a /\ as_cache_allocated b = as_cache_allocated a
  /\ as_ptr_committed b = as_ptr_committed a /\ as_sec b = as_sec a /\ as_sec_stale b = as_sec_stale a /\ as_sec_stats b = as_sec_stats a
  /\ as_glob_allocated b = as_glob_allocated a /\ as_glob_mapped b = as_glob_mapped a /\ as_oom b = as_oom a
  /\ as_chunks b = as_chunks a /\ as_dead b = as_dead a /\ as_tq b = as_tq a /\ as_gq b = as_gq a
  /\ as_keys b = as_keys a /\ as_frames b = as_frames a /\ as_ia_inited b = as_ia_inited a /\ as_residue b = as_residue a
  /\ as_nprim_ever b = as_nprim_ever a /\ as_node_blocks b = as_node_blocks a /\ as_store_blocks b = as_store_blocks a
  /\ as_store_stored b = as_store_stored a /\ as_ndepot_ins b = as_ndepot_ins a /\ as_everc b = as_everc a
  /\ (forall c', c' <> c -> get_region b c' = get_region a c')
  /\ ts_nomap_agree (as_ts a) (as_ts b).

Lemma popf_refl : forall c a, popf c a a.
Proof. intros c a. unfold popf, ts_nomap_agree. repeat split; reflexivity. Qed.
Lemma ts_nomap_agree_trans : forall t u v, ts_nomap_agree t u -> ts_nomap_agree u v -> ts_nomap_agree t v.
Proof. intros t u v A B. unfold ts_nomap_agree in *. decompose [and] A. decompose [and] B. repeat split; congruence. Qed.
Lemma popf_trans : forall c a b d, popf c a b -> popf c b d -> popf c a d.
Proof.
  intros c a b d A B. unfold popf in *.
  destruct A as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?& GA & TA).
  destruct B as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?& GB & TB).
  repeat (split; [congruence|]). split; [intros c' NE; rewrite (GB c' NE), (GA c' NE); reflexivity| eapply ts_nomap_agree_trans; eassumption].
Qed.

Lemma popf_set_region : forall c r a, popf c a (set_region c r a).
Proof.
  intros c r a. unfold popf, ts_nomap_agree. destruct a; cbn. repeat split; try reflexivity.
  intros c' NE. unfold get_region. cbn. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma popf_upd_ts_mmap : forall c sz a, popf c a (upd_ts (ts_on_mmap sz) a).
Proof.
  intros c sz a. unfold popf, ts_nomap_agree. destruct a as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ts ? ? ? ? ? ? ?]; destruct ts; cbn. repeat split; reflexivity.
Qed.
Lemma popf_upd_cache_mapped : forall c f a, popf c a (upd_cache_mapped f a).
Proof. intros c f a. unfold popf, ts_nomap_agree. destruct a; cbn. repeat split; reflexivity. Qed.

Lemma popf_call_mmap_fixed : forall c addr len, monoW (popf c) (call_mmap_fixed addr len).
Proof.
  intros c addr len. unfold call_mmap_fixed. hw (popf_refl c) (popf_trans c).
Qed.
Lemma popf_ensure : forall c nf, monoW (popf c) (ensure_free_array_space E c nf).
Proof.
  intros c nf. unfold ensure_free_array_space. hw (popf_refl c) (popf_trans c); try apply popf_call_mmap_fixed.
  intros s1. eapply popf_trans; [apply popf_set_region| apply popf_upd_ts_mmap].
Qed.
Lemma popf_populate : forall c req, monoW (popf c) (populate_free_array E c req).
Proof.
  intros c req. unfold populate_free_array. hw (popf_refl c) (popf_trans c); try apply popf_call_mmap_fixed; try apply popf_ensure.
  - intros s1. eapply popf_trans; [| apply popf_upd_cache_mapped]. eapply popf_trans; [apply popf_set_region| apply popf_upd_ts_mmap].
  - intros s9. apply popf_set_region.
Qed.

(* [comment removed for export] *)
Definition pop_lb (c mu0 mfa0 : Z) (a : astate) : Prop := mu0 <= rg_mapped_user (get_region a c) /\ mfa0 <= rg_mapped_fa (get_region a c).

Lemma round_up_ge : forall x k, 0 < k -> x <= round_up x k.
Proof. intros x k Hk. unfold round_up. Z.div_mod_to_equations. nia. Qed.

Lemma pop_lb_call_mmap_fixed : forall c mu0 mfa0 addr len, presW (pop_lb c mu0 mfa0) (call_mmap_fixed addr len).
Proof.
  intros. unfold call_mmap_fixed. apply presW_bind; [apply presW_call|]. intros [r|e]; [destruct (r =? addr)| destruct (e =? ENOMEM)];
    first [apply presW_ret| apply presW_undef].
Qed.
Lemma pop_lb_ensure : forall c mu0 mfa0 nf, presW (pop_lb c mu0 mfa0) (ensure_free_array_space E c nf).
Proof.
  intros c mu0 mfa0 nf. unfold ensure_free_array_space. apply presW_get_bind. intros s [L1 L2].
  match goal with |- presW _ (if ?b then _ else _) => destruct b eqn:HB end; [| apply presW_ret]. apply Z.ltb_lt in HB.
  apply presW_bind; [apply presW_check|]. intros _. apply presW_bind; [apply pop_lb_call_mmap_fixed|]. intros ok. destruct ok; [| apply presW_ret].
  apply presW_bind; [| intros; apply presW_ret]. apply presW_upd. intros s' [M1 M2]. unfold pop_lb.
  rewrite get_region_upd_ts, get_set_region_eq. cbn. split; [exact L1|].
  pose proof (round_up_ge (4 * nf) kFreeArrayMapSize ltac:(unfold kFreeArrayMapSize; lia)). lia.
Qed.
Lemma pop_lb_populate : forall c mu0 mfa0 req, 0 <= req -> 1 <= c <= kLargestClassID -> presW (pop_lb c mu0 mfa0) (populate_free_array E c req).
Proof.
  intros c mu0 mfa0 req Hreq Hc. pose proof (class_size_mod c Hc) as [_ CS]. unfold populate_free_array. apply presW_get_bind. intros s [L1 L2].
  apply presW_bind.
  { match goal with |- presW _ (if ?b then _ else _) => destruct b eqn:HB end; [| apply presW_ret]. apply Z.ltb_lt in HB.
    apply presW_bind; [apply presW_check|]. intros _. apply presW_bind; [apply pop_lb_call_mmap_fixed|]. intros ok. destruct ok; [| apply presW_ret].
    apply presW_bind; [| intros; apply presW_ret]. apply presW_upd. intros s' [M1 M2]. unfold pop_lb.
    rewrite get_region_upd_cache_mapped, get_region_upd_ts, get_set_region_eq. cbn. split; [| exact L2].
    pose proof (round_up_ge (rg_alloc_user (get_region s c) + req * class_size c - rg_mapped_user (get_region s c)) kUserMapSize ltac:(unfold kUserMapSize; lia)).
    clear -H L1 HB. lia. }
  intros ok1. destruct (negb ok1); [apply presW_ret|]. apply presW_get_bind. intros s1 [K1 K2].
  apply presW_bind; [apply pop_lb_ensure|]. intros ok2. destruct (negb ok2); [apply presW_ret|]. apply presW_get_bind. intros s2 [J1 J2].
  apply presW_bind; [| intros; apply presW_ret]. apply presW_upd. intros s' [M1 M2]. unfold pop_lb. rewrite get_set_region_eq. cbn. split; assumption.
Qed.

(* [comment removed for export] *)
Definition gfa_keep (c n : Z) (a1 : astate) : nat := (length (rg_free (get_region a1 c)) - Z.to_nat n)%nat.
Definition gfa_hi (c n : Z) (a1 : astate) : list Z := skipn (gfa_keep c n a1) (rg_free (get_region a1 c)).
Definition gfa_reg (c n : Z) (a1 : astate) : region :=
  let r1 := get_region a1 c in
  mkRegion (rg_mapped_user r1) (rg_alloc_user r1) (firstn (gfa_keep c n a1) (rg_free r1)) (rg_mapped_fa r1) (rg_n_allocated r1 + n) (rg_n_freed r1).
Definition gfa_fin (c n : Z) (a1 : astate) : astate := set_region c (gfa_reg c n a1) a1.
Definition refill_fin (c n : Z) (a1 : astate) : astate :=
  let l := gfa_hi c n a1 in
  upd_cache_stale (fun st => <[c := fold_right (fun i mm => delete i mm) (match st !! c with Some mm => mm | None => ∅ end)
                                           (map Z.of_nat (seq 0 (length l)))]> st)
                  (set_cache c l (gfa_fin c n a1)).

Section FIN.
Variables (c n : Z) (a1 : astate).
#[warnings="-notation-for-abbreviation"] Notation a' := (refill_fin c n a1).
Ltac fld := unfold refill_fin, gfa_fin; destruct a1; reflexivity.
Lemma fin_cache_inited : as_cache_inited a' = as_cache_inited a1. Proof. fld. Qed.
Lemma fin_cache_allocated : as_cache_allocated a' = as_cache_allocated a1. Proof. fld. Qed.
Lemma fin_cache_mapped : as_cache_mapped a' = as_cache_mapped a1. Proof. fld. Qed.
Lemma fin_ptr : as_ptr_committed a' = as_ptr_committed a1. Proof. fld. Qed.
Lemma fin_sec : as_sec a' = as_sec a1. Proof. fld. Qed.
Lemma fin_sec_stale : as_sec_stale a' = as_sec_stale a1. Proof. fld. Qed.
Lemma fin_sec_stats : as_sec_stats a' = as_sec_stats a1. Proof. fld. Qed.
Lemma fin_glob_allocated : as_glob_allocated a' = as_glob_allocated a1. Proof. fld. Qed.
Lemma fin_glob_mapped : as_glob_mapped a' = as_glob_mapped a1. Proof. fld. Qed.
Lemma fin_oom : as_oom a' = as_oom a1. Proof. fld. Qed.
Lemma fin_chunks : as_chunks a' = as_chunks a1. Proof. fld. Qed.
Lemma fin_dead : as_dead a' = as_dead a1. Proof. fld. Qed.
Lemma fin_tq : as_tq a' = as_tq a1. Proof. fld. Qed.
Lemma fin_gq : as_gq a' = as_gq a1. Proof. fld. Qed.
Lemma fin_keys : as_keys a' = as_keys a1. Proof. fld. Qed.
Lemma fin_frames : as_frames a' = as_frames a1. Proof. fld. Qed.
Lemma fin_ia : as_ia_inited a' = as_ia_inited a1. Proof. fld. Qed.
Lemma fin_ts : as_ts a' = as_ts a1. Proof. fld. Qed.
Lemma fin_residue : as_residue a' = as_residue a1. Proof. fld. Qed.
Lemma fin_nprim : as_nprim_ever a' = as_nprim_ever a1. Proof. fld. Qed.
Lemma fin_node_blocks : as_node_blocks a' = as_node_blocks a1. Proof. fld. Qed.
Lemma fin_store_blocks : as_store_blocks a' = as_store_blocks a1. Proof. fld. Qed.
Lemma fin_store_stored : as_store_stored a' = as_store_stored a1. Proof. fld. Qed.
Lemma fin_ndepot : as_ndepot_ins a' = as_ndepot_ins a1. Proof. fld. Qed.
Lemma fin_everc : as_everc a' = as_everc a1. Proof. fld. Qed.
Lemma fin_regions : as_regions a' = <[c := gfa_reg c n a1]> (as_regions a1). Proof. fld. Qed.
Lemma fin_cache : as_cache a' = <[c := gfa_hi c n a1]> (as_cache a1). Proof. fld. Qed.
Lemma fin_get_region : forall c', get_region a' c' = if decide (c' = c) then gfa_reg c n a1 else get_region a1 c'.
Proof.
  intros c'. unfold get_region at 1. rewrite fin_regions. destruct (decide (c' = c)) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma fin_get_cache : forall c', get_cache a' c' = if decide (c' = c) then gfa_hi c n a1 else get_cache a1 c'.
Proof.
  intros c'. unfold get_cache at 1. rewrite fin_cache. destruct (decide (c' = c)) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma tq_bytes_fin : tq_bytes a' = tq_bytes a1. Proof. fld. Qed.
Lemma gq_bytes_fin : gq_bytes a' = gq_bytes a1. Proof. fld. Qed.
Lemma n_chunks_fin : n_chunks a' = n_chunks a1. Proof. fld. Qed.
End FIN.

(* [comment removed for export] *)
Lemma arun_aget : forall s orc, arun 0%nat (aget s) orc = Some (s, ONorm s, [], orc).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma arun_gfa_tail : forall c n a1 orc, n <= rg_num_freed (get_region a1 c) ->
  arun 0%nat ((s1 <- aget ;;
               acheck (n <=? rg_num_freed (get_region s1 c)) 229 ;;;
               aupd (set_region c (mkRegion (rg_mapped_user (get_region s1 c)) (rg_alloc_user (get_region s1 c))
                                            (firstn (length (rg_free (get_region s1 c)) - Z.to_nat n) (rg_free (get_region s1 c)))
                                            (rg_mapped_fa (get_region s1 c)) (rg_n_allocated (get_region s1 c) + n) (rg_n_freed (get_region s1 c)))) ;;;
               aret (Some (skipn (length (rg_free (get_region s1 c)) - Z.to_nat n) (rg_free (get_region s1 c))))) a1) orc
  = Some (gfa_fin c n a1, ONorm (Some (gfa_hi c n a1)), [], orc).
Proof.
  intros c n a1 orc Hn. unfold abind, aget, acheck. cbn [sbind fst snd].
  replace (n <=? rg_num_freed (get_region a1 c)) with true by (symmetry; apply Z.leb_le; exact Hn).
  reflexivity.
Qed.

Lemma arun_refill_direct : forall c a orc, let n := hint c in
  n <= rg_num_freed (get_region a c) ->
  arun 0%nat (refill E c a) orc = Some (refill_fin c n (upd_cache_inited true a), ONorm true, [], orc).
Proof.
  intros c a orc n Hn. unfold refill, init_cache, get_from_allocator. unfold abind. cbn [sbind aupd aget fst snd]. rewrite get_region_upd_cache_inited. fold n.
  replace (rg_num_freed (get_region a c) <? n) with false by (symmetry; apply Z.ltb_ge; exact Hn). cbn [sbind aret fst snd negb]. unfold acheck.
  rewrite get_region_upd_cache_inited. replace (n <=? rg_num_freed (get_region a c)) with true by (symmetry; apply Z.leb_le; exact Hn).
  cbn [sbind aret fst snd negb]. unfold refill_fin, gfa_fin, gfa_hi, gfa_reg, gfa_keep. rewrite !get_region_upd_cache_inited. reflexivity.
Qed.

Lemma arun_refill_pop : forall c a fuel orc a1 evs orc', let n := hint c in let nf := rg_num_freed (get_region a c) in
  nf < n ->
  arun fuel (populate_free_array E c (n - nf) (upd_cache_inited true a)) orc = Some (a1, ONorm true, evs, orc') ->
  n <= rg_num_freed (get_region a1 c) ->
  arun fuel (refill E c a) orc = Some (refill_fin c n a1, ONorm true, evs, orc').
Proof.
  intros c a fuel orc a1 evs orc' n nf LT RUN Hn. unfold refill, init_cache, get_from_allocator. unfold abind. cbn [sbind aupd aget fst snd].
  rewrite get_region_upd_cache_inited. fold nf. fold n.
  replace (nf <? n) with true by (symmetry; apply Z.ltb_lt; exact LT).
  pose proof (arun_gfa_tail c n a1 orc' Hn) as G. unfold abind in G.
  lazymatch goal with |- arun _ (sbind (sbind ?t ?k1) ?k2) _ = _ =>
    eassert (X1 : arun (fuel + 0)%nat (sbind t k1) orc = Some (gfa_fin c n a1, ONorm (Some (gfa_hi c n a1)), evs ++ [], orc'));
    [ eapply (arun_sbind t k1 fuel 0); [exact RUN| cbn [negb]; exact G]
    | eassert (X2 : arun (fuel + 0 + 0)%nat (sbind (sbind t k1) k2) orc = Some (refill_fin c n a1, ONorm true, (evs ++ []) ++ [], orc'));
      [ eapply (arun_sbind (sbind t k1) k2 (fuel + 0)%nat 0); [exact X1| reflexivity]
      | rewrite !app_nil_r, !Nat.add_0_r in X2; exact X2 ] ]
  end.
Qed.

End RM.
End RC__1.
