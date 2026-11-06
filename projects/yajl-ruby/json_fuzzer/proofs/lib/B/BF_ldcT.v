(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA MmStep StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed XB_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf9 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanRepX AsanFrame AsanRealloc AsanRefillMB AsanRepEnqB AsanRepRefillB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_poison BF_free_kit BF_qkit BF_mmfix1 BF_rarmap BF_unwind BF_free6 BF_free7 BF_free8 BF_free9 BF_free10 BF_free11 B_policy5 B_slack5 B_budget5 B_mmchk5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 B_bframe BF_alloc_iface BF_populate_iface BF_refill_iface BF_tkit BF_ainv_kit BF_statics BF_popdefs BF_pop0 BF_popT BF_caT BF_refill_room BF_refillT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma arun_bind_l : forall {R S} (mm : AM R) (k : R -> AM S) s0 f orc s1 r res,
  arun 0%nat (mm s0) orc = Some (s1, ONorm r, [], orc) -> arun f (k r s1) orc = Some res -> arun f (abind mm k s0) orc = Some res.
Proof.
  intros R S mm k s0 f orc s1 r [[[s2 o2] evs2] orc2] H1 H2.
  pose proof (arun_abind mm k s0 0%nat f orc s1 r [] orc s2 o2 evs2 orc2 H1 H2) as X. exact X.
Qed.
Lemma arun_bind_r : forall {R S} (mm : AM R) (k : R -> AM S) s0 f orc s1 r evs orc1 s2 o2 orc2,
  arun f (mm s0) orc = Some (s1, ONorm r, evs, orc1) -> arun 0%nat (k r s1) orc1 = Some (s2, o2, [], orc2) ->
  arun f (abind mm k s0) orc = Some (s2, o2, evs, orc2).
Proof.
  intros R S mm k s0 f orc s1 r evs orc1 s2 o2 orc2 H1 H2.
  pose proof (arun_abind mm k s0 f 0%nat orc s1 r evs orc1 s2 o2 [] orc2 H1 H2) as X. rewrite Nat.add_0_r, app_nil_r in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Model.
Variable E : aenv.
#[local] Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
Definition dr_keep (a : astate) (c : Z) : nat := (length (get_cache a c) - Z.to_nat (hint c))%nat.
Definition dr_st (c : Z) (a : astate) : astate := set_cache c (firstn (dr_keep a c) (get_cache a c)) a.
Definition dr_chunks (c : Z) (a : astate) : list Z := skipn (dr_keep a c) (get_cache a c).
(* [comment removed for export] *)
Definition rta_st (c : Z) (chunks : list Z) (a : astate) : astate :=
  let r := get_region a c in
  set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ chunks) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r + zlen chunks)) a.
(* [comment removed for export] *)
Definition push_st (c p : Z) (a : astate) : astate :=
  let l1 := get_cache a c in
  upd_cache_allocated (fun al => al - class_size c)
    (upd_cache_stale (fun st => <[c := delete (zlen l1) (match st !! c with Some mm => mm | None => ∅ end)]> st)
       (set_cache c (l1 ++ [compact_of_chunk SB c p]) a)).

(* [comment removed for export] *)
Lemma push_as_chunks : forall c p a, as_chunks (push_st c p a) = as_chunks a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_dead : forall c p a, as_dead (push_st c p a) = as_dead a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_tq : forall c p a, as_tq (push_st c p a) = as_tq a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_gq : forall c p a, as_gq (push_st c p a) = as_gq a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_sec : forall c p a, as_sec (push_st c p a) = as_sec a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_ptr_committed : forall c p a, as_ptr_committed (push_st c p a) = as_ptr_committed a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_sec_stats : forall c p a, as_sec_stats (push_st c p a) = as_sec_stats a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_sec_stale : forall c p a, as_sec_stale (push_st c p a) = as_sec_stale a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_glob_allocated : forall c p a, as_glob_allocated (push_st c p a) = as_glob_allocated a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_glob_mapped : forall c p a, as_glob_mapped (push_st c p a) = as_glob_mapped a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_oom : forall c p a, as_oom (push_st c p a) = as_oom a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_nprim_ever : forall c p a, as_nprim_ever (push_st c p a) = as_nprim_ever a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_residue : forall c p a, as_residue (push_st c p a) = as_residue a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_everc : forall c p a, as_everc (push_st c p a) = as_everc a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_ndepot_ins : forall c p a, as_ndepot_ins (push_st c p a) = as_ndepot_ins a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_node_blocks : forall c p a, as_node_blocks (push_st c p a) = as_node_blocks a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_store_blocks : forall c p a, as_store_blocks (push_st c p a) = as_store_blocks a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_keys : forall c p a, as_keys (push_st c p a) = as_keys a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_frames : forall c p a, as_frames (push_st c p a) = as_frames a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_store_stored : forall c p a, as_store_stored (push_st c p a) = as_store_stored a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_cache_inited : forall c p a, as_cache_inited (push_st c p a) = as_cache_inited a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_cache_mapped : forall c p a, as_cache_mapped (push_st c p a) = as_cache_mapped a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_ia_inited : forall c p a, as_ia_inited (push_st c p a) = as_ia_inited a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_ts : forall c p a, as_ts (push_st c p a) = as_ts a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_as_regions : forall c p a, as_regions (push_st c p a) = as_regions a. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_allocated : forall c p a, as_cache_allocated (push_st c p a) = as_cache_allocated a - class_size c. Proof. intros c p a; destruct a; reflexivity. Qed.
Lemma push_get_region : forall c p a c', get_region (push_st c p a) c' = get_region a c'. Proof. intros c p a c'; destruct a; reflexivity. Qed.
Lemma push_get_cache_eq : forall c p a, get_cache (push_st c p a) c = get_cache a c ++ [compact_of_chunk SB c p].
Proof. intros c p a. unfold push_st. cbv zeta. destruct a; unfold get_cache; cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma push_get_cache_ne : forall c p a c', c <> c' -> get_cache (push_st c p a) c' = get_cache a c'.
Proof. intros c p a c' NE. unfold push_st. cbv zeta. destruct a; unfold get_cache; cbn. rewrite lookup_insert_ne by exact NE. reflexivity. Qed.
Lemma dr_as_chunks : forall c a, as_chunks (dr_st c a) = as_chunks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_dead : forall c a, as_dead (dr_st c a) = as_dead a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_tq : forall c a, as_tq (dr_st c a) = as_tq a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_gq : forall c a, as_gq (dr_st c a) = as_gq a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_sec : forall c a, as_sec (dr_st c a) = as_sec a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_ptr_committed : forall c a, as_ptr_committed (dr_st c a) = as_ptr_committed a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_sec_stats : forall c a, as_sec_stats (dr_st c a) = as_sec_stats a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_sec_stale : forall c a, as_sec_stale (dr_st c a) = as_sec_stale a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_glob_allocated : forall c a, as_glob_allocated (dr_st c a) = as_glob_allocated a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_glob_mapped : forall c a, as_glob_mapped (dr_st c a) = as_glob_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_oom : forall c a, as_oom (dr_st c a) = as_oom a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_nprim_ever : forall c a, as_nprim_ever (dr_st c a) = as_nprim_ever a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_residue : forall c a, as_residue (dr_st c a) = as_residue a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_everc : forall c a, as_everc (dr_st c a) = as_everc a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_ndepot_ins : forall c a, as_ndepot_ins (dr_st c a) = as_ndepot_ins a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_node_blocks : forall c a, as_node_blocks (dr_st c a) = as_node_blocks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_store_blocks : forall c a, as_store_blocks (dr_st c a) = as_store_blocks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_keys : forall c a, as_keys (dr_st c a) = as_keys a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_frames : forall c a, as_frames (dr_st c a) = as_frames a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_store_stored : forall c a, as_store_stored (dr_st c a) = as_store_stored a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_cache_inited : forall c a, as_cache_inited (dr_st c a) = as_cache_inited a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_cache_mapped : forall c a, as_cache_mapped (dr_st c a) = as_cache_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_ia_inited : forall c a, as_ia_inited (dr_st c a) = as_ia_inited a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_ts : forall c a, as_ts (dr_st c a) = as_ts a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_regions : forall c a, as_regions (dr_st c a) = as_regions a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_cache_allocated : forall c a, as_cache_allocated (dr_st c a) = as_cache_allocated a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_as_cache_stale : forall c a, as_cache_stale (dr_st c a) = as_cache_stale a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma dr_get_region : forall c a c', get_region (dr_st c a) c' = get_region a c'. Proof. intros c a c'; destruct a; reflexivity. Qed.
Lemma dr_get_cache_eq : forall c a, get_cache (dr_st c a) c = firstn (dr_keep a c) (get_cache a c).
Proof. intros c a. unfold dr_st. apply get_set_cache_eq. Qed.
Lemma dr_get_cache_ne : forall c a c', c <> c' -> get_cache (dr_st c a) c' = get_cache a c'.
Proof. intros c a c' NE. unfold dr_st. apply get_set_cache_ne. exact NE. Qed.
Lemma rta_as_chunks : forall c ch a, as_chunks (rta_st c ch a) = as_chunks a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_dead : forall c ch a, as_dead (rta_st c ch a) = as_dead a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_tq : forall c ch a, as_tq (rta_st c ch a) = as_tq a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_gq : forall c ch a, as_gq (rta_st c ch a) = as_gq a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_sec : forall c ch a, as_sec (rta_st c ch a) = as_sec a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_ptr_committed : forall c ch a, as_ptr_committed (rta_st c ch a) = as_ptr_committed a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_sec_stats : forall c ch a, as_sec_stats (rta_st c ch a) = as_sec_stats a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_sec_stale : forall c ch a, as_sec_stale (rta_st c ch a) = as_sec_stale a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_glob_allocated : forall c ch a, as_glob_allocated (rta_st c ch a) = as_glob_allocated a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_glob_mapped : forall c ch a, as_glob_mapped (rta_st c ch a) = as_glob_mapped a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_oom : forall c ch a, as_oom (rta_st c ch a) = as_oom a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_nprim_ever : forall c ch a, as_nprim_ever (rta_st c ch a) = as_nprim_ever a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_residue : forall c ch a, as_residue (rta_st c ch a) = as_residue a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_everc : forall c ch a, as_everc (rta_st c ch a) = as_everc a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_ndepot_ins : forall c ch a, as_ndepot_ins (rta_st c ch a) = as_ndepot_ins a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_node_blocks : forall c ch a, as_node_blocks (rta_st c ch a) = as_node_blocks a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_store_blocks : forall c ch a, as_store_blocks (rta_st c ch a) = as_store_blocks a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_keys : forall c ch a, as_keys (rta_st c ch a) = as_keys a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_frames : forall c ch a, as_frames (rta_st c ch a) = as_frames a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_store_stored : forall c ch a, as_store_stored (rta_st c ch a) = as_store_stored a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_cache_inited : forall c ch a, as_cache_inited (rta_st c ch a) = as_cache_inited a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_cache_mapped : forall c ch a, as_cache_mapped (rta_st c ch a) = as_cache_mapped a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_ia_inited : forall c ch a, as_ia_inited (rta_st c ch a) = as_ia_inited a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_ts : forall c ch a, as_ts (rta_st c ch a) = as_ts a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_cache : forall c ch a, as_cache (rta_st c ch a) = as_cache a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_cache_allocated : forall c ch a, as_cache_allocated (rta_st c ch a) = as_cache_allocated a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_as_cache_stale : forall c ch a, as_cache_stale (rta_st c ch a) = as_cache_stale a. Proof. intros c ch a; destruct a; reflexivity. Qed.
Lemma rta_get_cache : forall c ch a c', get_cache (rta_st c ch a) c' = get_cache a c'. Proof. intros c ch a c'; destruct a; reflexivity. Qed.
Lemma rta_get_region_eq : forall c ch a, get_region (rta_st c ch a) c = let r := get_region a c in mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ ch) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r + zlen ch).
Proof. intros c ch a. unfold rta_st. cbv zeta. apply get_set_region_eq. Qed.
Lemma rta_get_region_ne : forall c ch a c', c <> c' -> get_region (rta_st c ch a) c' = get_region a c'.
Proof. intros c ch a c' NE. unfold rta_st. cbv zeta. apply get_set_region_ne. exact NE. Qed.
Lemma fa_as_chunks : forall c a, as_chunks (st_fa c a) = as_chunks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_dead : forall c a, as_dead (st_fa c a) = as_dead a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_tq : forall c a, as_tq (st_fa c a) = as_tq a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_gq : forall c a, as_gq (st_fa c a) = as_gq a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_sec : forall c a, as_sec (st_fa c a) = as_sec a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_ptr_committed : forall c a, as_ptr_committed (st_fa c a) = as_ptr_committed a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_sec_stats : forall c a, as_sec_stats (st_fa c a) = as_sec_stats a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_sec_stale : forall c a, as_sec_stale (st_fa c a) = as_sec_stale a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_glob_allocated : forall c a, as_glob_allocated (st_fa c a) = as_glob_allocated a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_glob_mapped : forall c a, as_glob_mapped (st_fa c a) = as_glob_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_oom : forall c a, as_oom (st_fa c a) = as_oom a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_nprim_ever : forall c a, as_nprim_ever (st_fa c a) = as_nprim_ever a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_residue : forall c a, as_residue (st_fa c a) = as_residue a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_everc : forall c a, as_everc (st_fa c a) = as_everc a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_ndepot_ins : forall c a, as_ndepot_ins (st_fa c a) = as_ndepot_ins a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_node_blocks : forall c a, as_node_blocks (st_fa c a) = as_node_blocks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_store_blocks : forall c a, as_store_blocks (st_fa c a) = as_store_blocks a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_keys : forall c a, as_keys (st_fa c a) = as_keys a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_frames : forall c a, as_frames (st_fa c a) = as_frames a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_store_stored : forall c a, as_store_stored (st_fa c a) = as_store_stored a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_cache_inited : forall c a, as_cache_inited (st_fa c a) = as_cache_inited a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_cache_mapped : forall c a, as_cache_mapped (st_fa c a) = as_cache_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_ia_inited : forall c a, as_ia_inited (st_fa c a) = as_ia_inited a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_cache : forall c a, as_cache (st_fa c a) = as_cache a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_cache_allocated : forall c a, as_cache_allocated (st_fa c a) = as_cache_allocated a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_as_cache_stale : forall c a, as_cache_stale (st_fa c a) = as_cache_stale a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma fa_get_cache : forall c a c', get_cache (st_fa c a) c' = get_cache a c'. Proof. intros c a c'; destruct a; reflexivity. Qed.

Lemma upd_ci_id : forall a, as_cache_inited a = true -> upd_cache_inited true a = a.
Proof. intros a H. destruct a; cbn in H |- *. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_ldc_push : forall c p a orc, 1 <= c <= kLargestClassID -> as_cache_inited a = true ->
  zlen (get_cache a c) <> max_count c ->
  arun 0%nat (local_dealloc E c p a) orc = Some (push_st c p a, ONorm tt, [], orc).
Proof.
  intros c p a orc Hc CI NF. unfold local_dealloc, acheck.
  replace ((1 <=? c) && (c <? kNumClasses)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kNumClasses, kLargestClassID in *; lia).
  eapply arun_bind_l; [apply arun_aret|]. unfold init_cache.
  eapply arun_bind_l; [apply arun_aupd|]. rewrite (upd_ci_id a CI).
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta.
  replace (zlen (get_cache a c) =? max_count c) with false by (symmetry; apply Z.eqb_neq; exact NF).
  eapply arun_bind_l; [apply arun_aret|].
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. rewrite arun_aupd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma run_ldc_drain_nogrow : forall c p a orc, 1 <= c <= kLargestClassID -> as_cache_inited a = true ->
  zlen (get_cache a c) = max_count c ->
  let a1 := dr_st c a in let ch := dr_chunks c a in let r := get_region a c in
  4 * (rg_num_freed r + zlen ch) <= rg_mapped_fa r ->
  arun 0%nat (local_dealloc E c p a) orc = Some (push_st c p (rta_st c ch a1), ONorm tt, [], orc).
Proof.
  intros c p a orc Hc CI FULL. cbv zeta. intros ROOM. unfold local_dealloc, acheck.
  replace ((1 <=? c) && (c <? kNumClasses)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kNumClasses, kLargestClassID in *; lia).
  eapply arun_bind_l; [apply arun_aret|]. unfold init_cache.
  eapply arun_bind_l; [apply arun_aupd|]. rewrite (upd_ci_id a CI).
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. rewrite FULL, Z.eqb_refl.
  eapply arun_bind_l.
  { eapply arun_bind_l; [apply arun_aupd|]. fold (dr_keep a c). change (set_cache c (firstn (dr_keep a c) (get_cache a c)) a) with (dr_st c a).
    fold (dr_chunks c a). unfold return_to_allocator.
    eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta.
    eapply arun_bind_l.
    { unfold ensure_free_array_space. eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta.
      unfold dr_st at 1 2. rewrite get_region_set_cache.
      replace (rg_mapped_fa (get_region a c) <? 4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a))) with false by (symmetry; apply Z.ltb_ge; exact ROOM).
      apply arun_aret. }
    cbn [negb]. eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. apply arun_aupd. }
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. rewrite arun_aupd.
  unfold rta_st, dr_st. rewrite get_region_set_cache. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma run_ldc_drain_grant : forall c p a orc, 1 <= c <= kLargestClassID -> as_cache_inited a = true ->
  zlen (get_cache a c) = max_count c ->
  let a1 := dr_st c a in let ch := dr_chunks c a in let r := get_region a c in
  rg_mapped_fa r < 4 * (rg_num_freed r + zlen ch) -> 4 * (rg_num_freed r + zlen ch) <= rg_mapped_fa r + kFreeArrayMapSize ->
  0 <= rg_mapped_fa r -> rg_mapped_fa r mod kFreeArrayMapSize = 0 -> rg_mapped_fa r + kFreeArrayMapSize <= kFreeArraySize ->
  arun 1%nat (local_dealloc E c p a) (AnsOk (free_array SB c + rg_mapped_fa r) :: orc)
  = Some (push_st c p (rta_st c ch (st_fa c a1)), ONorm tt, [AEvMmap (free_array SB c + rg_mapped_fa r) kFreeArrayMapSize kProtRw kFlagsFixedRw], orc).
Proof.
  intros c p a orc Hc CI FULL. cbv zeta. intros GROW ONE MF0 MFM FAS. unfold local_dealloc, acheck.
  replace ((1 <=? c) && (c <? kNumClasses)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kNumClasses, kLargestClassID in *; lia).
  assert (NEWFA : round_up (4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a))) kFreeArrayMapSize = rg_mapped_fa (get_region a c) + kFreeArrayMapSize).
  { unfold kFreeArrayMapSize in *. apply (roundup_next E); [exact MF0| exact MFM| split; [exact GROW| exact ONE]]. }
  eapply arun_bind_l; [apply arun_aret|]. unfold init_cache.
  eapply arun_bind_l; [apply arun_aupd|]. rewrite (upd_ci_id a CI).
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. rewrite FULL, Z.eqb_refl.
  replace [AEvMmap (free_array SB c + rg_mapped_fa (get_region a c)) kFreeArrayMapSize kProtRw kFlagsFixedRw]
     with ([AEvMmap (free_array SB c + rg_mapped_fa (get_region a c)) kFreeArrayMapSize kProtRw kFlagsFixedRw] ++ []) by reflexivity.
  eapply (arun_abind _ _ _ 1%nat 0%nat).
  { eapply arun_bind_l; [apply arun_aupd|]. fold (dr_keep a c). change (set_cache c (firstn (dr_keep a c) (get_cache a c)) a) with (dr_st c a).
    fold (dr_chunks c a). unfold return_to_allocator.
    eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta.
    replace [AEvMmap (free_array SB c + rg_mapped_fa (get_region a c)) kFreeArrayMapSize kProtRw kFlagsFixedRw]
       with ([AEvMmap (free_array SB c + rg_mapped_fa (get_region a c)) kFreeArrayMapSize kProtRw kFlagsFixedRw] ++ []) by reflexivity.
    eapply (arun_abind _ _ _ 1%nat 0%nat).
    { unfold ensure_free_array_space. eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta.
      unfold dr_st at 1 2 3 4 5 6 7 8. rewrite ?get_region_set_cache.
      replace (rg_mapped_fa (get_region a c) <? 4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a))) with true by (symmetry; apply Z.ltb_lt; exact GROW).
      rewrite NEWFA. replace (rg_mapped_fa (get_region a c) + kFreeArrayMapSize <=? kFreeArraySize) with true by (symmetry; apply Z.leb_le; exact FAS).
      eapply arun_bind_l; [apply arun_aret|].
      replace (rg_mapped_fa (get_region a c) + kFreeArrayMapSize - rg_mapped_fa (get_region a c)) with kFreeArrayMapSize by (clear; lia).
      unfold call_mmap_fixed. cbn -[st_fa dr_st free_array kFreeArrayMapSize get_region set_region upd_ts ts_on_mmap Z.add Z.eqb kProtRw kFlagsFixedRw].
      rewrite Z.eqb_refl. cbn -[st_fa dr_st free_array kFreeArrayMapSize get_region set_region upd_ts ts_on_mmap Z.add kProtRw kFlagsFixedRw].
      unfold st_fa. reflexivity. }
    cbn [negb]. eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. apply arun_aupd. }
  eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. rewrite arun_aupd. reflexivity.
Qed.
End Model.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regions_bytes_ext : forall a b,
  (forall c, rg_mapped_user (get_region b c) = rg_mapped_user (get_region a c) /\ rg_mapped_fa (get_region b c) = rg_mapped_fa (get_region a c)) ->
  regions_bytes b = regions_bytes a.
Proof.
  intros a b H. unfold regions_bytes. generalize classes30. intros cs. induction cs as [|x cs IH]; cbn; [reflexivity|].
  destruct (H x) as [H1 H2]. rewrite IH, H1, H2. reflexivity.
Qed.

Lemma nth_error_app_mid : forall {X} (l1 : list X) (v : X) l2, nth_error (l1 ++ v :: l2) (length l1) = Some v.
Proof. intros X l1 v l2. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cpn_app : forall vs src1 src2 pre mid post, length mid = length vs ->
  cpn (length vs) (src1 ++ vs ++ src2) (pre ++ mid ++ post) (length src1) (length pre) = pre ++ vs ++ post.
Proof.
  induction vs as [|v vs IH]; intros src1 src2 pre mid post LEN.
  - destruct mid; [reflexivity| discriminate].
  - destruct mid as [|m0 mid']; [discriminate|]. cbn [length cpn].
    change (src1 ++ (v :: vs) ++ src2) with (src1 ++ v :: (vs ++ src2)). rewrite (nth_error_app_mid src1 v (vs ++ src2)).
    change (pre ++ (m0 :: mid') ++ post) with (pre ++ [m0] ++ (mid' ++ post)). rewrite (BF_popT.upd_app_mid pre (mid' ++ post) m0 v).
    specialize (IH (src1 ++ [v]) src2 (pre ++ [v]) mid' post ltac:(cbn in LEN; lia)).
    rewrite !length_app in IH. cbn [length] in IH. rewrite !Nat.add_1_r in IH. rewrite <- !app_assoc in IH. cbn [app] in IH. exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_LDC : Z := 688.    (* [comment removed for export] *)

Section LdcT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaaf58.
#[local] Notation CA := (ae_thread E0 + kThrCache).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blocks_sep_ofD : forall E P D a mo, env0_ok5 E -> AWf E P D a -> AKern E a mo -> blocks_sep E a.
Proof.
  intros E P D a mo ENV WF K. pose proof alloc_ceiling_range as CR.
  pose proof ENV as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & _).
  destruct WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  assert (SECR : forall sc r, In sc (as_sec a) -> In r (ae_reserved E) -> sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc).
  { intros sc r Hsc Hr. destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & S3 & S4 & S5).
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in N3, N4.
  intros b len [[Hb ->]|[Hb ->]].
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kDepotNodeBlockBytes in *; clear -N3 CR; lia|].
      split; [unfold kDepotNodeBlockBytes in *; clear -N3; lia|]. split; [exact N7|]. split; [| split; [exact N8| exact N5]].
      intros sc Hsc. destruct (SECR sc _ Hsc N1); cbn [fst snd] in *; [right| left]; lia.
    + destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kStoreBlockBytes in *; clear -N4 CR; lia|].
      split; [unfold kStoreBlockBytes in *; clear -N4; lia|]. unfold kStoreBlockBytes. split; [exact S1|]. split; [exact S2|]. split; [exact N9| exact N6].
    + destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
Qed.
Lemma img_depsep_asan' : forall E, ae_ic E = both_ic ->
  forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros E IC x y Hx Hy. unfold arep_img_ranges, ae_instance in Hx. unfold depot_static in Hy. rewrite IC in Hx, Hy.
  cbn -[Z.add Z.le In] in Hx, Hy.
  destruct Hy as [<-|[<-|[]]]; cbn [fst snd]; repeat (destruct Hx as [<-|Hx]; [cbn [fst snd]; lia|]); destruct Hx.
Qed.
Lemma renv_of : forall D a mo, AWf E0 [] D a -> AKern E0 a mo -> fst (ae_img E0) = 0x10000 -> 0x5f3000 <= snd (ae_img E0) -> AsanRepEnqB.renv_ok E0 a.
Proof.
  intros D a mo WF K EI1 EI2. pose proof alloc_ceiling_range as CR.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as (_ & _ & TR & _). pose proof TR as (_ & (Tlo & Thi & Timg & Tband) & _). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  split; [exact (blocks_sep_ofD E0 [] D a mo ENV0 WF K)|]. split; [clear -Tlo Thi Timg; repeat split; lia|].
  split; [intros r Hr; pose proof (IMGR r Hr) as X; rewrite EI1; clear -X EI2; lia|]. split; [rewrite EI1; clear; lia|]. split; [exact IMGR|].
  split; [exact (img_depsep_asan' E0 IC0)|]. split; [exists mo; exact K|]. split; [exact TDN| exact DNP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FPW5b (lo c : Z) (z : Z) : Prop :=
     lo <= z
  \/ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + kPerClassSize)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24).
Definition R5b_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo c p : Z) (D : list batch) (junk : list word),
  let l := get_cache a c in
  1 <= c <= kLargestClassID -> as_cache_inited a = true -> zlen l < max_count c -> avail E0 D a c p ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPW5b lo c z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (T + kThrCache + kPerClassSize * c) [C4 (wz (zlen l + 1)); C4 (wz (max_count c)); C8 (wz (class_size c))] ->
  u32arr bsegs m' (T + kThrCache + kPerClassSize * c + 16) (map wz (l ++ [compact_of_chunk SB c p]) ++ junk) ->
  (length l + 1 + length junk = 16)%nat ->
  rw_cells bsegs m' (T + kThrCacheStats + 16) [C8 (wz (as_cache_allocated a - class_size c))] ->
  ARep bsegs E0 (DepotR bsegs E0) (push_st E0 c p a) m'.
Hypothesis R5b : R5b_stmt.

(* [comment removed for export] *)
Definition FPW6 (a : astate) (lo c : Z) (g : bool) (z : Z) : Prop :=
  let r := get_region a c in let FA := free_array SB c in
     lo <= z
  \/ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + kPerClassSize)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24)
  \/ (RI + kRegSize * c <= z < RI + kRegSize * c + kRegSize)
  \/ (FA + 4 * rg_num_freed r <= z < FA + 4 * (rg_num_freed r + hint c))
  \/ (g = true /\ (   (T + kThrStats + 72 <= z < T + kThrStats + 88)
                   \/ (FA + rg_mapped_fa r <= z < FA + rg_mapped_fa r + kFreeArrayMapSize)
                   \/ (kShadowBase + (FA + rg_mapped_fa r) / 8 <= z < kShadowBase + (FA + rg_mapped_fa r) / 8 + kFreeArrayMapSize / 8))).
Definition R6_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo c p : Z) (D : list batch) (junk fjunk : list word) (g : bool),
  let l := get_cache a c in let h := hint c in let r := get_region a c in let FA := free_array SB c in
  let ch := dr_chunks c a in let a1 := dr_st c a in let a2 := (if g then st_fa c a1 else a1) in
  let a' := push_st E0 c p (rta_st c ch a2) in
  let mfa' := rg_mapped_fa r + (if g then kFreeArrayMapSize else 0) in
  1 <= c <= kLargestClassID -> as_cache_inited a = true -> zlen l = max_count c -> avail E0 D a c p ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPW6 a lo c g z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (T + kThrCache + kPerClassSize * c) [C4 (wz (h + 1)); C4 (wz (max_count c)); C8 (wz (class_size c))] ->
  u32arr bsegs m' (T + kThrCache + kPerClassSize * c + 16) (map wz (firstn (Z.to_nat h) l ++ [compact_of_chunk SB c p]) ++ junk) ->
  (Z.to_nat h + 1 + length junk = 16)%nat ->
  rw_cells bsegs m' (T + kThrCacheStats + 16) [C8 (wz (as_cache_allocated a - class_size c))] ->
  rw_cells bsegs m' (RI + kRegSize * c) (region_cells (get_region a' c)) ->
  u32arr bsegs m' FA (map wz (rg_free r ++ ch) ++ fjunk) -> 4 * (Z.of_nat (length (rg_free r ++ ch)) + Z.of_nat (length fjunk)) = mfa' ->
  (g = true -> rw_cells bsegs m' (T + kThrStats + 72) [C8 (wz (ts_mmaps (as_ts a) + 1)); C8 (wz (ts_mmaped (as_ts a) + kFreeArrayMapSize))]
              /\ rw_cells bsegs m' (kShadowBase + (FA + rg_mapped_fa r) / 8)
                   [CB (Z.to_nat (kFreeArrayMapSize / 8)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (kFreeArrayMapSize / 8)))]) ->
  (g = true -> rg_mapped_fa r + kFreeArrayMapSize <= kFreeArraySize) ->
  ARep bsegs E0 (DepotR bsegs E0) a' m'.
Hypothesis R6 : R6_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ldc_W (a : astate) (c usp : Z) : list (Z * Z) :=
  let r := get_region a c in let FA := free_array SB c in
  [ (usp - K_LDC, usp)
  ; (T + kThrCache + kPerClassSize * c, T + kThrCache + kPerClassSize * c + kPerClassSize)
  ; (T + kThrCacheStats + 16, T + kThrCacheStats + 24)
  ; (T + kThrStats + 72, T + kThrStats + 88)
  ; (RI + kRegSize * c, RI + kRegSize * c + kRegSize)
  ; (FA + 4 * rg_num_freed r, FA + 4 * (rg_num_freed r + hint c))
  ; (FA + rg_mapped_fa r, FA + rg_mapped_fa r + kFreeArrayMapSize)
  ; (kShadowBase + (FA + rg_mapped_fa r) / 8, kShadowBase + (FA + rg_mapped_fa r) / 8 + kFreeArrayMapSize / 8) ].

(* [comment removed for export] *)
Definition ldc_same (a a' : astate) (c : Z) : Prop :=
     as_chunks a' = as_chunks a /\ as_dead a' = as_dead a /\ as_tq a' = as_tq a /\ as_gq a' = as_gq a
  /\ as_sec a' = as_sec a /\ as_ptr_committed a' = as_ptr_committed a /\ as_sec_stats a' = as_sec_stats a /\ as_sec_stale a' = as_sec_stale a
  /\ as_glob_allocated a' = as_glob_allocated a /\ as_glob_mapped a' = as_glob_mapped a
  /\ as_nprim_ever a' = as_nprim_ever a /\ as_residue a' = as_residue a /\ as_everc a' = as_everc a
  /\ as_ndepot_ins a' = as_ndepot_ins a /\ as_node_blocks a' = as_node_blocks a /\ as_store_blocks a' = as_store_blocks a
  /\ as_keys a' = as_keys a /\ as_frames a' = as_frames a /\ as_store_stored a' = as_store_stored a
  /\ as_cache_inited a' = true /\ as_cache_mapped a' = as_cache_mapped a /\ as_ia_inited a' = as_ia_inited a /\ as_oom a' = as_oom a
  /\ (forall c', c' <> c -> get_region a' c' = get_region a c' /\ get_cache a' c' = get_cache a c')
  /\ rg_mapped_user (get_region a' c) = rg_mapped_user (get_region a c) /\ rg_alloc_user (get_region a' c) = rg_alloc_user (get_region a c)
  /\ rg_mapped_fa (get_region a c) <= rg_mapped_fa (get_region a' c) <= rg_mapped_fa (get_region a c) + kFreeArrayMapSize
  /\ regions_bytes a' = regions_bytes a + (rg_mapped_fa (get_region a' c) - rg_mapped_fa (get_region a c)).

Definition ldc_post (D : list batch) (a a' : astate) (c p : Z) (m m' : mem) (mo mo' : Model) (s : aps) (C C' lo usp : Z) : Prop :=
     (exists fuel orc evs orc', arun fuel (local_dealloc E0 c p a) orc = Some (a', ONorm tt, evs, orc'))
  /\ ARep bsegs E0 (DepotR bsegs E0) a' m' /\ AWf E0 [] D a' /\ AKern E0 a' mo' /\ RTOKc C C' (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ stk bsegs m' lo usp /\ mem_inv bsegs m' /\ rt_misc5 FSB0 PL0 E0 m' /\ wmono bsegs m m' /\ munch (ldc_W a c usp) m m'
  /\ ldc_same a a' c.

(* [comment removed for export] *)
Theorem ldc_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (D : list batch) (c p lo usp C C' : Z) (K : TSet),
  let a := aps_alloc s in
  K [] ->
  RTOKc C C' s mo -> ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AKern E0 a mo -> res_ok a ->
  mem_inv bsegs m -> rt_misc5 FSB0 PL0 E0 m ->
  1 <= c <= kLargestClassID -> avail E0 D a c p -> as_cache_inited a = true ->
  kFreeArrayMapSize <= gapR a -> rg_mapped_fa (get_region a c) + kFreeArrayMapSize <= kFreeArraySize ->
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_LDC -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e1550 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     ldc_post D a a' c p m m' mo mo' s C C' lo usp ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz CA) (wz INST) (wz c) (wz p) a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz 0x35068) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. cbv zeta. intros KN TOK REP WF AK RES MI RT HC AV CI RR RFA SK LOC LO SPA SPH TP KONT.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  set (a := aps_alloc s) in *.
  unfold K_LDC in LO. assert (USPR : 0 <= usp < 2^64) by (clear -LO LOC CR SPH; lia).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & GLE). fold a in GR0, GD0, GLE.
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof L0OK as (LS_L0 & GS_L0 & HS_L0 & RES0_low & RES0_cover & RSVD & RSVD_pos).
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof HC as HC30. unfold kLargestClassID in HC30. pose proof (hint_range c HC30) as HR. set (h := hint c) in *.
  pose proof (proj2 (class_size_mod c HC30)) as CS. set (size := class_size c) in *.
  (* [comment removed for export] *)
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rins as (I1 & I2 & _).
  pose proof (pop_statics_of E0 FSB0 PL0 a m IC0 REP RT) as PST. pose proof PST as [STA PG].
  unfold ae_instance in I1, I2. rewrite IC0 in I1, I2. cbn [aic_instance both_ic kInsSpaceBeg kInsSecondary Z.add] in I1, I2.
  pose proof WF as (WE & WR & WC & WK & WQ & WS & WD). pose proof WC as (WC1 & WC2 & WC3).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 & WE19 & WE20 &
                    WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & _).
  unfold app_mem in WE14, WE16. rewrite KHB, KLE in WE14, WE16.
  assert (HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling).
  { rewrite KHB in WE2. split; [clear -WE2 WE3; lia|]. split; [clear -WE1; Z.div_mod_to_equations; nia| clear -WE4 WE5; unfold kSpaceSize in WE4 |- *; lia]. }
  assert (HSBH : kHighMemBeg <= SB) by (clear -WE2 WE3; lia).
  assert (HRI : RI = SB + kSpaceSize) by reflexivity.
  (* [comment removed for export] *)
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & CIA).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ RT) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  assert (TC : thread_cells m tp 0x6028f8 CTX T).
  { pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
    split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  assert (HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0).
  { unfold kThrCache. clear -Tlo Thi Timg T8. split; [| split; [lia| Z.div_mod_to_equations; lia]]. lia. }
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  assert (HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA).
  { unfold kThrCache, kSpaceSize. pose proof (wf_env_thread _ WE) as (_ & _ & _ & WT4 & _). clear -WT4 G1 G2 G3. lia. }
  (* [comment removed for export] *)
  destruct (proj2 WR c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). cbv zeta in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12.
  unfold region_of in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12.
  set (r := get_region a c) in *. set (l := get_cache a c) in *.
  set (RP := RI + kRegSize * c). set (FA := free_array SB c). set (PCB := CA + 80 * c).
  assert (HRP' : RP = SB + 2^37 + 128 * c) by (subst RP; rewrite HRI; reflexivity).
  assert (HFA' : FA = SB + c * 4294967296 + 3758096384) by (subst FA; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset; clear; lia).
  destruct (WC3 c HC) as (LMAX & LND & LIN). fold l in LMAX, LND, LIN.
  destruct (Tcache c ltac:(unfold kNumClasses; clear -HC30; lia)) as [ROW (junk & CARR & CLEN)]. fold l in ROW, CARR, CLEN |- *.
  unfold percls_cells in ROW. rewrite CI in ROW. fold l in ROW. unfold kThrCache, kPerClassSize in ROW, CARR. fold PCB in ROW. 
  (* [comment removed for export] *)
  assert (CNT0 : 0 <= zlen l) by (unfold zlen; clear; lia).
  assert (MC : max_count c = 2 * h) by (subst h; reflexivity).
  rewrite (row_max_count_reg E0 c HC), (row_class_size_reg E0 c HC) in ROW. fold size in ROW.
  assert (LEN : length (map (fun z : Z => wz z) l ++ junk) = 16%nat) by (rewrite length_app, length_map; exact CLEN).
  (* [comment removed for export] *)
  pose proof AV as (CVp & NFp & NCp & UTp). pose proof CVp as (kp & K0 & KE & KB). unfold region_of in KB. fold r size in KE, KB.
  assert (HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000).
  { unfold region_beg, kRegionSize in KE. unfold kFreeArrayOffset in A3. clear -KE KB K0 A1 A3 CS. nia. }
  (* [comment removed for export] *)
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)] [C1 (Z_to_bv 8 0)] I1) as [INS4 _].
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (wz SB)] [C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)] INS4) as [INS1 _].
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (wz (as_cache_allocated a))] [C8 (wz (as_cache_mapped a))] Tcst) as [CST _].
  unfold kThrCacheStats in CST. replace (T + (208 + 2560) + 16) with (CA + 2576) in CST by (unfold kThrCache; clear; lia).
  (* [comment removed for export] *)
  set (P0 := PP s mo).
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  assert (AKs : AKern E0 (aps_alloc s) mo) by exact AK.
  assert (PSTK : forall y j, lo <= y -> y + Z.of_nat j <= usp -> P0 (Z_to_bv 64 y, j)).
  { intros y j H1 H2. unfold P0, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo AKs WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PDAT : forall y j, 0xa5000 <= y -> y + Z.of_nat j <= 0x603000 -> P0 (Z_to_bv 64 y, j)).
  { intros y j H1 H2. unfold P0, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo AKs WE ENV ENV0); clear -H1 H2; lia. }
  assert (PRO : forall y j, 0x10000 <= y -> y + Z.of_nat j <= 0x31000 -> P0 (Z_to_bv 64 y, j)).
  { intros y j H1 H2. unfold P0, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo AKs WE ENV ENV0); clear -H1 H2; lia. }
  assert (PCA : forall y j, CA <= y -> y + Z.of_nat j <= CA + 2584 -> P0 (Z_to_bv 64 y, j)).
  { intros y j H1 H2. unfold P0, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo AKs WE); unfold kThrCache in H1, H2; clear -H1 H2; lia. }
  assert (PRIR : forall y j, BF_free6.RIc c RI <= y -> y + Z.of_nat j <= BF_free6.RIc c RI + 128 -> P0 (Z_to_bv 64 y, j)).
  { intros y j H1 H2. unfold BF_free6.RIc in H1, H2. rewrite HRI in H1, H2. unfold P0, BF_caT.PP. apply (pol_reginfo' E0 FSB0 HR0 s mo WE); change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
  destruct (Z_lt_le_dec (zlen l) (max_count c)) as [LT|GE].
  - (* [comment removed for export] *)
    set (Qp := fun ms' : machine_state => exists (m' : mem) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
          ms' = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
          /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ munch [(usp - 48, usp); (CA + 80 * c, CA + 80 * c + 4); (CA + 80 * c + 16 + 4 * zlen l, CA + 80 * c + 16 + 4 * zlen l + 4); (CA + 2576, CA + 2584)] m m'
          /\ wmono bsegs m m'
          /\ rw_cells bsegs m' (CA + 80 * c) [C4 (wz (zlen l + 1)); C4 (wz (max_count c)); C8 (wz size)]
          /\ u32arr bsegs m' (CA + 80 * c + 16) (upd (map (fun z : Z => wz z) l ++ junk) (Z.to_nat (zlen l)) (wz (BF_free6.xc SB c p)))
          /\ rw_cells bsegs m' (CA + 2576) [C8 (wz (as_cache_allocated a - size))]).
    eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 Qp).
    { eapply (ldc_push P0 gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) HSB HC HCA HCASB HP PSTK PDAT PCA
                m ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 (zlen l) (max_count c) (as_cache_allocated a) (wz size) (map (fun z : Z => wz z) l ++ junk) Qp MI SK INS1);
        [unfold BF_free6.PCB, kThrCache in ROW |- *; exact ROW| rewrite MC; clear -HR; lia| clear -CNT0 LT; lia| unfold BF_free6.PCB; unfold kThrCache in CARR |- *; exact CARR| exact LEN| exact CST|].
      intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' MI' SK' MU' WM' INS' ROW' ARR' CST'.
      apply evtA_done. unfold Qp. exists m', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact SK'|]. split; [unfold BF_free6.PCB in MU'; exact MU'|]. split; [exact WM'|].
      split; [unfold BF_free6.PCB in ROW'; exact ROW'|]. split; [unfold BF_free6.PCB in ARR'; exact ARR'|].
      rewrite unsigned_lit in CST' by (clear -CS; lia). exact CST'. }
    { exact KIP0. }
    intros ms1 mo1 HQ1 AG1 KIP1. unfold Qp in HQ1.
    destruct HQ1 as (m1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & MI1 & SK1 & MU1 & WM1 & ROW1 & ARR1 & CST1).
    pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _). destruct KIP1 as [KIA1 _].
    set (a' := push_st E0 c p a).
    (* [comment removed for export] *)
    destruct junk as [|j0 junk']; [exfalso; rewrite MC in LT; unfold zlen in LT; cbn [length] in CLEN; clear -LT CLEN HR; lia|].
    assert (EARR : upd (map (fun z : Z => wz z) l ++ j0 :: junk') (Z.to_nat (zlen l)) (wz (BF_free6.xc SB c p)) = map (fun z : Z => wz z) (l ++ [compact_of_chunk SB c p]) ++ junk').
    { replace (Z.to_nat (zlen l)) with (length (map (fun z : Z => wz z) l)) by (rewrite length_map; unfold zlen; clear; lia).
      pose proof (BF_popT.upd_app_mid (map (fun z : Z => wz z) l) junk' j0 (wz (compact_of_chunk SB c p))) as X. cbn [app] in X.
      replace (BF_free6.xc SB c p) with (compact_of_chunk SB c p) by (unfold BF_free6.xc, compact_of_chunk, region_beg, kRegionSize; f_equal; clear; lia).
      rewrite X, map_app, <- app_assoc. reflexivity. }
    rewrite EARR in ARR1.
    assert (AGW : forall z, 0 <= z < 2^64 -> ~ FPW5b lo c z -> m1 (wa z) = m (wa z)).
    { intros z Hz NF. apply MU1. rewrite wa_unsigned by exact Hz. unfold FPW5b, kThrCache, kPerClassSize, kThrCacheStats in NF. cbn [outside]. unfold kThrCache.
      clear -NF LO Hz CNT0 LT MC HR. repeat split; try exact I; lia. }
    pose proof (renv_of D a mo WF AK EI1 EI2) as RENV.
    assert (REP1 : ARep bsegs E0 (DepotR bsegs E0) a' m1).
    { apply (R5b a m m1 lo c p D junk' HC CI LT AV REP WF RENV WM1 AGW LOC).
      - unfold kPerClassSize. fold l size. unfold kThrCache in ROW1 |- *. exact ROW1.
      - unfold kPerClassSize. fold l. unfold kThrCache in ARR1 |- *. exact ARR1.
      - fold l. cbn [length] in CLEN. clear -CLEN. lia.
      - unfold kThrCacheStats. fold size. unfold kThrCache in CST1. replace (T + (208 + 2560) + 16) with (T + 208 + 2576) by (clear; lia). exact CST1. }
    assert (NF : zlen l <> max_count c) by (clear -LT; lia).
    pose proof (run_ldc_push E0 c p a [] HC CI NF) as RUN.
    pose proof (hoare_arun _ _ _ a 0%nat [] a' tt [] [] (local_dealloc_spec E0 [] D a c p HC WF AV) eq_refl RUN) as (WF' & PF' & CVM' & CI').
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
    assert (TOK1' : RTOKc C C' (sA a' s) mo1).
    { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a' mo1).
      - change a with (aps_alloc s). rewrite BF_popT.sA_self. exact TOK1.
      - subst a'. unfold same_fp. rewrite push_as_sec, push_as_ptr_committed, push_as_residue, push_as_node_blocks, push_as_store_blocks.
        rewrite (regions_bytes_same a (push_st E0 c p a) (push_get_region E0 c p a)). repeat split; reflexivity.
      - apply push_as_nprim_ever. - apply push_as_ndepot_ins. }
    pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
    pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
    eapply KONT. unfold ldc_post. split; [exists 0%nat, [], [], []; exact RUN|].
    split; [exact REP1|]. split; [exact WF'|].
    split. { apply (AKern_ext E0 a a'); [apply push_as_regions| apply push_as_ptr_committed| apply push_as_sec| apply push_as_node_blocks| apply push_as_store_blocks|].
             exact (AKern_frame _ _ _ _ Fvm1 Flz1 AK). }
    split; [exact TOK1'|]. split; [exact Ffs1|]. split; [exact Ffds1|]. split; [exact Ftid1|].
    split; [exact SK1|]. split; [exact MI1|].
    split. { apply (rt_misc5_agree E0 FSB0 PL0 m m1 RT). intros z Hz.
             destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
             - apply MU1. rewrite wa_unsigned by (clear -ZI; lia). cbn [outside]. unfold kThrCache. clear -ZI LOC LO CR Timg Tlo HC30 CNT0 LT MC HR. repeat split; try exact I; lia.
             - unfold rt_high2 in RH. apply MU1. rewrite wa_unsigned by (clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia). cbn [outside]. unfold kThrCache.
               clear -RH LOC LO CR Tlo Thi CT DT CQ2 CC1 CC2 DQ2 DD1 DD2 HC30 CNT0 LT MC HR. repeat split; try exact I; lia. }
    split; [exact WM1|].
    split. { eapply munch_cover; [exact MU1|]. unfold ldc_W, K_LDC, kThrCache, kPerClassSize, kThrCacheStats. cbv zeta. clear -LO CNT0 LT MC HR. solve_covers. }
    subst a'. unfold ldc_same.
    rewrite push_as_chunks, push_as_dead, push_as_tq, push_as_gq, push_as_sec, push_as_ptr_committed, push_as_sec_stats, push_as_sec_stale, push_as_glob_allocated, push_as_glob_mapped,
            push_as_nprim_ever, push_as_residue, push_as_everc, push_as_ndepot_ins, push_as_node_blocks, push_as_store_blocks, push_as_keys, push_as_frames, push_as_store_stored,
            push_as_cache_inited, push_as_cache_mapped, push_as_ia_inited, push_as_oom, !push_get_region.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact CI.
    + intros c' NE. rewrite push_get_region. split; [reflexivity| apply push_get_cache_ne; clear -NE; lia].
    + unfold kFreeArrayMapSize; clear; lia.
    + rewrite (regions_bytes_same a (push_st E0 c p a) (push_get_region E0 c p a)). clear; lia.
  - (* [comment removed for export] *)
    assert (FULL : zlen l = max_count c) by (clear -GE LMAX; lia).
    assert (LENl : length l = (2 * Z.to_nat h)%nat) by (rewrite MC in FULL; unfold zlen in FULL; clear -FULL HR; lia).
    assert (KEEP : dr_keep a c = Z.to_nat h) by (unfold dr_keep; fold l; subst h; rewrite LENl; clear -HR; lia).
    set (l1 := firstn (Z.to_nat h) l). set (l2 := dr_chunks c a).
    assert (El2 : l2 = skipn (Z.to_nat h) l) by (subst l2; unfold dr_chunks; fold l; rewrite KEEP; reflexivity).
    assert (El : l = l1 ++ l2) by (rewrite El2; subst l1; symmetry; apply firstn_skipn).
    assert (LEN1 : length l1 = Z.to_nat h) by (subst l1; rewrite firstn_length_le; [reflexivity| rewrite LENl; clear -HR; lia]).
    assert (LEN2 : length l2 = Z.to_nat h) by (rewrite El2, length_skipn, LENl; clear -HR; lia).
    assert (ZL2 : zlen l2 = h) by (unfold zlen; rewrite LEN2; clear -HR; lia).
    assert (El2c : dr_chunks c a = l2) by reflexivity. clearbody l2.
    destruct l2 as [|x0 l2']; [exfalso; cbn [length] in LEN2; clear -LEN2 HR; lia|]. set (l2 := x0 :: l2') in *.
    (* [comment removed for export] *)
    set (nf := rg_num_freed r). set (mfa := rg_mapped_fa r).
    assert (NF0 : 0 <= nf < 2^40) by (subst nf mfa; unfold kFreeArraySize in A7; clear -A8 A7; unfold rg_num_freed in *; lia).
    set (nfr := rg_n_freed r mod 2^64). assert (NFR : 0 <= nfr < 2^64) by (subst nfr; apply Z.mod_pos_bound; clear; lia).
    assert (RIC : rw_cells bsegs m (BF_free6.RIc c RI) (ri_cells 0 nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr)).
    { pose proof (Rri c ltac:(unfold kNumClasses; clear -HC30; lia)) as X. unfold region_of in X. fold r in X.
      change (region_cells r) with (C8 (Z_to_bv 64 0) :: List.tl (region_cells r)) in X. rewrite (pop_row 0 r) in X.
      subst nfr. unfold ri_cells in X |- *. rewrite (ZBridge.Z_to_bv_mod64 (rg_n_freed r)). unfold BF_free6.RIc. unfold kRegSize in X. exact X. }
    destruct (Rrm c ltac:(unfold kNumClasses; clear -HC30; lia)) as [UMAP (fjunk & FARR & FAL)]. unfold region_of in UMAP, FARR, FAL. fold r in UMAP, FARR, FAL. fold FA in FARR.
    set (fws := map AsanRep.zw (rg_free r) ++ fjunk) in FARR.
    assert (FLEN : 4 * Z.of_nat (length fws) = mfa) by (subst fws mfa; rewrite length_app, length_map; rewrite <- FAL; clear; lia).
    assert (LENF : length (rg_free r) = Z.to_nat nf) by (subst nf; unfold rg_num_freed; clear; lia).
    assert (MFR : mfa <= 2^29) by (subst mfa; unfold kFreeArraySize in A7; clear -A7; lia).
    (* [comment removed for export] *)
    assert (SMALL : forall j, (Z.to_nat h <= j < Z.to_nat (2 * h))%nat -> exists x, nth_error (map (fun z : Z => wz z) l ++ junk) j = Some (Z_to_bv 64 x) /\ 0 <= x < 2^31).
    { intros j Hj. assert (Hjl : (j < length l)%nat) by (rewrite LENl; clear -Hj HR; lia).
      destruct (nth_error l j) as [x|] eqn:NTH; [| exfalso; apply nth_error_None in NTH; clear -NTH Hjl; lia].
      exists x. split; [rewrite nth_error_app1 by (rewrite length_map; exact Hjl); rewrite nth_error_map, NTH; reflexivity|].
      destruct (LIN x (nth_error_In _ _ NTH)) as ((kx & KX0 & KXE & KXB) & _). unfold region_of in KXB. fold r in KXB.
      unfold chunk_of_compact, region_beg in KXE. unfold kFreeArrayOffset in A3. clear -KX0 KXE KXB A1 A3 CS. nia. }
    (* [comment removed for export] *)
    assert (PFA : forall y j, FA <= y -> y + Z.of_nat j <= FA + mfa -> P0 (Z_to_bv 64 y, j)).
    { intros y j H1 H2. destruct j as [|j']; [apply acc_ok_empty|]. unfold P0, BF_caT.PP.
      apply (pol_fa E0 FSB0 HR0 s mo [] D AKs WF c y (Datatypes.S j') HC); [exact H1| subst FA mfa; exact H2| clear; lia]. }
    pose proof STA as (GPS & _ & _ & VPS & _). unfold GOT_PAGESIZE, V_PAGESIZE in GPS, VPS.
    rewrite FULL, MC in ROW.
    destruct (Z_lt_le_dec mfa (4 * (nf + h))) as [GROW|NOGROW].
    + (* [comment removed for export] *)
      subst FA. rewrite HFA' in *. set (FA := SB + c * 4294967296 + 3758096384) in *.
      set (A := FA + mfa).
      assert (HA : 0x603000 <= A /\ A + 262144 <= SB + kSpaceSize /\ A mod 4096 = 0 /\ A mod 8 = 0).
      { subst A FA. unfold kSpaceSize. unfold kFreeArraySize, kFreeArrayMapSize in RFA. unfold kFreeArrayMapSize in A6. fold mfa in RFA, A6, A5.
        clear -HSB HC30 RFA A5 A6. split; [lia|]. split; [lia|]. split; Z.div_mod_to_equations; lia. }
      destruct HA as (HA1 & HA2 & HA3 & HA8). pose proof HSB as (SB1 & SB2 & SB3).
      assert (ONE : 4 * (nf + h) <= mfa + kFreeArrayMapSize) by (unfold kFreeArrayMapSize; subst nf mfa; clear -A8 HR; lia).
      assert (MFM : mfa mod 262144 = 0) by (subst mfa; unfold kFreeArrayMapSize in A6; exact A6).
      assert (MF0 : 0 <= mfa) by (subst mfa; exact A5).
      assert (MFR2 : mfa + 262144 <= 2^29) by (subst mfa; unfold kFreeArraySize, kFreeArrayMapSize in RFA; clear -RFA; lia).
      (* [comment removed for export] *)
      set (QA := fun ms' : machine_state => exists (m1 : mem) (j1 j2 j : list byte),
          ms' = MS (BF_free9.gregs gp tp t3 t4 t5 t6 CA SB c RI (wz 0x35968) (usp + -288) t0 t1 t2 (wz INST) (wz (FA + mfa)) (wz 262144) (wz 0x18a20) (wz mfa) (wz 3758096384) (wz 0) (wz 1500) h nf mfa)
                   F (wz 0x6f978) fc None m1 (seg_rom bsegs)
          /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -288)
          /\ munch [(usp - 688, usp); (BF_free6.PCB CA c, BF_free6.PCB CA c + 4); (BF_free6.RIc c RI, BF_free6.RIc c RI + 8)] m m1 /\ wmono bsegs m m1
          /\ BF_free6.drain_frames s5 s6 s7 s8 s9 s10 s11 usp CA c p RI m1 ra s0 s1 s2 s3 s4 j1 j2 /\ BF_free9.efa_frame usp c RI m1 j nf
          /\ rw_cells bsegs m1 0xaaf78 [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI); C1 (Z_to_bv 8 0)]
          /\ rw_cells bsegs m1 (BF_free6.PCB CA c) [C4 (wz h); C4 (wz (2 * h)); C8 (wz size)]
          /\ u32arr bsegs m1 (BF_free6.PCB CA c + 16) (map (fun z : Z => wz z) l ++ junk)
          /\ rw_cells bsegs m1 (CA + 2576) [C8 (wz (as_cache_allocated a))]
          /\ rw_cells bsegs m1 (BF_free6.RIc c RI) (ri_cells 1152921504606846976 nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr)).
      eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 QA).
      { eapply (ldc_drain_head P0 gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) HSB HC HCA HCASB PSTK PDAT PCA RI HRI PRIR ltac:(clear -LO; lia)
                  m ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 h (as_cache_allocated a) nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr (wz size)
                  (map (fun z : Z => wz z) l ++ junk) QA MI SK INS4);
          [unfold BF_free6.PCB, kThrCache in ROW |- *; exact ROW| exact HR| unfold BF_free6.PCB; unfold kThrCache in CARR |- *; exact CARR| exact LEN| exact CST| exact RIC| exact NF0|].
        intros m0 j1 j2 MI0 SK0 MU0 WM0 DF0 INS0 PC0 ARR0 CST0 RIC0.
        assert (INS5 : rw_cells bsegs m0 0xaaf78 [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI); C1 (Z_to_bv 8 0)]).
        { eapply rw_cells_transport; [exact I1| exact MU0| exact WM0|]. cbn [disjoint_from cells_size csize fst snd Nat.add]. unfold BF_free6.PCB, BF_free6.RIc, kThrCache. rewrite HRI.
          unfold kSpaceSize. clear -LO LOC CR Timg Tlo HC30 HSB. repeat split; try exact I; lia. }
        eapply (efa_grow_pre P0 gp tp t3 t4 t5 t6 F fc usp lo CA SB c RI LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) HSB HC HCA HRI PSTK PDAT PRIR
                  m0 t0 t1 t2 h nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr 1152921504606846976 QA MI0 SK0 INS5 RIC0 HR ltac:(clear -NF0; lia)
                  ltac:(subst nf mfa; exact A8) GROW MF0 MFM MFR2).
        intros m1 j MI1' SK1' MU1' WM1' EFR1.
        apply evtA_done. unfold QA. exists m1, j1, j2, j.
        split; [reflexivity|]. split; [exact MI1'|]. split; [exact SK1'|].
        split; [eapply munch_trans; [exact MU0| eapply munch_cover; [exact MU1'| clear -LO; solve_covers]]|]. split; [exact (wmono_trans _ _ _ _ WM0 WM1')|].
        Ltac tr688 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]].
        split. { unfold BF_free6.drain_frames in DF0 |- *. destruct DF0 as (FRa & FRb & FRc).
                 split; [tr688 FRa MU1' WM1'; clear -LO; lia|]. split; [tr688 FRb MU1' WM1'; clear -LO; lia| tr688 FRc MU1' WM1'; clear -LO; lia]. }
        split; [exact EFR1|].
        split; [tr688 INS5 MU1' WM1'; clear -LO LOC CR; lia|].
        split; [tr688 PC0 MU1' WM1'; unfold BF_free6.PCB, kThrCache; clear -LO LOC CR Tlo Thi HC30; lia|].
        split; [eapply u32arr_transport; [exact ARR0| exact MU1'| exact WM1'|]; cbn [disjoint_from]; rewrite LEN; unfold BF_free6.PCB, kThrCache; clear -LO LOC CR Tlo Thi HC30; lia|].
        split; [tr688 CST0 MU1' WM1'; unfold kThrCache; clear -LO LOC CR Tlo Thi; lia|].
        tr688 RIC0 MU1' WM1'. unfold BF_free6.RIc. rewrite HRI. unfold kSpaceSize. unfold kSpaceSize in HSB. clear -LO LOC CR HSB HC30. repeat split; try exact I; lia. }
      { exact KIP0. }
      intros ms1 mo1 HQ1 AG1 KIP1. unfold QA in HQ1.
      destruct HQ1 as (m1 & j1 & j2 & j & -> & MI1 & SK1 & MU1 & WM1 & DF1 & EFR1 & INSm1 & PC1 & ARR1 & CST1 & RIC1).
      pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _). destruct KIP1 as [KIA1 POL1].
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK AG1 KIA1) as ATK1.
      assert (ATK1s : ATOKc R0 R0' (sA a s) mo1) by (change a with (aps_alloc s); rewrite BF_popT.sA_self; exact ATK1).
      pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 AK) as AK1.
      assert (P1EQ : forall x, P0 x -> acc_ok (m_vm_lazy mo1) (aSc s) x) by (intros x Hx; unfold P0, BF_caT.PP in Hx; rewrite Flz1; exact Hx).
      assert (KIP1' : KIP (aSc s) (aNc s) (aEBc s) P0 mo1) by (split; [exact KIA1| exact P1EQ]).
      pose proof (pop_statics_agree m m1 PST ltac:(intros z Hz; apply MU1; rewrite wa_unsigned by (clear -Hz; lia); unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite HRI; cbn [outside]; unfold kSpaceSize; clear -Hz LO LOC CR Timg Tlo HSB HC30; repeat split; try exact I; lia)) as PST1.
      assert (USP288 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; clear -LO LOC CR SPH; lia).
      (* [comment removed for export] *)
      unfold BF_free9.gregs.
      eapply (rzA_mm_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 (NMmap A 262144 3 MAP_FIXED_RW) (mmap_CHK A 262144 3 MAP_FIXED_RW) (dec_zs A 262144)
                (rar_map_gen_post (fun x r u => x = (r, u)) (wz 0x35968) (wz (usp + -288)) gp tp
                   (wz (mfa + 262144)) (wz (SB + c * 4294967296 + 3758096384 + mfa)) (wz 262144) (wz (BF_free6.RIc c RI)) (wz INST) (wz h) (wz (BF_free6.PCB CA c + 4 * h + 16)) (wz (nf + h))
                   (wz 2305843009213693952) (wz (SB + c * 4294967296 + 3758096384)) (wz 1152921504607895551) (wz 1152921504606846976) F fc A 262144 lo m1)
                _ mo1 K).
      * apply mm_node_mmap.
      * left. reflexivity.
      * eapply (rar_map_gen_specA P0 PDAT (dec_zs A 262144) (fun x r u => x = (r, u))); rewrite ?USP288;   (* [comment removed for export] *)
          [ intros rsp x Dx; destruct (dec_zs_Some _ _ _ _ Dx) as (r' & u' & -> & ->); exists r', u'; split; reflexivity
          | exact SK1 | exact LOC | clear -LO; lia | clear -SPH; lia | exact MI1 | exact (proj1 PST1)
          | subst A FA; reflexivity | reflexivity | exact HA3 | reflexivity
          | unfold b_image_end; exact HA1 | clear; lia | rewrite mmap_len_alignedA by reflexivity; unfold kSpaceSize in HA2, SB3; clear -HA2 SB3 LOC; lia
          | intros x k H1 H2; apply PSTK; [exact H1| clear -H2; lia] ].
      * exact KIP1'.
      * exact KN.
      * intros moK AGK KIAK.
        assert (SITE : commit_site E0 a A 262144).
        { left. unfold kResvLen, kPtrArrayLen, kPtrArrayCommit. unfold kSpaceSize in HA2, WE4. split; [subst A FA; clear -WE3 HA1 HSB HC30 MF0; lia|].
          split; [clear -HA2 WE4; lia|]. destruct (as_ptr_committed a =? 0); subst A FA; clear -WE20 HA2 WE3 WE4 HA1 HSB HC30 MF0; lia. }
        assert (GROWFA : forall mox mo', AKern E0 a mox -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mox) -> ivs_wf (vm_noaccess (m_vmmaps mox)) ->
           vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mox)) A (A + 262144) ->
           (forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mox) /\ elo e <= elo e' /\ ehi e' <= ehi e
                         /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + 262144 <= elo e'))) ->
           AKern E0 (st_fa c a) mo').
        { intros mox mo' Kx MAPS WFN NOACC LAV.
          eapply (AKern_grow_fa E0 a (st_fa c a) mox mo' A 262144 Kx WE MAPS ltac:(clear -HA1; lia) ltac:(clear; lia) WFN NOACC LAV
                    (fa_as_sec c a) (fa_as_node_blocks c a) (fa_as_store_blocks c a) c HC).
          - subst A FA mfa r. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset. clear; lia.
          - fold r. exact A5.
          - rewrite st_fa_region. cbn [rg_mapped_fa]. reflexivity.
          - rewrite st_fa_region. cbn [rg_mapped_user]. reflexivity.
          - intros c' Hc' NE. apply st_fa_other. clear -NE. lia.
          - apply fa_as_ptr_committed.
          - fold r mfa. unfold kRegionSize, kFreeArrayOffset. clear -MFR2. lia. }
        assert (LR : 262144 <= 4096 * R0) by (pose proof (gapP_nonneg a) as GP0; unfold kFreeArrayMapSize in RR; clear -GLE RR GD0 GP0 HCR; lia).
        destruct (commit_ks E0 FSB0 HR0 L0 RES0 EB0 HR0_ok RES0_low s [] D WF a (st_fa c a) mo1 R0 R0' A 262144 ATK1s AK1 HA3 eq_refl ltac:(clear; lia) LR
                    ltac:(clear -HA1; lia) ltac:(unfold kSpaceSize in HA2, SB3; clear -HA2 SB3; lia) SITE
                    (a_eager_bytes_st_fa E0 c a HC30) (fa_as_sec c a) (fa_as_residue c a) (fa_as_node_blocks c a) (fa_as_store_blocks c a)
                    GROWFA moK AGK KIAK) as (NU & GRT & ALL).
        split; [exact NU|]. split; [exact GRT|].
        intros eff mo' HC' NR. destruct (ALL eff mo' HC' NR) as (-> & ATK' & AK' & LZ & ES & FSK).
        exists (Z_to_bv 64 A, true).
        split. { replace (mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 262144)] [] [] []) with (zshape A 262144 (Z_to_bv 64 A) true)
                   by (unfold zshape; rewrite mmap_len_alignedA by reflexivity; reflexivity). apply dec_zs_zshape. }
        exists (aSc (sA (st_fa c a) s)), (aNc (sA (st_fa c a) s)), (aEBc (sA (st_fa c a) s)).
        split; [exact (proj1 (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK'))|].
        pose proof (magree_frame _ _ AGK) as (FfdsK & FvmK & FlzK & FfsK & FhK & FtidK & _).
        split. { intros x Hx. unfold P0, BF_caT.PP in Hx. apply LZ. rewrite FlzK, Flz1. eapply acc_ok_lazy_sub; [| exact ES| exact Hx]. intros e' He'; exists e'; split; [exact He'| clear; lia]. }
        intros ms3 mo3 HQ AG3 KIA3 POL3.
        destruct HQ as (r' & u' & m3 & ESK & MU3 & WM3 & MI3 & ST3 & ZB3 & HRR).
        injection HRR as <- <-.
        assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CR; lia).
        assert (RRV : rar_ret (Z_to_bv 64 A) = true) by (unfold rar_ret, is_err; rewrite UA; apply andb_true_intro; split; apply negb_true_iff; [apply Z.ltb_ge| apply Z.eqb_neq]; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CR; lia).
        assert (IE : is_err (Z_to_bv 64 A) = false) by (unfold is_err; rewrite UA; apply Z.ltb_ge; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CR; lia).
        destruct (ESK RRV) as ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & E) & SK3). clear ESK. subst ms3. specialize (ZB3 eq_refl). unfold rar_W in MU3. rewrite USP288 in MU3, SK3.
        rewrite mmap_len_alignedA in MU3, ZB3 by reflexivity.
        replace (ret_pc (wz 0x35968)) with (wz 0x35968 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
        set (a2 := st_fa c a) in *.
        pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK' AG3 KIA3) as ATK3.
        pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK') as AK3.
        assert (GR2 : gapR a2 = gapR a - 262144) by (subst a2; rewrite (gapR_st_fa E0 c a HC30); reflexivity).
        assert (GD2 : gapD a2 = gapD a) by (subst a2; apply gapD_st_fa).
        assert (GP2 : gapP a2 = gapP a) by (subst a2; unfold gapP; rewrite fa_as_ptr_committed; reflexivity).
        assert (TOK3 : RTOKc C C' (sA a2 s) mo3).
        { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 C C' (sA a2 s) mo3 (R0 - 262144 / 4096) R0' ATK3); cbn [aps_alloc sA aps_set_alloc];
            rewrite ?GR2, ?GD2, ?GP2; pose proof (gapP_nonneg a) as GP0; unfold kFreeArrayMapSize in RR; clear -HCR HCR' GLE GD0 GP0 RR; lia. }
        (* [comment removed for export] *)
        set (P3 := PP (sA a2 s) mo3).
        assert (KIP3 : KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 mo3) by (split; [exact KIA3| intros x Hx; exact Hx]).
        assert (AK3s : AKern E0 (aps_alloc (sA a2 s)) mo3) by exact AK3.
        assert (ENV3 : ENVOK E0 FSB0 (sA a2 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3).
        assert (PSTK3 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
        assert (PDAT3 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV3 ENV0); clear -H1 H2; lia. }
        assert (PRO3 : forall x k, 0x10000 <= x -> x + Z.of_nat k <= 0x31000 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV3 ENV0); clear -H1 H2; lia. }
        assert (PCA3 : forall x k, CA <= x -> x + Z.of_nat k <= CA + 2584 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE); unfold kThrCache in H1, H2; clear -H1 H2; lia. }
        assert (PRIR3 : forall x k, BF_free6.RIc c RI <= x -> x + Z.of_nat k <= BF_free6.RIc c RI + 128 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold BF_free6.RIc in H1, H2. rewrite HRI in H1, H2. unfold P3, BF_caT.PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a2 s) mo3 WE); change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
        assert (PFA3 : forall x k, FA <= x -> x + Z.of_nat k <= FA + mfa + 262144 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. destruct k as [|k']; [apply acc_ok_empty|].
          assert (HU : 0 < rg_mapped_fa (get_region a2 c)) by (subst a2; rewrite st_fa_region; cbn [rg_mapped_fa]; fold r mfa; unfold kFreeArrayMapSize; clear -MF0; lia).
          pose proof (ak_fa _ _ _ AK3 c HC HU) as U. pose proof (eager_rw_lazy_disjoint _ _ _ U) as LD.
          subst a2. rewrite st_fa_region in LD. cbn [rg_mapped_fa] in LD. fold r mfa in LD. unfold kFreeArrayMapSize in LD.
          unfold free_array, region_beg in LD. change kRegionSize with 4294967296 in LD. change kFreeArrayOffset with 3758096384 in LD. fold FA in LD.
          eapply (acc_ok_of_lazy_disjoint mo3 _ _ _ _ _ LD); subst FA; unfold kSpaceSize in HSB; clear -H1 H2 HSB HC30 MF0 MFR2 CR; lia. }
        assert (PSH3 : forall x k, kShadowBase + A / 8 <= x -> x + Z.of_nat k <= kShadowBase + A / 8 + 32768 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_space_shadow' E0 FSB0 HR0 (sA a2 s) mo3 WE); unfold kShadowBase in H1, H2; rewrite A_SB_val;
            change kSpaceSize with (2^37) in HA2; subst A FA; clear -H1 H2 HA1 HA2 SB1 HC30 MF0; Z.div_mod_to_equations; lia. }
        assert (PCTX3 : P3 (Z_to_bv 64 (CTX + 152), 8%nat)).
        { unfold P3, BF_caT.PP. apply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo3 AK3s c0 cl _ _ CR0); clear -CC1 CC2; cbn; lia. }
        assert (PT3 : forall x k, T <= x -> x + Z.of_nat k <= T + 4096 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE); assumption. }
        (* [comment removed for export] *)
        pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
        pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
        pose proof CR0 as (_ & _ & _ & CRS & _). pose proof DR0 as (_ & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
        destruct PL0OK as (_ & _ & _ & _ & _ & _ & [IA1 IA2]). pose proof WE as WEx.
        destruct WEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE25x & WE26x & WE27x & _ & _ & _ & _ & _ & _ & _ & WE35x).
        unfold app_mem in WE25x. rewrite ?KHB, ?KLE in WE25x. unfold img_sep in WE35x. rewrite EI1 in WE35x. unfold kIArenaLen in WE25x, WE26x, WE27x, WE35x, IA2.
        assert (PLC : placed_s CTX 4096).
        { apply placed_placed_s. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. clear -IA1 IA2 WE25x WE26x WE35x EI2. lia. }
        assert (HTSB : T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) by (unfold kSpaceSize; clear -WE19 G1 G3; lia).
        assert (HCSB : CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) by (unfold kSpaceSize; clear -WE27x IA1 IA2 G1 G3; lia).
        (* [comment removed for export] *)
        assert (AG03 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 688 \/ usp <= z) -> (z + 1 <= BF_free6.PCB CA c \/ BF_free6.PCB CA c + 4 <= z) ->
                      (z + 1 <= BF_free6.RIc c RI \/ BF_free6.RIc c RI + 8 <= z) -> (z + 1 <= A \/ A + 262144 <= z) -> m3 (wa z) = m (wa z)).
        { intros z Hz Z1 Z2 Z3 Z4. rewrite (MU3 (wa z)), (MU1 (wa z)); [reflexivity| |]; rewrite wa_unsigned by exact Hz; cbn [outside]; clear -Z1 Z2 Z3 Z4; repeat split; try exact I; lia. }
        Ltac tr3 H MA WA MB WB := eapply rw_cells_transport; [eapply rw_cells_transport; [exact H| exact MA| exact WA|]| exact MB| exact WB|]; unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length].
        assert (DF3 : BF_free6.drain_frames s5 s6 s7 s8 s9 s10 s11 usp CA c p RI m3 ra s0 s1 s2 s3 s4 j1 j2).
        { unfold BF_free6.drain_frames in DF1 |- *. destruct DF1 as (FRa & FRb & FRc).
          (* [comment removed for export] *)
          split; [eapply rw_cells_transport; [exact FRa| exact MU3| exact WM3|] | split; [eapply rw_cells_transport; [exact FRb| exact MU3| exact WM3|] | eapply rw_cells_transport; [exact FRc| exact MU3| exact WM3|]]];
            cbn [disjoint_from cells_size csize fst snd Nat.add length]; clear -LO LOC HA1 HA2 HSB; unfold kSpaceSize in *; lia. }
        assert (EFR3 : BF_free9.efa_frame usp c RI m3 j nf).
        { unfold BF_free9.efa_frame in EFR1 |- *. eapply rw_cells_transport; [exact EFR1| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize fst snd Nat.add length]; clear -LO LOC HA1 HA2 HSB; unfold kSpaceSize in *; lia. }
        assert (INS3 : rw_cells bsegs m3 0xaaf78 [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI); C1 (Z_to_bv 8 0)]).
        { eapply rw_cells_transport; [exact INSm1| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize fst snd Nat.add length]; clear -LO LOC CR HA1; lia. }
        assert (PC3' : rw_cells bsegs m3 (BF_free6.PCB CA c) [C4 (wz h); C4 (wz (2 * h)); C8 (wz size)]).
        { eapply rw_cells_transport; [exact PC1| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize fst snd Nat.add length]. unfold BF_free6.PCB, kThrCache. subst A FA.
          clear -LO LOC CR Tlo Thi HC30 HTSB HSB MF0 MFR2; unfold kSpaceSize in *; repeat split; try exact I; lia. }
        assert (ARR3 : u32arr bsegs m3 (BF_free6.PCB CA c + 16) (map (fun z : Z => wz z) l ++ junk)).
        { eapply u32arr_transport; [exact ARR1| exact MU3| exact WM3|]. cbn [disjoint_from]. rewrite LEN. unfold BF_free6.PCB, kThrCache. subst A FA.
          clear -LO LOC CR Tlo Thi HC30 HTSB HSB MF0 MFR2; unfold kSpaceSize in *; repeat split; try exact I; lia. }
        assert (CST3 : rw_cells bsegs m3 (CA + 2576) [C8 (wz (as_cache_allocated a))]).
        { eapply rw_cells_transport; [exact CST1| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize fst snd Nat.add length]. unfold kThrCache. subst A FA.
          clear -LO LOC CR Tlo Thi HTSB HSB MF0 HC30 MFR2; unfold kSpaceSize in *; repeat split; try exact I; lia. }
        assert (RIC3 : rw_cells bsegs m3 (BF_free6.RIc c RI) (ri_cells 1152921504606846976 nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr)).
        { eapply rw_cells_transport; [exact RIC1| exact MU3| exact WM3|]. unfold ri_cells. cbn [disjoint_from cells_size csize fst snd Nat.add length]. unfold BF_free6.RIc. rewrite HRI. subst A FA.
          clear -LO LOC CR HSB HC30 HA2; unfold kSpaceSize in *; lia. }
        assert (FAR3 : u32arr bsegs m3 FA (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536))).
        { apply u32arr_app.
          - eapply u32arr_transport; [eapply u32arr_transport; [exact FARR| exact MU1| exact WM1|]| exact MU3| exact WM3|]; cbn [disjoint_from];
              replace (4 * Z.of_nat (length fws)) with mfa by (symmetry; exact FLEN); unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI; subst A FA;
              clear -LO LOC CR Tlo Thi HC30 HTSB HSB MF0 MFR2; unfold kSpaceSize in *; lia.
          - replace (FA + 4 * Z.of_nat (length fws)) with A by (subst A; rewrite <- FLEN; clear; lia).
            apply (u32arr_of_zeros m3 A 262144 65536 ZB3); clear; lia. }
        pose proof (pop_statics_agree m m3 PST ltac:(intros z Hz; apply AG03; subst A FA; unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI; clear -Hz LO LOC CR Timg Tlo HSB HC30 MF0; unfold kSpaceSize in *; lia)) as PST3.
        assert (TC3 : thread_cells m3 tp 0x6028f8 CTX T).
        { destruct TC as (X1 & X2 & X3 & X4 & X5). unfold thread_cells. rewrite TP in X3 |- *. rewrite unsigned_lit in X3 |- * by (clear; lia).
          assert (AGI : forall z, 0x10000 <= z < 0x603000 -> m3 (wa z) = m (wa z)).
          { intros z Hz. apply AG03; subst A FA; unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI; clear -Hz LO LOC CR Timg Tlo HSB HC30 MF0; unfold kSpaceSize in *; lia. }
          split; [eapply rw_cells_agree; [| exact X1]; cbn; intros z Hz; apply AGI; clear -Hz; lia|].
          split; [eapply rw_cells_agree; [| exact X2]; cbn; intros z Hz; apply AGI; clear -Hz; lia|].
          split; [eapply rw_cells_agree; [| exact X3]; cbn; intros z Hz; apply AGI; clear -Hz; lia|].
          split; [eapply rw_cells_agree; [| exact X4]; cbn; intros z Hz; apply AGI; clear -Hz; lia|].
          eapply rw_cells_agree; [| exact X5]; cbn; intros z Hz. apply AG03; subst A FA; unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI;
            clear -Hz LO LOC CR CT CQ1 CQ2 CC1 CC2 CRS G1 G3 HSB HC30 MF0 MFR2; unfold kSpaceSize in *; lia. }
        (* [comment removed for export] *)
        assert (SHJ : rw_cells bsegs m (kShadowBase + A / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0) (Z.to_nat 32768))]).
        { apply (BF_tkit.shadow_join m kShadowBase (A / 8) (Z.to_nat 32768) 0); [| clear; lia]. intros g Hg. apply (Rsh g 0).
          apply (Sh_beyond_fa E0 [] D a WF c (8 * g) HC); [| unfold region_of; fold r; exact RFA]. unfold region_of. fold r mfa. subst A FA.
          unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArrayMapSize. clear -Hg HA8 MF0. rewrite Z2Nat.id in Hg by (clear; lia). Z.div_mod_to_equations. lia. }
        assert (SHJ3 : rw_cells bsegs m3 (kShadowBase + A / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0) (Z.to_nat 32768))]).
        { tr3 SHJ MU1 WM1 MU3 WM3; rewrite ?Nat.add_0_r, ?repeat_length, ?(Z2Nat.id 32768) by (clear; lia); unfold kShadowBase, BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI; subst A FA;
            rewrite KHB in HSBH; clear -LO LOC CR HSB HSBH HC30 MF0 MFR2 Tband Tlo Thi; unfold kSpaceSize, A_LOWAPP_END, A_HIGH_BEG in *; repeat split; try exact I; Z.div_mod_to_equations; lia. }
        set (nmaps := ts_mmaps (as_ts a) mod 2^64). set (nmapped := ts_mmaped (as_ts a) mod 2^64).
        assert (TST : rw_cells bsegs m (T + 2872) [C8 (wz nmaps); C8 (wz nmapped)]).
        { pose proof (BF_tkit.u64arr_cell m _ _ 9 _ Tst eq_refl) as X9. pose proof (BF_tkit.u64arr_cell m _ _ 10 _ Tst eq_refl) as X10.
          pose proof (BF_kit3.rwc_join_at bsegs m _ _ _ _ X9 X10 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X.
          replace (T + 2800 + 8 * Z.of_nat 9) with (T + 2872) in X by (clear; lia). subst nmaps nmapped. rewrite !BF_popT.wz_mod. exact X. }
        assert (TST3 : rw_cells bsegs m3 (T + 2872) [C8 (wz nmaps); C8 (wz nmapped)]).
        { tr3 TST MU1 WM1 MU3 WM3; unfold BF_free6.PCB, BF_free6.RIc, kThrCache; rewrite ?HRI; subst A FA; clear -LO LOC CR HSB HTSB HC30 MF0 MFR2 Tlo Thi; unfold kSpaceSize in *; repeat split; try exact I; lia. }
        (* [comment removed for export] *)
        set (Qg := fun ms' : machine_state => exists (m4 : mem) (t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word),
            ms' = MS (mkR ra (wz usp) gp tp t0x t1x t2x s0 s1 a0x a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x) F (ret_pc ra) fc None m4 (seg_rom bsegs)
            /\ mem_inv bsegs m4 /\ stk bsegs m4 lo usp
            /\ munch [(usp - 688, usp); (BF_free6.RIc c RI, BF_free6.RIc c RI + 8); (BF_free6.RIc c RI + 16, BF_free6.RIc c RI + 32); (BF_free6.RIc c RI + 80, BF_free6.RIc c RI + 88); (BF_free6.PCB CA c, BF_free6.PCB CA c + 4);
                      (BF_free6.PCB CA c + 16 + 4 * h, BF_free6.PCB CA c + 16 + 4 * h + 4); (CA + 2576, CA + 2584); (FA + 4 * nf, FA + 4 * (nf + h));
                      (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888)] m3 m4
            /\ wmono bsegs m3 m4
            /\ rw_cells bsegs m4 (BF_free6.PCB CA c) [C4 (wz (h + 1)); C4 (wz (2 * h)); C8 (wz size)]
            /\ u32arr bsegs m4 (BF_free6.PCB CA c + 16) (upd (map (fun z : Z => wz z) l ++ junk) (Z.to_nat h) (wz (BF_free6.xc SB c p)))
            /\ rw_cells bsegs m4 (CA + 2576) [C8 (wz (as_cache_allocated a - size))]
            /\ rw_cells bsegs m4 (BF_free6.RIc c RI) (ri_cells 0 (nf + h) (mfa + 262144) (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (nfr + h))
            /\ u32arr bsegs m4 FA (cpn (Z.to_nat h) (map (fun z : Z => wz z) l ++ junk) (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)) (Z.to_nat h) (Z.to_nat nf))
            /\ rw_cells bsegs m4 (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))]
            /\ rw_cells bsegs m4 (T + 2872) [C8 (wz (nmaps + 1)); C8 (wz (nmapped + 262144))]).
        eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 Qg).
        { subst A.
          eapply (rta_after_grow P3 gp tp s5 s6 s7 s8 s9 s10 s11 F fc usp lo CA SB c p RI LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) SPA HSB HSBH HC HCA HCASB HP HRI PSTK3 PDAT3 PRO3 PCA3 PRIR3
                    m3 ra s0 s1 s2 s3 s4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 h (as_cache_allocated a) nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr (wz size)
                    (map (fun z : Z => wz z) l ++ junk) fws (repeat (Z_to_bv 8 0) (Z.to_nat 32768)) j1 j2 j 0x6028f8 CTX T nmaps nmapped Qg MI3 SK3 DF3 EFR3 INS3 PC3' HR ARR3 LEN SMALL CST3 RIC3
                    ltac:(clear -NF0; lia) NFR FAR3 FLEN ltac:(subst nf mfa; exact A8) GROW MFM MFR2 PFA3 ST3 (proj2 PST3) SHJ3 PSH3 TC3 ltac:(clear; lia) ltac:(clear; lia) PLC TR2
                    ltac:(rewrite TP, unsigned_lit by (clear; lia); clear; lia) CT HTSB HCSB PCTX3 PT3 TST3 ltac:(subst nmaps; apply Z.mod_pos_bound; clear; lia) ltac:(subst nmapped; apply Z.mod_pos_bound; clear; lia)
                    ltac:(unfold kThrCache; reflexivity)).
          intros m4 t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x MI4 SK4 STA4 MU4 WM4 INS4' PC4 ARR4 CST4 RIC4 FAR4 SHP4 PG4 TC4 TST4.
          apply evtA_done. unfold Qg. exists m4, t0x, t1x, t2x, a0x, a1x, a2x, a3x, a4x, a5x, a6x, a7x, t3x, t4x, t5x, t6x.
          rewrite unsigned_lit in CST4 by (clear -CS; lia).
          (* [comment removed for export] *)
          split; [reflexivity|]. split; [exact MI4|]. split; [exact SK4|]. split; [exact MU4|]. split; [exact WM4|]. split; [exact PC4|]. split; [exact ARR4|].
          split; [exact CST4|]. split; [exact RIC4|]. split; [exact FAR4|]. split; [exact SHP4| exact TST4]. }
        { exact KIP3. }
        intros ms4 mo4 HQ4 AG4 KIP4. unfold Qg in HQ4.
        destruct HQ4 as (m4 & t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & -> & MI4 & SK4 & MU4 & WM4 & ROW4 & ARR4 & CST4 & RIC4 & FAR4 & SHP4 & TST4).
        pose proof (magree_frame _ _ AG4) as (Ffds4 & Fvm4 & Flz4 & Ffs4 & Fh4 & Ftid4 & _). destruct KIP4 as [KIA4 _].
        set (a' := push_st E0 c p (rta_st c l2 (st_fa c (dr_st c a)))).
        (* [comment removed for export] *)
        assert (EARR : upd (map (fun z : Z => wz z) l ++ junk) (Z.to_nat h) (wz (BF_free6.xc SB c p)) = map (fun z : Z => wz z) (l1 ++ [compact_of_chunk SB c p]) ++ (map (fun z : Z => wz z) l2' ++ junk)).
        { rewrite El. subst l2. rewrite !map_app. cbn [map]. rewrite <- !app_assoc. cbn [app].
          replace (Z.to_nat h) with (length (map (fun z : Z => wz z) l1)) by (rewrite length_map; exact LEN1).
          replace (BF_free6.xc SB c p) with (compact_of_chunk SB c p) by (unfold BF_free6.xc, compact_of_chunk, region_beg, kRegionSize; f_equal; clear; lia).
          pose proof (BF_popT.upd_app_mid (map (fun z : Z => wz z) l1) (map (fun z : Z => wz z) l2' ++ junk) (wz x0) (wz (compact_of_chunk SB c p))) as X. cbn [app] in X. exact X. }
        rewrite EARR in ARR4.
        (* [comment removed for export] *)
        set (fjz := fjunk ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)).
        assert (FJL : (Z.to_nat h <= length fjz)%nat) by (subst fjz; rewrite length_app, repeat_length; clear -HR; lia).
        assert (EFAR : cpn (Z.to_nat h) (map (fun z : Z => wz z) l ++ junk) (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)) (Z.to_nat h) (Z.to_nat nf) = map (fun z : Z => wz z) (rg_free r ++ l2) ++ skipn (Z.to_nat h) fjz).
        { pose proof (cpn_app (map (fun z : Z => wz z) l2) (map (fun z : Z => wz z) l1) junk (map (fun z : Z => wz z) (rg_free r)) (firstn (Z.to_nat h) fjz) (skipn (Z.to_nat h) fjz)
                        ltac:(rewrite firstn_length_le, length_map; [symmetry; exact LEN2| exact FJL])) as X.
          rewrite !length_map, LEN2, LEN1, LENF in X.
          subst fws. change AsanRep.zw with (fun z : Z => wz z). rewrite El, !map_app, <- !app_assoc. fold fjz.
          rewrite <- (firstn_skipn (Z.to_nat h) fjz) at 1. exact X. }
        rewrite EFAR in FAR4.
        (* [comment removed for export] *)
        assert (AGW : forall z, 0 <= z < 2^64 -> ~ FPW6 a lo c true z -> m4 (wa z) = m (wa z)).
        { intros z Hz NF. unfold FPW6, kThrCache, kPerClassSize, kThrCacheStats, kRegSize, kThrStats in NF. cbv zeta in NF. fold r nf in NF. rewrite HFA' in NF. fold FA mfa in NF.
          rewrite (MU4 (wa z)); [apply AG03; [exact Hz| | | |]|]; try (rewrite wa_unsigned by exact Hz; cbn [outside]);
            unfold BF_free6.RIc, BF_free6.PCB, kThrCache; subst A; unfold kFreeArrayMapSize in NF; clear -NF LO Hz HR HC30; repeat split; try exact I; lia. }
        pose proof (renv_of D a mo WF AK EI1 EI2) as RENV.
        assert (GR' : get_region a' c = mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ l2) (mfa + kFreeArrayMapSize) (rg_n_allocated r) (rg_n_freed r + h)).
        { subst a'. rewrite push_get_region, rta_get_region_eq, st_fa_region, dr_get_region. fold r. cbv zeta. cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed]. rewrite ZL2. reflexivity. }
        assert (REP4 : ARep bsegs E0 (DepotR bsegs E0) a' m4).
        { subst a'. rewrite <- El2c. apply (R6 a m m4 lo c p D (map (fun z : Z => wz z) l2' ++ junk) (skipn (Z.to_nat h) fjz) true HC CI FULL AV REP WF RENV (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM3 WM4)) AGW LOC);
            fold l r h size; rewrite ?HFA'; fold FA; rewrite ?El2c.
          - unfold kPerClassSize. rewrite MC. unfold BF_free6.PCB, kThrCache in ROW4 |- *. exact ROW4.
          - unfold kPerClassSize. fold l1. unfold BF_free6.PCB, kThrCache in ARR4 |- *. exact ARR4.
          - rewrite length_app, length_map. unfold l2 in LEN2. cbn [length] in LEN2. clear -CLEN LENl LEN2 HR. lia.
          - unfold kThrCacheStats. unfold kThrCache in CST4. replace (T + (208 + 2560) + 16) with (T + 208 + 2576) by (clear; lia). exact CST4.
          - rewrite GR'. match goal with |- rw_cells _ _ _ (region_cells ?rr) => change (region_cells rr) with (C8 (Z_to_bv 64 0) :: List.tl (region_cells rr)); rewrite (pop_row 0 rr) end.
            cbn [rg_num_freed rg_mapped_fa rg_alloc_user rg_mapped_user rg_n_allocated rg_n_freed rg_free].
            unfold rg_num_freed. rewrite length_app, LENF. unfold l2 in LEN2 |- *. rewrite LEN2. replace (Z.of_nat (Z.to_nat nf + Z.to_nat h)) with (nf + h) by (clear -NF0 HR; lia).
            unfold kRegSize, ri_cells, kFreeArrayMapSize. rewrite <- (BF_popT.wz_mod_add (rg_n_freed r) h). fold nfr. unfold BF_free6.RIc, ri_cells in RIC4. exact RIC4.
          - exact FAR4.
          - cbn [rg_mapped_fa]. rewrite length_app. rewrite length_skipn. subst fjz. rewrite length_app, repeat_length, LENF. unfold l2 in LEN2. rewrite LEN2.
            unfold kFreeArrayMapSize. try subst mfa. try subst nf. clear -FAL NF0 HR. unfold rg_num_freed in *. lia.
          - intros _. split.
            + unfold kThrStats, kFreeArrayMapSize. replace (T + 2800 + 72) with (T + 2872) by (clear; lia). subst nmaps nmapped. rewrite !BF_popT.wz_mod_add in TST4. exact TST4.
            + change (Z.to_nat (kFreeArrayMapSize / 8)) with (Z.to_nat 32768). change kAsanHeapLeftRedzoneMagic with 250. fold mfa. exact SHP4.
          - intros _. fold mfa. subst mfa. exact RFA. }
        assert (GROW' : rg_mapped_fa (get_region a c) < 4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a))) by (fold r; rewrite El2c, ZL2; exact GROW).
        assert (ONE' : 4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a)) <= rg_mapped_fa (get_region a c) + kFreeArrayMapSize) by (fold r; rewrite El2c, ZL2; exact ONE).
        pose proof (run_ldc_drain_grant E0 c p a [] HC CI FULL GROW' ONE' ltac:(fold r; exact A5) ltac:(fold r; exact A6) ltac:(fold r; exact RFA)) as RUN. cbv zeta in RUN. rewrite El2c in RUN. fold a' in RUN.
        pose proof (hoare_arun _ _ _ a 1%nat _ a' tt _ [] (local_dealloc_spec E0 [] D a c p HC WF AV) eq_refl RUN) as (WF' & PF' & CVM' & CI').
        pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG4 KIA4) as TOK4.
        assert (GRo : forall c', c' <> c -> get_region a' c' = get_region a c').
        { intros c' NE. subst a'. rewrite push_get_region, rta_get_region_ne, st_fa_other, dr_get_region by (clear -NE; lia). reflexivity. }
        assert (GMU : forall c', rg_mapped_user (get_region a' c') = rg_mapped_user (get_region a2 c') /\ rg_mapped_fa (get_region a' c') = rg_mapped_fa (get_region a2 c')).
        { intros c'. subst a2. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GR', st_fa_region; cbn [rg_mapped_user rg_mapped_fa]; fold r mfa; split; reflexivity| rewrite (GRo c' NE), st_fa_other by (clear -NE; lia); split; reflexivity]. }
        pose proof (regions_bytes_ext a2 a' GMU) as RB'. pose proof (regions_bytes_st_fa E0 c a HC30) as RB2. fold a2 in RB2.
        assert (TOK4' : RTOKc C C' (sA a' s) mo4).
        { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a2 a' mo4); [exact TOK4| | |]; subst a' a2.
          - unfold same_fp. rewrite push_as_sec, push_as_ptr_committed, push_as_residue, push_as_node_blocks, push_as_store_blocks,
                                      rta_as_sec, rta_as_ptr_committed, rta_as_residue, rta_as_node_blocks, rta_as_store_blocks,
                                      !fa_as_sec, !fa_as_ptr_committed, !fa_as_residue, !fa_as_node_blocks, !fa_as_store_blocks,
                                      dr_as_sec, dr_as_ptr_committed, dr_as_residue, dr_as_node_blocks, dr_as_store_blocks.
            repeat split; try reflexivity. exact RB'.
          - rewrite push_as_nprim_ever, rta_as_nprim_ever, !fa_as_nprim_ever, dr_as_nprim_ever. reflexivity.
          - rewrite push_as_ndepot_ins, rta_as_ndepot_ins, !fa_as_ndepot_ins, dr_as_ndepot_ins. reflexivity. }
        eapply KONT. unfold ldc_post. split; [exists 1%nat, [AnsOk (free_array SB c + rg_mapped_fa (get_region a c))]; eexists; exists []; exact RUN|].
        split; [exact REP4|]. split; [exact WF'|].
        split. { apply (AKern_ext2 E0 a2 a'); [intros c'; apply (proj1 (GMU c'))| intros c'; apply (proj2 (GMU c'))
                 | subst a' a2; rewrite push_as_ptr_committed, rta_as_ptr_committed, !fa_as_ptr_committed, dr_as_ptr_committed; reflexivity
                 | subst a' a2; rewrite push_as_sec, rta_as_sec, !fa_as_sec, dr_as_sec; reflexivity
                 | subst a' a2; rewrite push_as_node_blocks, rta_as_node_blocks, !fa_as_node_blocks, dr_as_node_blocks; reflexivity
                 | subst a' a2; rewrite push_as_store_blocks, rta_as_store_blocks, !fa_as_store_blocks, dr_as_store_blocks; reflexivity|].
                 exact (AKern_frame _ _ _ _ Fvm4 Flz4 AK3). }
        split; [exact TOK4'|].
        pose proof FSK as (Kfs & Kfds & Ktid).
        split; [rewrite Ffs4, Ffs3, Kfs, FfsK; exact Ffs1|]. split; [rewrite Ffds4, Ffds3, Kfds, FfdsK; exact Ffds1|]. split; [rewrite Ftid4, Ftid3, Ktid, FtidK; exact Ftid1|].
        split; [exact SK4|]. split; [exact MI4|].
        split. { apply (rt_misc5_agree E0 FSB0 PL0 m m4 RT). intros z Hz.
                 destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
                 - rewrite (MU4 (wa z)); [apply AG03; [clear -ZI; lia| | | |]|]; try (rewrite wa_unsigned by (clear -ZI; lia); cbn [outside]);
                     unfold BF_free6.RIc, BF_free6.PCB, kThrCache; rewrite ?HRI; subst A FA; unfold kShadowBase;
                     clear -ZI LO LOC CR Timg Tlo Thi Tband HSB HSBH HC30 HR MF0 MFR2 NF0 A8 KHB;
                     unfold kSpaceSize, A_LOWAPP_END, A_HIGH_BEG in *; rewrite ?KHB in *; repeat split; try exact I; lia.
                 - unfold rt_high2 in RH.
                   (* [comment removed for export] *)
                   destruct RH as [[RHT|RHT]|[RHC|RHD]];
                   (rewrite (MU4 (wa z));
                     [apply AG03; [first [clear -RHT Tlo Thi CR| clear -RHC CQ1 CQ2 CC1 CC2 CR| clear -RHD DQ1 DQ2 DD1 DD2 CR]; lia| | | |]|];
                     try (rewrite wa_unsigned by (first [clear -RHT Tlo Thi CR| clear -RHC CQ1 CQ2 CC1 CC2 CR| clear -RHD DQ1 DQ2 DD1 DD2 CR]; lia); cbn [outside]);
                     unfold BF_free6.RIc, BF_free6.PCB, kThrCache; rewrite ?HRI; subst A FA; unfold kShadowBase;
                     first [ clear -RHT LO LOC CR Timg Tlo Thi Tband G1 G3 WE19 HSB HSBH HC30 HR MF0 MFR2 NF0 A8 KHB
                           | clear -RHC LO LOC CR Timg Tlo Thi Tband CT CQ1 CQ2 CQ4 CC1 CC2 CRS G1 G3 WE19 HSB HSBH HC30 HR MF0 MFR2 NF0 A8 KHB
                           | clear -RHD LO LOC CR Timg Tlo Thi Tband DT DQ1 DQ2 DQ4 DD1 DD2 DRS G1 G3 WE19 HSB HSBH HC30 HR MF0 MFR2 NF0 A8 KHB ];
                     unfold kSpaceSize, A_LOWAPP_END, A_HIGH_BEG in *; rewrite ?KHB in *; repeat split; try exact I; lia). }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM3 WM4))|].
        split. { eapply munch_trans; [eapply munch_cover; [exact MU1|]| eapply munch_trans; [eapply munch_cover; [exact MU3|]| eapply munch_cover; [exact MU4|]]];
                   unfold ldc_W, K_LDC, kThrCache, kPerClassSize, kThrCacheStats, kRegSize, kThrStats, kFreeArrayMapSize; cbv zeta; fold r nf h; rewrite ?HFA'; fold FA mfa; subst A;
                   unfold BF_free6.RIc, BF_free6.PCB, kThrCache; clear -LO HR HC30; solve_covers. }
        subst a' a2. unfold ldc_same.
        rewrite push_as_chunks, push_as_dead, push_as_tq, push_as_gq, push_as_sec, push_as_ptr_committed, push_as_sec_stats, push_as_sec_stale, push_as_glob_allocated, push_as_glob_mapped,
                push_as_nprim_ever, push_as_residue, push_as_everc, push_as_ndepot_ins, push_as_node_blocks, push_as_store_blocks, push_as_keys, push_as_frames, push_as_store_stored,
                push_as_cache_inited, push_as_cache_mapped, push_as_ia_inited, push_as_oom,
                rta_as_chunks, rta_as_dead, rta_as_tq, rta_as_gq, rta_as_sec, rta_as_ptr_committed, rta_as_sec_stats, rta_as_sec_stale, rta_as_glob_allocated, rta_as_glob_mapped,
                rta_as_nprim_ever, rta_as_residue, rta_as_everc, rta_as_ndepot_ins, rta_as_node_blocks, rta_as_store_blocks, rta_as_keys, rta_as_frames, rta_as_store_stored,
                rta_as_cache_inited, rta_as_cache_mapped, rta_as_ia_inited, rta_as_oom,
                fa_as_chunks, fa_as_dead, fa_as_tq, fa_as_gq, fa_as_sec, fa_as_ptr_committed, fa_as_sec_stats, fa_as_sec_stale, fa_as_glob_allocated, fa_as_glob_mapped,
                fa_as_nprim_ever, fa_as_residue, fa_as_everc, fa_as_ndepot_ins, fa_as_node_blocks, fa_as_store_blocks, fa_as_keys, fa_as_frames, fa_as_store_stored,
                fa_as_cache_inited, fa_as_cache_mapped, fa_as_ia_inited, fa_as_oom,
                dr_as_chunks, dr_as_dead, dr_as_tq, dr_as_gq, dr_as_sec, dr_as_ptr_committed, dr_as_sec_stats, dr_as_sec_stale, dr_as_glob_allocated, dr_as_glob_mapped,
                dr_as_nprim_ever, dr_as_residue, dr_as_everc, dr_as_ndepot_ins, dr_as_node_blocks, dr_as_store_blocks, dr_as_keys, dr_as_frames, dr_as_store_stored,
                dr_as_cache_inited, dr_as_cache_mapped, dr_as_ia_inited, dr_as_oom.
        rewrite RB', RB2, GR'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa].
        repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact CI.
        -- intros c' NE. split; [exact (GRo c' ltac:(clear -NE; lia))|]. rewrite push_get_cache_ne, rta_get_cache, fa_get_cache, dr_get_cache_ne by (clear -NE; lia). reflexivity.
        -- subst mfa r. unfold kFreeArrayMapSize. clear; lia.
        -- subst mfa r. clear; lia.
    + (* [comment removed for export] *)
      set (Qn := fun ms' : machine_state => exists (m' : mem) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
          ms' = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
          /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ munch [(usp - 688, usp); (BF_free6.RIc c RI, BF_free6.RIc c RI + 8); (BF_free6.RIc c RI + 16, BF_free6.RIc c RI + 24); (BF_free6.RIc c RI + 80, BF_free6.RIc c RI + 88);
                    (BF_free6.PCB CA c, BF_free6.PCB CA c + 4); (BF_free6.PCB CA c + 16 + 4 * h, BF_free6.PCB CA c + 16 + 4 * h + 4); (CA + 2576, CA + 2584); (FA + 4 * nf, FA + 4 * (nf + h))] m m'
          /\ wmono bsegs m m'
          /\ rw_cells bsegs m' (BF_free6.PCB CA c) [C4 (wz (h + 1)); C4 (wz (2 * h)); C8 (wz size)]
          /\ u32arr bsegs m' (BF_free6.PCB CA c + 16) (upd (map (fun z : Z => wz z) l ++ junk) (Z.to_nat h) (wz (BF_free6.xc SB c p)))
          /\ rw_cells bsegs m' (CA + 2576) [C8 (wz (as_cache_allocated a - size))]
          /\ rw_cells bsegs m' (BF_free6.RIc c RI) (ri_cells 0 (nf + h) mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (nfr + h))
          /\ u32arr bsegs m' FA (cpn (Z.to_nat h) (map (fun z : Z => wz z) l ++ junk) fws (Z.to_nat h) (Z.to_nat nf))).
      eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 Qn).
      { rewrite HFA' in PFA, FARR.
        eapply (ldc_drain_nogrow P0 gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p RI LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) SPA HSB HC HCA HCASB HP HRI PSTK PDAT PRO PCA PRIR
                  m ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 h (as_cache_allocated a) nf mfa (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) nfr (wz size)
                  (map (fun z : Z => wz z) l ++ junk) fws Qn MI SK INS4);
          [unfold BF_free6.PCB, kThrCache in ROW |- *; exact ROW| exact HR| unfold BF_free6.PCB; unfold kThrCache in CARR |- *; exact CARR| exact LEN| exact SMALL| exact CST| exact RIC
          | exact NF0| exact NFR| exact FARR| exact FLEN| exact NOGROW| exact MFR| exact PFA| exact GPS| exact VPS|].
        intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' MI' SK' MU' WM' INS' ROW' ARR' CST' RIC' FAR' G1' V1'.
        apply evtA_done. unfold Qn. exists m', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7'.
        rewrite unsigned_lit in CST' by (clear -CS; lia). rewrite <- HFA' in FAR', MU'.
        repeat match goal with |- _ /\ _ => split end; first [reflexivity| assumption]. }
      { exact KIP0. }
      intros ms1 mo1 HQ1 AG1 KIP1. unfold Qn in HQ1.
      destruct HQ1 as (m1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & MI1 & SK1 & MU1 & WM1 & ROW1 & ARR1 & CST1 & RIC1 & FAR1).
      pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _). destruct KIP1 as [KIA1 _].
      set (a' := push_st E0 c p (rta_st c l2 (dr_st c a))).
      (* [comment removed for export] *)
      assert (EARR : upd (map (fun z : Z => wz z) l ++ junk) (Z.to_nat h) (wz (BF_free6.xc SB c p)) = map (fun z : Z => wz z) (l1 ++ [compact_of_chunk SB c p]) ++ (map (fun z : Z => wz z) l2' ++ junk)).
      { rewrite El. subst l2. rewrite !map_app. cbn [map]. rewrite <- !app_assoc. cbn [app].
        replace (Z.to_nat h) with (length (map (fun z : Z => wz z) l1)) by (rewrite length_map; exact LEN1).
        replace (BF_free6.xc SB c p) with (compact_of_chunk SB c p) by (unfold BF_free6.xc, compact_of_chunk, region_beg, kRegionSize; f_equal; clear; lia).
        pose proof (BF_popT.upd_app_mid (map (fun z : Z => wz z) l1) (map (fun z : Z => wz z) l2' ++ junk) (wz x0) (wz (compact_of_chunk SB c p))) as X. cbn [app] in X. exact X. }
      rewrite EARR in ARR1.
      (* [comment removed for export] *)
      assert (FJL : (Z.to_nat h <= length fjunk)%nat) by (clear -FAL NOGROW LENF HR NF0; subst nf; unfold rg_num_freed in *; lia).
      assert (EFAR : cpn (Z.to_nat h) (map (fun z : Z => wz z) l ++ junk) fws (Z.to_nat h) (Z.to_nat nf) = map (fun z : Z => wz z) (rg_free r ++ l2) ++ skipn (Z.to_nat h) fjunk).
      { pose proof (cpn_app (map (fun z : Z => wz z) l2) (map (fun z : Z => wz z) l1) junk (map (fun z : Z => wz z) (rg_free r)) (firstn (Z.to_nat h) fjunk) (skipn (Z.to_nat h) fjunk)
                      ltac:(rewrite firstn_length_le, length_map; [symmetry; exact LEN2| exact FJL])) as X.
        rewrite !length_map, LEN2, LEN1, LENF in X.
        subst fws. change AsanRep.zw with (fun z : Z => wz z). rewrite El, !map_app, <- !app_assoc.
        rewrite <- (firstn_skipn (Z.to_nat h) fjunk) at 1. exact X. }
      rewrite EFAR in FAR1.
      assert (AGW : forall z, 0 <= z < 2^64 -> ~ FPW6 a lo c false z -> m1 (wa z) = m (wa z)).
      { intros z Hz NF. apply MU1. rewrite wa_unsigned by exact Hz. unfold FPW6, kThrCache, kPerClassSize, kThrCacheStats, kRegSize in NF. cbv zeta in NF. fold r FA nf in NF.
        unfold BF_free6.RIc, BF_free6.PCB, kThrCache. cbn [outside]. clear -NF LO Hz HR HC30. repeat split; try exact I; lia. }
      pose proof (renv_of D a mo WF AK EI1 EI2) as RENV.
      assert (GR' : get_region a' c = mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ l2) mfa (rg_n_allocated r) (rg_n_freed r + h)).
      { subst a'. rewrite push_get_region, rta_get_region_eq, dr_get_region. fold r. cbv zeta. rewrite ZL2. reflexivity. }
      assert (REP1 : ARep bsegs E0 (DepotR bsegs E0) a' m1).
      { subst a'. rewrite <- El2c. apply (R6 a m m1 lo c p D (map (fun z : Z => wz z) l2' ++ junk) (skipn (Z.to_nat h) fjunk) false HC CI FULL AV REP WF RENV WM1 AGW LOC); fold l r h FA size; rewrite ?El2c.
        - unfold kPerClassSize. rewrite MC. unfold BF_free6.PCB, kThrCache in ROW1 |- *. exact ROW1.
        - unfold kPerClassSize. fold l1. unfold BF_free6.PCB, kThrCache in ARR1 |- *. exact ARR1.
        - rewrite length_app, length_map. unfold l2 in LEN2. cbn [length] in LEN2. clear -CLEN LENl LEN2 HR. lia.
        - unfold kThrCacheStats. unfold kThrCache in CST1. replace (T + (208 + 2560) + 16) with (T + 208 + 2576) by (clear; lia). exact CST1.
        - rewrite GR'. match goal with |- rw_cells _ _ _ (region_cells ?rr) => change (region_cells rr) with (C8 (Z_to_bv 64 0) :: List.tl (region_cells rr)); rewrite (pop_row 0 rr) end.
          cbn [rg_num_freed rg_mapped_fa rg_alloc_user rg_mapped_user rg_n_allocated rg_n_freed rg_free].
          unfold rg_num_freed. rewrite length_app, LENF, LEN2. replace (Z.of_nat (Z.to_nat nf + Z.to_nat h)) with (nf + h) by (clear -NF0 HR; lia).
          unfold kRegSize, ri_cells. rewrite <- (BF_popT.wz_mod_add (rg_n_freed r) h). fold nfr. unfold BF_free6.RIc, ri_cells in RIC1. exact RIC1.
        - exact FAR1.
        - cbn [rg_mapped_fa]. rewrite length_app. match goal with |- ?g => idtac "LENGOAL"; idtac g end. rewrite length_skipn.  match goal with |- ?g => idtac "LENGOAL"; idtac g end. rewrite LENF. unfold l2 in LEN2. rewrite LEN2. clear -FAL FJL NF0 HR. unfold rg_num_freed in *. lia.
        - intros X; discriminate X.
        - intros X; discriminate X. }
      assert (ROOM' : 4 * (rg_num_freed (get_region a c) + zlen (dr_chunks c a)) <= rg_mapped_fa (get_region a c)) by (fold r; rewrite El2c, ZL2; exact NOGROW).
      pose proof (run_ldc_drain_nogrow E0 c p a [] HC CI FULL ROOM') as RUN. cbv zeta in RUN. rewrite El2c in RUN. fold a' in RUN.
      pose proof (hoare_arun _ _ _ a 0%nat [] a' tt [] [] (local_dealloc_spec E0 [] D a c p HC WF AV) eq_refl RUN) as (WF' & PF' & CVM' & CI').
      pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
      assert (GRo : forall c', c' <> c -> get_region a' c' = get_region a c').
      { intros c' NE. subst a'. rewrite push_get_region, rta_get_region_ne, dr_get_region by (clear -NE; lia). reflexivity. }
      assert (GMU : forall c', rg_mapped_user (get_region a' c') = rg_mapped_user (get_region a c') /\ rg_mapped_fa (get_region a' c') = rg_mapped_fa (get_region a c')).
      { intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GR'; split; reflexivity| rewrite (GRo c' NE); split; reflexivity]. }
      pose proof (regions_bytes_ext a a' GMU) as RB'.
      assert (TOK1' : RTOKc C C' (sA a' s) mo1).
      { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a' mo1).
        - change a with (aps_alloc s). rewrite BF_popT.sA_self. exact TOK1.
        - subst a'. unfold same_fp. rewrite push_as_sec, push_as_ptr_committed, push_as_residue, push_as_node_blocks, push_as_store_blocks,
                                    rta_as_sec, rta_as_ptr_committed, rta_as_residue, rta_as_node_blocks, rta_as_store_blocks,
                                    dr_as_sec, dr_as_ptr_committed, dr_as_residue, dr_as_node_blocks, dr_as_store_blocks.
          repeat split; try reflexivity. exact RB'.
        - subst a'. rewrite push_as_nprim_ever, rta_as_nprim_ever, dr_as_nprim_ever. reflexivity.
        - subst a'. rewrite push_as_ndepot_ins, rta_as_ndepot_ins, dr_as_ndepot_ins. reflexivity. }
      pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
      pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
      pose proof CR0 as (_ & _ & _ & CRS & _). pose proof DR0 as (_ & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
      eapply KONT. unfold ldc_post. split; [exists 0%nat, [], [], []; exact RUN|].
      split; [exact REP1|]. split; [exact WF'|].
      split. { apply (AKern_ext2 E0 a a'); [intros c'; apply (proj1 (GMU c'))| intros c'; apply (proj2 (GMU c'))
               | subst a'; rewrite push_as_ptr_committed, rta_as_ptr_committed, dr_as_ptr_committed; reflexivity
               | subst a'; rewrite push_as_sec, rta_as_sec, dr_as_sec; reflexivity
               | subst a'; rewrite push_as_node_blocks, rta_as_node_blocks, dr_as_node_blocks; reflexivity
               | subst a'; rewrite push_as_store_blocks, rta_as_store_blocks, dr_as_store_blocks; reflexivity|].
               exact (AKern_frame _ _ _ _ Fvm1 Flz1 AK). }
      split; [exact TOK1'|]. split; [exact Ffs1|]. split; [exact Ffds1|]. split; [exact Ftid1|].
      split; [exact SK1|]. split; [exact MI1|].
      split. { apply (rt_misc5_agree E0 FSB0 PL0 m m1 RT). intros z Hz.
               destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
               - apply MU1. rewrite wa_unsigned by (clear -ZI; lia). unfold BF_free6.RIc, BF_free6.PCB, kThrCache. rewrite HRI, HFA'. cbn [outside]. unfold kSpaceSize.
                 clear -ZI LOC LO CR Timg Tlo HC30 HR HSB NF0. repeat split; try exact I; lia.
               - unfold rt_high2 in RH. apply MU1. rewrite wa_unsigned by (clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia).
                 unfold BF_free6.RIc, BF_free6.PCB, kThrCache. rewrite HRI, HFA'. cbn [outside]. unfold kSpaceSize.
                 subst nf mfa. clear -RH LOC LO CR Tlo Thi CT DT CQ2 CC1 CC2 DQ2 DD1 DD2 HC30 HR CRS DRS G1 G2 G3 A7 A8 NF0 HSB WE19. unfold kFreeArraySize in A7. unfold kSpaceSize in HSB. repeat split; try exact I; lia. }
      split; [exact WM1|].
      split. { eapply munch_cover; [exact MU1|]. unfold ldc_W, K_LDC, kThrCache, kPerClassSize, kThrCacheStats, kRegSize. cbv zeta. fold r FA nf h. unfold BF_free6.RIc, BF_free6.PCB, kThrCache.
               clear -LO HR HC30. solve_covers. }
      subst a'. unfold ldc_same.
      rewrite push_as_chunks, push_as_dead, push_as_tq, push_as_gq, push_as_sec, push_as_ptr_committed, push_as_sec_stats, push_as_sec_stale, push_as_glob_allocated, push_as_glob_mapped,
              push_as_nprim_ever, push_as_residue, push_as_everc, push_as_ndepot_ins, push_as_node_blocks, push_as_store_blocks, push_as_keys, push_as_frames, push_as_store_stored,
              push_as_cache_inited, push_as_cache_mapped, push_as_ia_inited, push_as_oom,
              rta_as_chunks, rta_as_dead, rta_as_tq, rta_as_gq, rta_as_sec, rta_as_ptr_committed, rta_as_sec_stats, rta_as_sec_stale, rta_as_glob_allocated, rta_as_glob_mapped,
              rta_as_nprim_ever, rta_as_residue, rta_as_everc, rta_as_ndepot_ins, rta_as_node_blocks, rta_as_store_blocks, rta_as_keys, rta_as_frames, rta_as_store_stored,
              rta_as_cache_inited, rta_as_cache_mapped, rta_as_ia_inited, rta_as_oom,
              dr_as_chunks, dr_as_dead, dr_as_tq, dr_as_gq, dr_as_sec, dr_as_ptr_committed, dr_as_sec_stats, dr_as_sec_stale, dr_as_glob_allocated, dr_as_glob_mapped,
              dr_as_nprim_ever, dr_as_residue, dr_as_everc, dr_as_ndepot_ins, dr_as_node_blocks, dr_as_store_blocks, dr_as_keys, dr_as_frames, dr_as_store_stored,
              dr_as_cache_inited, dr_as_cache_mapped, dr_as_ia_inited, dr_as_oom.
      rewrite RB', GR'. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa].
      repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact CI.
      * intros c' NE. split; [exact (GRo c' ltac:(clear -NE; lia))|]. rewrite push_get_cache_ne, rta_get_cache, dr_get_cache_ne by (clear -NE; lia). reflexivity.
      * subst mfa r. unfold kFreeArrayMapSize. clear; lia.
      * subst mfa r. clear; lia.
Qed.

End LdcT.
End RC__1.
(* [comment removed for export] *)
