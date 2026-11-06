(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanDepot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section INIT.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
Let IC := ae_ic E.
Let INST : Z := ae_instance E.
Let SB : Z := ae_space_beg E.
Let RI : Z := ae_region_info E.
Let T : Z := ae_thread E.

(* [comment removed for export] *)
Definition arep0_facts (m : mem) : Prop :=
  (* [comment removed for export] *)
     RW m (INST + kInsSpaceBeg) [C8 (zw SB); C4 (zw 0xffffffff); C4 (zw 0); C8 (zw RI); C1 (zb 0)]
  /\ RW m (INST + kInsSecondary) [C8 (zw kPageSize); C8 (zw (ae_ptr_array E)); C8 (zw (ae_ptr_array E)); C8 (zw (2^23))]
  /\ RW m (INST + kInsNReserved) [C8 (zw 0); C8 (zw 0); C1 (zb 0)]
  /\ RW m (INST + kInsSecStats) [C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0)]
  /\ u64arr segs m (INST + kInsSecStats + 32) (map zw (repeat 0 64))
  /\ RW m (INST + kInsSecMutex) [C4 (zw 0)]
  /\ RW m (INST + kInsGlobalStats + 16) [C8 (zw 0); C8 (zw 0)]
  /\ RW m (INST + kInsQuarantine + 64) [C8 (zw kQuarantineMax); C8 (zw kQuarantineMin); C8 (zw kThreadQuarantineMax)]
  /\ RW m (INST + kInsQMutex) [C4 (zw 0)]                      (* [comment removed for export] *)
  /\ RW m (INST + kInsQGlobal) [C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0)]
  /\ RW m (INST + kInsFallbackMutex) [C1 (zb 0)]
  /\ RW m (INST + kInsMaxUserDefined) [C8 (zw (2^40)); C2 (zw kMinRedzone); C2 (zw kMaxRedzone); C1 (zb 1)]
  (* [comment removed for export] *)
  /\ (forall c, 0 <= c < kNumClasses -> RW m (RI + kRegSize * c) (region_cells region0))
  (* [comment removed for export] *)
  /\ RW m (T + kThrStackTop) [C8 (zw (ae_stack_top E)); C8 (zw (ae_stack_bottom E))]
  /\ RW m (T + 40) [C1 (zb 0)]
  /\ RW m (T + kThrQCache) [C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0)]
  /\ (forall c, 0 <= c < kNumClasses ->
        RW m (T + kThrCache + kPerClassSize * c) [C4 (zw 0); C4 (zw 0); C8 (zw 0)]
        /\ exists junk, u32arr segs m (T + kThrCache + kPerClassSize * c + 16) junk /\ length junk = 16%nat)
  /\ RW m (T + kThrCacheStats + 16) [C8 (zw 0); C8 (zw 0)]
  /\ u64arr segs m (T + kThrStats) (map zw (repeat 0 14))
  /\ u64arr segs m (T + kThrStats + 112) (map zw (repeat 0 32))
  /\ RW m (T + kThrUnwinding) [C1 (zb 0)]
  (* [comment removed for export] *)
  /\ u8arr segs m (aic_asan_flags IC) (map zb (asan_flags_bytes IC))
  /\ RW m (aic_common_flags IC + 34) [C1 (zb 1)]
  /\ RW m (aic_common_flags IC + 120) [C8 (zw kClearShadowMmapThreshold)]
  /\ RW m (aic_common_flags IC + 219) [C1 (zb 1)]
  /\ RW m (aic_shadow_dyn_addr IC) [C8 (zw kShadowBase)]
  /\ RW m (aic_kHighMemEnd IC) [C8 (zw kHighMemEnd); C8 (zw 0); C8 (zw 0)]
  /\ RW m (aic_can_poison_memory IC) [C1 (zb 1)]
  /\ RW m (aic_asan_inited IC) [C1 (zb 1)]
  /\ RW m (aic_malloc_context_size IC) [C4 (zw kMallocContextSize)]
  /\ RW m (aic_page_size_cached IC) [C8 (zw kPageSize)]
  /\ RW m (aic_dying_flag IC) [C4 (zw 0)]
  /\ RW m (aic_stack_anchor IC) [C8 (zw (ae_sp0 E - kStackAnchorDelta))]
  /\ RW m (aic_REAL_memcpy_var IC) [C8 (zw (aic_musl_memcpy IC)); C8 (zw (aic_musl_memset IC))]
  /\ u64arr segs m (aic_malloc_hook_table IC) (map zw (repeat 0 10))
  /\ RW m (aic_internal_alloc_initialized IC) [C1 (zb 0); C1 (zb 0)]
  /\ u8arr segs m (aic_internal_allocator_instance IC + 8) (zeros (Z.to_nat 0x40000))
  /\ wr_at segs m (aic_internal_allocator_instance IC) 0x81030
  (* [comment removed for export] *)
  /\ (forall g, sh_default_dom E (8 * g) = true -> sh_excluded E (8 * g) = false -> RW m (kShadowBase + g) [C1 (zb 0)])
  (* [comment removed for export] *)
  /\ (forall c, 0 <= c < kNumClasses -> u32arr segs m (free_array SB c) [] /\ wr_at segs m (region_beg SB c) 0).

Lemma existsb_all_false : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
Proof. induction l; cbn; intros H; [reflexivity|]. rewrite (H a) by (left; reflexivity). cbn. apply IHl. intros; apply H; right; assumption. Qed.

Lemma Sh_init : forall a v, Sh E (astate0 E) a = Some v ->
  v = 0 /\ sh_default_dom E a = true /\ sh_excluded E a = false.
Proof.
  intros a v H. unfold Sh in H.
  assert (R : in_some_region_map E (astate0 E) a = false).
  { unfold in_some_region_map. rewrite !existsb_all_false; [reflexivity| |]; intros c _; unfold region_of, get_region; cbn -[Z.leb Z.ltb Z.add region_beg free_array];
      rewrite Z.add_0_r; apply andb_false_iff;
      [ destruct (Z.le_gt_cases (free_array (ae_space_beg E) c) a); [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia]
      | destruct (Z.le_gt_cases (region_beg (ae_space_beg E) c) a); [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia] ]. }
  assert (S : in_some_sec_map (astate0 E) a = false) by reflexivity.
  rewrite R, S in H. cbn [orb] in H.
  destruct (sh_default_dom E a && negb (sh_excluded E a)) eqn:C; [| discriminate].
  injection H as <-. apply andb_prop in C as [C1 C2]. apply negb_true_iff in C2. auto.
Qed.

Theorem ARep_init : forall (DepotR : astate -> mem -> Prop) m,
  arep0_facts m -> DepotR (astate0 E) m -> ARep segs E DepotR (astate0 E) m.
Proof.
  intros DepotR m F D.
  destruct F as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & B & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8
                 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & J & C).
  unfold ARep. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact D| split]]]]]]]].
  - (* [comment removed for export] *) unfold arep_instance. cbn [as_ptr_committed as_sec_stats as_glob_allocated as_glob_mapped as_gq astate0 secstats0 ss_n_allocs ss_n_frees ss_cur ss_max ss_by_size_log].
    Ltac ex H := first [exact H | unfold n_chunks, qcount, list_first, list_last, gq_bytes, qbytes; cbn -[rw_cells Z.add zw zb]; exact H].
    split; [ex A1|]. split; [ex A2|]. split; [ex A3|]. split; [ex A4|]. split.
    { exists (map zw (repeat 0 64)). split; [exact A5| rewrite length_map, repeat_length; reflexivity]. }
    split; [ex A6|]. split; [ex A7|]. split; [ex A8|]. split; [ex A9|]. split; [ex A10|]. split; [ex A11| ex A12].
  - (* [comment removed for export] *) intros c Hc. unfold region_of, get_region. cbn. exact (B c Hc).
  - (* [comment removed for export] *) intros c Hc. unfold region_of, get_region. cbn. destruct (C c Hc) as [U W]. split; [exact W|]. exists []. split; [rewrite app_nil_r; exact U| reflexivity].
  - (* [comment removed for export] *) unfold arep_thread. split; [exact D1|]. split; [exact D2|]. split.
    { unfold qcount, list_first, list_last, tq_bytes. cbn. exact D3. }
    split.
    { intros c Hc. destruct (D4 c Hc) as [R [junk [U L]]]. unfold percls_cells, get_cache. cbn. split; [exact R|]. exists junk. cbn. split; [exact U| exact L]. }
    split; [cbn; exact D5|]. split; [cbn; exact D6|]. split; [| exact D8].
    match goal with |- u64arr _ _ _ ?l => replace l with (map zw (repeat 0 32)); [exact D7| clear; vm_compute; reflexivity] end.
  - (* [comment removed for export] *) unfold arep_secondary. split; [left; split; reflexivity|]. intros i c H. destruct i; cbn in H; discriminate.
  - (* [comment removed for export] *) intros cb cm H. cbn in H. rewrite lookup_empty in H. discriminate.
  - (* [comment removed for export] *) unfold arep_batches. cbn. auto.
  - (* [comment removed for export] *) unfold arep_globals. cbn [as_ia_inited astate0 boolz].
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|]. split; [exact I6|]. split; [exact I7|].
    split; [exact I8|]. split; [exact I9|]. split; [exact I10|]. split; [exact I11|]. split; [exact I12|]. split; [exact I13|]. split; [exact I14|].
    split; [exact I15|]. split; [intros H; discriminate|]. split; [exact I16| exact I17].
  - (* [comment removed for export] *) intros g v H. destruct (Sh_init _ _ H) as (-> & R1 & EX). apply J; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot0_facts (m : mem) : Prop :=
  let HS := map depot_hash (ae_keys0 E) in
  let n0 := zlen (ae_keys0 E) in
     (forall b, 0 <= b < kTabSize -> RW m ((aic_theDepot IC) + 4 * b) [C4 (zw (bucket_head HS b))])
  /\ RW m ((aic_theDepot IC) + 0x400000) [C4 (zw n0)]
  /\ RW m ((aic_theDepot IC) + 0x400010) [C8 (zw (ae_depot_nodes E))]
  /\ (forall k, 1 <= k < kNodesMap1 -> RW m ((aic_theDepot IC) + 0x400010 + 8 * k) [C8 (zw 0)])
  /\ (forall i, 1 <= i <= n0 -> exists sid, RW m (ae_depot_nodes E + 16 * i) [C8 (zw (nth_hash HS i)); C4 (zw (node_link HS i)); C4 sid])
  /\ wr_at segs m (ae_depot_nodes E) kDepotNodeBlockBytes
  /\ RW m (aic_stackStore IC) [C8 (zw (ae_frames0 E))]
  /\ (exists al, RW m ((aic_stackStore IC) + 8) [C8 al])
  /\ RW m ((aic_stackStore IC) + 16) [C8 (zw (ae_store_blk E)); C4 (zw (ae_frames0 E))]
  /\ (exists mx, RW m ((aic_stackStore IC) + 28) [C4 mx])
  /\ (forall k, 1 <= k < kStoreBlockCount -> RW m ((aic_stackStore IC) + 16 + 16 * k) [C8 (zw 0); C4 (zw 0)] /\ exists mx, RW m ((aic_stackStore IC) + 28 + 16 * k) [C4 mx])
  /\ (exists bs, u8arr segs m (ae_store_blk E) bs /\ Z.of_nat (length bs) = kStoreBlockBytes)
  (* [comment removed for export] *)
  /\ RW m ((aic_theDepot IC) + 0x400008) [C4 (zw 0)]
  /\ (forall k, 0 <= k < kStoreBlockCount -> RW m ((aic_stackStore IC) + 28 + 16 * k) [C4 (zw 0)]).


Theorem DepotRep_init : forall m, zlen (ae_keys0 E) < kDepotNodesPerBlock -> 0 <= ae_frames0 E <= kStoreBlockFrames ->
  depot0_facts m -> DepotRep segs E (astate0 E) m.
Proof.
  intros m NK FR (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
  unfold DepotRep, depot_hashes, depot_keys, node_blocks, store_blocks, node_addr. cbn [as_keys as_node_blocks as_store_blocks as_frames astate0].
  rewrite app_nil_r.
  assert (NZ0 : forall l : list Z, nthz l 0 = List.hd 0 l) by (intros [|z l]; unfold nthz, zlen; cbn; reflexivity).
  assert (NZk : forall (z : Z) k, 1 <= k -> nthz [z] k = 0).
  { intros z k Hk. unfold nthz. replace (0 <=? k) with true by (symmetry; apply Z.leb_le; lia).
    replace (k <? zlen [z]) with false by (symmetry; apply Z.ltb_ge; unfold zlen; cbn; lia). reflexivity. }
  split; [exact F1|]. split; [exact F2|]. split.
  { intros k Hk. destruct (Z.eq_dec k 0) as [->|NE].
    - rewrite NZ0. cbn [hd]. rewrite Z.mul_0_r, Z.add_0_r. exact F3.
    - rewrite NZk by lia. apply F4. lia. }
  split.
  { intros i Hi. pose proof (Z.mod_pos_bound i kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)).
    rewrite Z.div_small by lia. rewrite NZ0. cbn [hd]. rewrite Z.mod_small by lia. apply F5. exact Hi. }
  split; [intros b [<-|[]]; exact F6|]. split; [exact F7|]. split; [exact F8|]. split.
  { intros k Hk. destruct (Z.eq_dec k 0) as [->|NE].
    - rewrite NZ0. cbn [hd]. unfold stored_of. rewrite Z.mul_0_l, Z.sub_0_r. rewrite (Z.max_r 0 (ae_frames0 E)) by lia. rewrite Z.min_r by lia.
      rewrite Z.mul_0_r, !Z.add_0_r. split; [exact F9| exact F10].
    - rewrite NZk by lia. unfold stored_of.
      replace (Z.min kStoreBlockFrames (Z.max 0 (ae_frames0 E - k * kStoreBlockFrames))) with 0 by (unfold kStoreBlockFrames in *; nia).
      apply F11. lia. }
  split; [intros b [<-|[]]; exact F12|]. split; [exact F13| exact F14].
Qed.

End INIT.
End RC__1.
