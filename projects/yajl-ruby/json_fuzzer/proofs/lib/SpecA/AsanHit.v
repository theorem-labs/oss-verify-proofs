(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanDepot AsanClient AsanWf1 AsanWf4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section HIT.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
Definition hc (n : Z) : Z := class_id (needed1 n).
Definition hx (n : Z) (a : astate) : Z := List.last (get_cache a (hc n)) 0.
Definition hab (n : Z) (a : astate) : Z := chunk_of_compact SB (hc n) (hx n a).
Definition hub (n : Z) (a : astate) : Z := hab n a + rz_size n.
Definition hcb (n : Z) (a : astate) : Z := hub n a - kChunkHeaderSize.
Definition hid (key : list Z) (a : astate) : Z :=
  match depot_lookup E a key with Some id => id | None => depot_n_ids E a + 1 end.
Definition hcm (key : list Z) (n : Z) (a : astate) : chunkmeta :=
  mkCM (hab n a) (rz_log n) (req n) (Some (hc n)) (CAllocated (hid key a)).

(* [comment removed for export] *)
Definition pop_st (n : Z) (a : astate) : astate :=
  let c := hc n in let l := get_cache a c in let x := List.last l 0 in let i := Z.of_nat (Nat.pred (length l)) in
  upd_cache_allocated (fun al => al + class_size c)
    (upd_cache_stale (fun st => <[c := <[i := x]> (match st !! c with Some m => m | None => ∅ end)]> st)
       (set_cache c (removelast l) (upd_nprimc true c a))).
Definition dput_st (key : list Z) (n : Z) (a : astate) : astate :=
  let a3 := upd_ndepot (fun k => k + 1) (pop_st n a) in
  match depot_lookup E a key with
  | Some _ => a3
  | None => upd_keys (fun ks => ks ++ [key]) (fun f => f) (upd_keys (fun ks => ks) (fun f => f + (zlen key + 1)) a3)
  end.
Definition amalloc_hit_st (key : list Z) (n : Z) (a : astate) : astate :=
  upd_ts (ts_on_malloc (req n) (needed n) (kMaxSize <? needed n) (class_id (needed n)))
    (upd_dead (delete (hcb n a)) (upd_chunks (fun cm => <[hcb n a := hcm key n a]> cm) (dput_st key n a))).

(* [comment removed for export] *)
Definition hit_ok (key : list Z) (n : Z) (a : astate) : Prop :=
     1 <= n <= 448
  /\ get_cache a (hc n) <> []
  /\ (depot_n_ids E a + 1) mod kDepotNodesPerBlock <> 0
  /\ as_frames a mod kStoreBlockFrames + (zlen key + 1) <= kStoreBlockFrames
  /\ 0 <= zlen key
  /\ as_frames a / kStoreBlockFrames < zlen (store_blocks E a)
  /\ 0 <= as_frames a
  /\ depot_n_ids E a + 2 < 2^31
  /\ as_chunks a !! (hcb n a) = None.

Lemma small_primary : forall n, 1 <= n <= 448 -> from_primary n = true /\ needed n = needed1 n /\ req n = n /\ needs_remap ((req n / 8) * 8) = false.
Proof.
  intros n Hn. unfold from_primary, needed, from_primary, req, needs_remap.
  assert (N1 : needed1 n <= kMaxSize).
  { unfold needed1, rounded, rz_size, rz_log, round_up, kChunkHeader2Size, kMaxSize.
    destruct (n <=? 64 - 16) eqn:C1; [apply Z.leb_le in C1| apply Z.leb_gt in C1];
    [| destruct (n <=? 128 - 32) eqn:C2; [apply Z.leb_le in C2| apply Z.leb_gt in C2];
       [| destruct (n <=? 512 - 64) eqn:C3; [apply Z.leb_le in C3| apply Z.leb_gt in C3]; [| lia]]];
    cbn [Z.pow Z.pow_pos Pos.iter Z.mul]; Z.div_mod_to_equations; lia. }
  replace (needed1 n <=? kMaxSize) with true by (symmetry; apply Z.leb_le; exact N1).
  repeat split; try reflexivity; [lia|]. apply Z.leb_gt. unfold kClearShadowMmapThreshold. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Theorem amalloc_hit_eval : forall key n a, hit_ok key n a ->
  amalloc E key n a = SRet (amalloc_hit_st key n a, ONorm (Some (hub n a))).
Proof.
  intros key n a (Hn & HC & HNB & HNS & HK & HSB & HF & HID & HFRESH).
  pose proof (small_primary n Hn) as (P1 & P2 & P3 & P4).
  { unfold amalloc, amalloc_core. unfold abind at 1. unfold acheck.
    replace (n <? 2^40) with true by (symmetry; apply Z.ltb_lt; lia). cbn [aret sbind snd fst].
    unfold abind at 1. cbn [aupd sbind snd fst]. rewrite P1.
    unfold abind at 1. unfold cache_pop. unfold abind at 1. cbn [aget sbind snd fst].
    fold (hc n).
    assert (GC : get_cache (upd_nprimc true (hc n) a) (hc n) = get_cache a (hc n)) by (destruct a; reflexivity). rewrite GC.
    destruct (get_cache a (hc n)) as [|y l0] eqn:EL; [congruence|].
    unfold abind at 1. cbn [aret sbind snd fst negb]. unfold abind at 1. cbn [aget sbind snd fst]. rewrite GC.
    unfold abind at 1. cbn [aupd sbind snd fst aret].
    (* [comment removed for export] *)
    unfold abind at 1. unfold depot_put. unfold abind at 1. cbn [aget sbind snd fst]. unfold abind at 1. cbn [aupd sbind snd fst].
    set (a2 := upd_cache_allocated _ _).
    assert (DL : depot_lookup E a2 key = depot_lookup E a key) by (subst a2; destruct a; reflexivity).
    assert (DN : depot_n_ids E a2 = depot_n_ids E a) by (subst a2; destruct a; reflexivity).
    rewrite DL, DN.
    (* [comment removed for export] *)
    Ltac tail0 a HFRESH EL P4 :=
      cbn [AsanOps.aget sbind snd fst];
      match goal with |- context [as_chunks ?st !! ?k] => let X := fresh in assert (X : as_chunks st !! k = None) by (rewrite <- HFRESH; unfold hcb, hub, hab, hx; rewrite EL; destruct a; reflexivity); rewrite X; clear X end;
      unfold abind at 1; cbn [aret sbind snd fst];
      unfold abind at 1; cbn [aupd sbind snd fst]; unfold abind at 1; unfold poison_zero; try rewrite P4; cbn [aret sbind snd fst];
      unfold abind at 1; cbn [aupd sbind snd fst aret]; unfold AsanOps.aret.
    Ltac tail a HFRESH EL P4 := unfold abind at 1; tail0 a HFRESH EL P4.
    unfold amalloc_hit_st, dput_st. unfold pop_st. rewrite EL. fold a2.
    destruct (depot_lookup E a key) as [id|] eqn:DLK.
    - cbn [aret sbind snd fst]. tail a HFRESH EL P4.
      unfold hid, hcm, hid. rewrite DLK. unfold hcb, hub, hab, hx. rewrite EL. subst a2. destruct a; reflexivity.
    - unfold acheck. replace (depot_n_ids E a + 1 <? 2^31) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold abind at 1. unfold abind at 1. cbn [aret sbind snd fst].
      replace ((depot_n_ids E a + 1) mod kDepotNodesPerBlock =? 0) with false by (symmetry; apply Z.eqb_neq; exact HNB).
      unfold abind at 1. cbn [aret sbind snd fst].
      unfold abind at 1. unfold store_alloc. unfold abind at 1. unfold store_alloc_once. unfold abind at 1. cbn [aget sbind snd fst].
      unfold abind at 1. cbn [aupd sbind snd fst].
      assert (FR2 : as_frames (upd_ndepot (fun k => k + 1) a2) = as_frames a) by (subst a2; destruct a; reflexivity). rewrite FR2.
      replace (as_frames a / kStoreBlockFrames =? (as_frames a + (zlen key + 1) - 1) / kStoreBlockFrames) with true.
      2: { symmetry. apply Z.eqb_eq. unfold kStoreBlockFrames in *.
           pose proof (Z.div_mod (as_frames a) (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound (as_frames a) (2^20) ltac:(lia)).
           apply Z.div_unique with (r := as_frames a mod 2^20 + zlen key); lia. }
      unfold abind at 1. cbn [aget sbind snd fst].
      assert (SBK : as_store_blocks (upd_keys (fun ks => ks) (fun f => f + (zlen key + 1)) (upd_ndepot (fun k => k + 1) a2)) = as_store_blocks a)
        by (subst a2; destruct a; reflexivity). rewrite SBK.
      replace ((0 <? as_frames a / kStoreBlockFrames) && (zlen (as_store_blocks a) <? as_frames a / kStoreBlockFrames)) with false.
      2: { symmetry. unfold store_blocks, zlen in HSB. cbn [length] in HSB. destruct (0 <? as_frames a / kStoreBlockFrames); [| reflexivity]. cbn. apply Z.ltb_ge. unfold zlen. lia. }
      unfold abind at 1. cbn [aret sbind snd fst]. unfold abind at 1. cbn [aupd sbind snd fst].
      tail0 a HFRESH EL P4.
      unfold hid, hcm, hid. rewrite DLK. unfold hcb, hub, hab, hx. rewrite EL. subst a2. destruct a; reflexivity. }
Qed.

Corollary arun_amalloc_hit : forall key n a fuel orc, hit_ok key n a ->
  arun fuel (amalloc E key n a) orc = Some (amalloc_hit_st key n a, ONorm (Some (hub n a)), [], orc).
Proof. intros key n a fuel orc H. rewrite (amalloc_hit_eval key n a H). destruct fuel; reflexivity. Qed.

(* [comment removed for export] *)
Lemma hoare_hit : forall key n a (P : astate -> Prop) (Q : astate -> option Z -> Prop),
  hit_ok key n a -> hoare P (amalloc E key n) Q -> P a -> Q (amalloc_hit_st key n a) (Some (hub n a)).
Proof. intros key n a P Q H T HP. pose proof (T a HP) as X. rewrite (amalloc_hit_eval key n a H) in X. exact X. Qed.
Lemma hoareW_hit : forall key n a (P : astate -> Prop) (Q : astate -> option Z -> Prop),
  hit_ok key n a -> hoareW P (amalloc E key n) Q -> P a -> Q (amalloc_hit_st key n a) (Some (hub n a)).
Proof. intros key n a P Q H T HP. pose proof (T a HP) as X. rewrite (amalloc_hit_eval key n a H) in X. exact X. Qed.

(* [comment removed for export] *)
Section Proj.
Variables (key : list Z) (n : Z) (a : astate).
#[warnings="-notation-for-abbreviation"] Notation a' := (amalloc_hit_st key n a).
Lemma hit_regions : as_regions a' = as_regions a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_cache_inited : as_cache_inited a' = as_cache_inited a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_cache : as_cache a' = <[hc n := removelast (get_cache a (hc n))]> (as_cache a). Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_get_cache : forall c, get_cache a' c = if decide (c = hc n) then removelast (get_cache a (hc n)) else get_cache a c.
Proof. intros c. unfold get_cache at 1. rewrite hit_cache. destruct (decide (c = hc n)) as [->|NE]; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. Qed.
Lemma hit_cache_allocated : as_cache_allocated a' = as_cache_allocated a + class_size (hc n). Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_cache_mapped : as_cache_mapped a' = as_cache_mapped a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_ptr : as_ptr_committed a' = as_ptr_committed a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_sec : as_sec a' = as_sec a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_sec_stale : as_sec_stale a' = as_sec_stale a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_sec_stats : as_sec_stats a' = as_sec_stats a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_glob : as_glob_allocated a' = as_glob_allocated a /\ as_glob_mapped a' = as_glob_mapped a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; split; reflexivity. Qed.
Lemma hit_chunks : as_chunks a' = <[hcb n a := hcm key n a]> (as_chunks a). Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_tq : as_tq a' = as_tq a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_gq : as_gq a' = as_gq a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_keys : as_keys a' = match depot_lookup E a key with Some _ => as_keys a | None => as_keys a ++ [key] end.
Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_frames : as_frames a' = match depot_lookup E a key with Some _ => as_frames a | None => as_frames a + (zlen key + 1) end.
Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_ia : as_ia_inited a' = as_ia_inited a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_ts : as_ts a' = ts_on_malloc (req n) (needed n) (kMaxSize <? needed n) (class_id (needed n)) (as_ts a).
Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_residue : as_residue a' = as_residue a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_nprim : as_nprim_ever a' = as_nprim_ever a + 1. Proof. unfold amalloc_hit_st, dput_st, pop_st, upd_nprimc; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_node_blocks : as_node_blocks a' = as_node_blocks a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_store_blocks : as_store_blocks a' = as_store_blocks a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_store_stored : as_store_stored a' = as_store_stored a. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_ndepot : as_ndepot_ins a' = as_ndepot_ins a + 1. Proof. unfold amalloc_hit_st, dput_st; destruct (depot_lookup E a key); destruct a; reflexivity. Qed.
Lemma hit_tstats : forall (Hn : 1 <= n <= 448), let t := as_ts a in
  as_ts a' = mkTS (ts_mallocs t + 1) (ts_malloced t + n) (ts_malloced_redzones t + (needed1 n - n)) (ts_frees t) (ts_freed t)
                  (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t)
                  (ts_malloc_large t) (<[hc n := match ts_by_size t !! hc n with Some k => k + 1 | None => 1 end]> (ts_by_size t)).
Proof.
  intros Hn. cbv zeta. rewrite hit_ts. pose proof (small_primary n Hn) as (P1 & P2 & P3 & _). rewrite P2, P3. unfold ts_on_malloc.
  replace (kMaxSize <? needed1 n) with false; [reflexivity|]. symmetry. apply Z.ltb_ge. unfold from_primary in P1. apply Z.leb_le in P1. lia.
Qed.
End Proj.

(* [comment removed for export] *)
Lemma hit_depot_keys : forall key n a, depot_keys E (amalloc_hit_st key n a) = match depot_lookup E a key with Some _ => depot_keys E a | None => depot_keys E a ++ [key] end.
Proof. intros. unfold depot_keys. rewrite hit_keys. destruct (depot_lookup E a key); [reflexivity| rewrite app_assoc; reflexivity]. Qed.
Lemma hit_node_blocks' : forall key n a, node_blocks E (amalloc_hit_st key n a) = node_blocks E a.
Proof. intros. unfold node_blocks. rewrite hit_node_blocks. reflexivity. Qed.
Lemma hit_store_blocks' : forall key n a, store_blocks E (amalloc_hit_st key n a) = store_blocks E a.
Proof. intros. unfold store_blocks. rewrite hit_store_blocks. reflexivity. Qed.
Lemma hit_depot_n_ids : forall key n a, depot_n_ids E (amalloc_hit_st key n a) = match depot_lookup E a key with Some _ => depot_n_ids E a | None => depot_n_ids E a + 1 end.
Proof. intros. unfold depot_n_ids. rewrite hit_keys. destruct (depot_lookup E a key); [reflexivity| rewrite length_app; cbn [length]; lia]. Qed.

(* [comment removed for export] *)
Lemma head_aux_app : forall hs1 hs2 i b acc, head_aux (hs1 ++ hs2) i b acc = head_aux hs2 (i + zlen hs1) b (head_aux hs1 i b acc).
Proof.
  induction hs1 as [|h t IH]; intros hs2 i b acc; cbn [app head_aux].
  - unfold zlen. cbn. rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. unfold zlen. cbn [length]. lia.
Qed.
Lemma bucket_head_app1 : forall hs h b,
  bucket_head (hs ++ [h]) b = if bucket_of h =? b then zlen hs + 1 else bucket_head hs b.
Proof. intros hs h b. unfold bucket_head. rewrite head_aux_app. cbn. destruct (bucket_of h =? b); [lia| reflexivity]. Qed.
Lemma nth_hash_app_old : forall hs h i, 1 <= i <= zlen hs -> nth_hash (hs ++ [h]) i = nth_hash hs i.
Proof. intros hs h i Hi. unfold nth_hash. apply app_nth1. unfold zlen in Hi. lia. Qed.
Lemma nth_hash_app_new : forall hs h, nth_hash (hs ++ [h]) (zlen hs + 1) = h.
Proof. intros hs h. unfold nth_hash, zlen. replace (Z.to_nat (Z.of_nat (length hs) + 1 - 1)) with (length hs) by lia. apply (nth_middle hs [] h 0). Qed.
Lemma node_link_app_old : forall hs h i, 1 <= i <= zlen hs -> node_link (hs ++ [h]) i = node_link hs i.
Proof.
  intros hs h i Hi. unfold node_link. rewrite nth_hash_app_old by exact Hi. rewrite firstn_app. unfold zlen in Hi.
  replace (Z.to_nat (i - 1) - length hs)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma node_link_app_new : forall hs h, node_link (hs ++ [h]) (zlen hs + 1) = bucket_head hs (bucket_of h).
Proof.
  intros hs h. unfold node_link. rewrite nth_hash_app_new. rewrite firstn_app. unfold zlen.
  replace (Z.to_nat (Z.of_nat (length hs) + 1 - 1) - length hs)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_all2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma depot_lookup_hashes : forall a key,
  match depot_lookup E a key with
  | Some id => 1 <= id <= zlen (depot_hashes E a) /\ nth_hash (depot_hashes E a) id = depot_hash key
  | None => forall j, 1 <= j <= zlen (depot_hashes E a) -> nth_hash (depot_hashes E a) j <> depot_hash key
  end.
Proof.
  intros a key. unfold depot_lookup. pose proof (index_of_spec (depot_hash key) (ae_keys0 E ++ as_keys a) 1) as SP.
  unfold depot_hashes, depot_keys. destruct (index_of _ _ 1) as [j|].
  - destruct SP as [A B]. unfold zlen in *. rewrite length_map. split; [lia|]. rewrite nth_hash_map by (unfold zlen; lia). exact B.
  - intros j Hj. unfold zlen in Hj. rewrite length_map in Hj. rewrite nth_hash_map by (unfold zlen; lia). apply SP. lia.
Qed.
Lemma depot_lookup_unique : forall a key id j, List.NoDup (depot_hashes E a) ->
  depot_lookup E a key = Some id -> 1 <= j <= zlen (depot_hashes E a) -> nth_hash (depot_hashes E a) j = depot_hash key -> j = id.
Proof.
  intros a key id j ND HL Hj Hh. pose proof (depot_lookup_hashes a key) as SP. rewrite HL in SP. destruct SP as [A B].
  unfold nth_hash in Hh, B. unfold zlen in *.
  pose proof (proj1 (List.NoDup_nth (depot_hashes E a) 0) ND (Z.to_nat (j - 1)) (Z.to_nat (id - 1)) ltac:(lia) ltac:(lia) ltac:(rewrite Hh, B; reflexivity)). lia.
Qed.

(* [comment removed for export] *)
Lemma find_chunk_some : forall s x cm, find_chunk s x = Some cm ->
  exists cb, as_chunks s !! cb = Some cm /\ cm_alloc_beg cm <= x < cm_alloc_beg cm + block_span cm.
Proof.
  intros s x cm. unfold find_chunk.
  set (f := fun (_ : Z) (cm0 : chunkmeta) (acc : option chunkmeta) => match acc with Some _ => acc | None =>
             if (cm_alloc_beg cm0 <=? x) && (x <? cm_alloc_beg cm0 + block_span cm0) then Some cm0 else None end).
  assert (IND : forall mm, (forall k v, mm !! k = Some v -> as_chunks s !! k = Some v) -> map_fold f None mm = Some cm ->
            exists cb, as_chunks s !! cb = Some cm /\ cm_alloc_beg cm <= x < cm_alloc_beg cm + block_span cm).
  { intros mm. induction mm as [|k v mm NONE FIRST IH] using map_first_key_ind; intros SUB H.
    - rewrite map_fold_empty in H. discriminate.
    - rewrite map_fold_insert_first_key in H by assumption.
      assert (SUB' : forall k0 v0, mm !! k0 = Some v0 -> as_chunks s !! k0 = Some v0).
      { intros k0 v0 H0. apply SUB. rewrite lookup_insert_ne; [exact H0|]. intros ->. rewrite NONE in H0. discriminate. }
      cbn in H. destruct (map_fold f None mm) as [cm1|] eqn:R.
      + exact (IH SUB' H).
      + subst f. cbn beta in H. destruct ((cm_alloc_beg v <=? x) && (x <? cm_alloc_beg v + block_span v)) eqn:C; [| discriminate].
        injection H as ->. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        exists k. split; [apply SUB; apply lookup_insert_eq| lia]. }
  apply IND. auto.
Qed.

Lemma blk_hi_span : forall s cm, blk_hi s cm = cm_alloc_beg cm + block_span cm.
Proof. intros s cm. unfold blk_hi, block_span. destruct (cm_prim cm); lia. Qed.

Theorem Sh_hit : forall (P : list Z) (D : list batch) key n a x, AWf E P D a -> AWf E [] [] (amalloc_hit_st key n a) -> 1 <= n <= 448 ->
  as_chunks a !! hcb n a = None ->
  Sh E (amalloc_hit_st key n a) x =
    if (hab n a <=? x) && (x <? hab n a + class_size (hc n)) then Some (chunk_shadow (hcm key n a) x) else Sh E a x.
Proof.
  intros P D key n a x WF WF' Hn FRESH. set (a' := amalloc_hit_st key n a) in *.
  assert (NEW : as_chunks a' !! hcb n a = Some (hcm key n a)) by (subst a'; rewrite hit_chunks; apply lookup_insert_eq).
  destruct ((hab n a <=? x) && (x <? hab n a + class_size (hc n))) eqn:IN.
  - apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    apply (block_Sh E [] [] a' (hcb n a) (hcm key n a) x WF' NEW). unfold blk_lo, blk_hi. cbn. lia.
  - assert (OUT : ~ (hab n a <= x < hab n a + class_size (hc n))).
    { intros [H1 H2]. assert (C : (hab n a <=? x) && (x <? hab n a + class_size (hc n)) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). rewrite C in IN. discriminate. }
    unfold Sh. subst a'.
    assert (RM : in_some_region_map E (amalloc_hit_st key n a) x = in_some_region_map E a x) by (unfold in_some_region_map, region_of, get_region; rewrite hit_regions; reflexivity).
    assert (SM : in_some_sec_map (amalloc_hit_st key n a) x = in_some_sec_map a x) by (unfold in_some_sec_map; rewrite hit_sec; reflexivity).
    rewrite RM, SM.
    assert (FC : find_chunk (amalloc_hit_st key n a) x = find_chunk a x).
    { destruct (find_chunk (amalloc_hit_st key n a) x) as [cm'|] eqn:F1.
      - destruct (find_chunk_some _ _ _ F1) as (cb & Hcb & Hx). rewrite hit_chunks in Hcb.
        destruct (decide (cb = hcb n a)) as [->|NE].
        + rewrite lookup_insert_eq in Hcb. injection Hcb as <-. exfalso. apply OUT. cbn in Hx. exact Hx.
        + rewrite lookup_insert_ne in Hcb by congruence. symmetry. apply (find_chunk_block E P D a cb cm' x WF Hcb). rewrite blk_hi_span. unfold blk_lo. exact Hx.
      - destruct (find_chunk a x) as [cm0|] eqn:F0; [| reflexivity].
        destruct (find_chunk_some _ _ _ F0) as (cb & Hcb & Hx).
        assert (Hcb' : as_chunks (amalloc_hit_st key n a) !! cb = Some cm0).
        { rewrite hit_chunks. rewrite lookup_insert_ne; [exact Hcb|]. intros E1. rewrite E1 in FRESH. rewrite FRESH in Hcb. discriminate. }
        rewrite (find_chunk_block E [] [] (amalloc_hit_st key n a) cb cm0 x WF' Hcb') in F1; [discriminate|]. rewrite blk_hi_span. unfold blk_lo. exact Hx. }
    rewrite FC. reflexivity.
Qed.

End HIT.
End RC__1.
