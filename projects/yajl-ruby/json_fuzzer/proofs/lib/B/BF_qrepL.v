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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf3 AsanBudget AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepEnqB AsanRepPushB AsanRepRefillB AsanRepRefill2B AsanRepRelB AsanRepLdlB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_pop0 BF_popT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section QRepL.
Variable E0 : aenv.
#[local] Notation T := (ae_thread E0).
#[local] Notation SB := (ae_space_beg E0).

(* [comment removed for export] *)
Definition FPW5b (lo c : Z) (z : Z) : Prop :=
     lo <= z
  \/ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + kPerClassSize)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24).

(* [comment removed for export] *)
Theorem R5b_holds :
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
Proof.
  intros a m m' lo c p D junk l HC CI _ _ REP WF RENV WM AG LOC NCr NCa NCl NCc.
  apply (ARep_after_push bsegs E0 [] D a m m' lo c p junk HC CI REP WF RENV WM); [| exact LOC| exact NCr| exact NCa| exact NCl| exact NCc].
  intros z Hz NF. apply AG; [exact Hz|]. intros X. apply NF. unfold FPWpu. unfold FPW5b in X. clear -X. lia.
Qed.

(* [comment removed for export] *)
Definition dr_keep (a : astate) (c : Z) : nat := (length (get_cache a c) - Z.to_nat (hint c))%nat.
Definition dr_st (c : Z) (a : astate) : astate := set_cache c (firstn (dr_keep a c) (get_cache a c)) a.
Definition dr_chunks (c : Z) (a : astate) : list Z := skipn (dr_keep a c) (get_cache a c).
Definition rta_st (c : Z) (chunks : list Z) (a : astate) : astate :=
  let r := get_region a c in
  set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ chunks) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r + zlen chunks)) a.
Definition FPW6 (a : astate) (lo c : Z) (g : bool) (z : Z) : Prop :=
  let r := get_region a c in let FA := free_array SB c in
     lo <= z
  \/ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + kPerClassSize)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24)
  \/ (ae_region_info E0 + kRegSize * c <= z < ae_region_info E0 + kRegSize * c + kRegSize)
  \/ (FA + 4 * rg_num_freed r <= z < FA + 4 * (rg_num_freed r + hint c))
  \/ (g = true /\ (   (T + kThrStats + 72 <= z < T + kThrStats + 88)
                   \/ (FA + rg_mapped_fa r <= z < FA + rg_mapped_fa r + kFreeArrayMapSize)
                   \/ (kShadowBase + (FA + rg_mapped_fa r) / 8 <= z < kShadowBase + (FA + rg_mapped_fa r) / 8 + kFreeArrayMapSize / 8))).

(* [comment removed for export] *)
Theorem R6_holds :
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
  rw_cells bsegs m' (ae_region_info E0 + kRegSize * c) (region_cells (get_region a' c)) ->
  u32arr bsegs m' FA (map wz (rg_free r ++ ch) ++ fjunk) -> 4 * (Z.of_nat (length (rg_free r ++ ch)) + Z.of_nat (length fjunk)) = mfa' ->
  (g = true -> rw_cells bsegs m' (T + kThrStats + 72) [C8 (wz (ts_mmaps (as_ts a) + 1)); C8 (wz (ts_mmaped (as_ts a) + kFreeArrayMapSize))]
              /\ rw_cells bsegs m' (kShadowBase + (FA + rg_mapped_fa r) / 8)
                   [CB (Z.to_nat (kFreeArrayMapSize / 8)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (kFreeArrayMapSize / 8)))]) ->
  (g = true -> rg_mapped_fa r + kFreeArrayMapSize <= kFreeArraySize) ->
  ARep bsegs E0 (DepotR bsegs E0) a' m'.
Proof.
  intros a m m' lo c p D junk fjunk g l h r FA ch a1 a2 a' mfa' HC CI ZL AV REP WF RENV WM AG LOC NCrow NCarr NClen NCcst NCri NCfa NCfl NCg ROOMg.
  pose proof alloc_ceiling_range as CR. pose proof (hint_range c ltac:(unfold kLargestClassID in HC; clear -HC; lia)) as HR.
  (* [comment removed for export] *)
  assert (Hkeep : dr_keep a c = Z.to_nat h).
  { unfold dr_keep. fold l. unfold zlen, max_count in ZL. fold h in ZL. clear -ZL HR. lia. }
  assert (Er' : get_region a' c = mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r ++ ch) mfa' (rg_n_allocated r) (rg_n_freed r + zlen ch)).
  { subst a' a2 a1 mfa' r. unfold push_st, rta_st, st_fa, dr_st. destruct g; destruct a; unfold get_region, get_cache; cbn -[Z.add zlen skipn firstn app];
    rewrite ?lookup_insert_eq; try reflexivity.
    all: unfold get_region; cbn; rewrite ?lookup_insert_eq; cbn; rewrite ?Z.add_0_r; reflexivity. }
  (* [comment removed for export] *)
  pose proof RENV as (BS & Tpl & IMG_IN & IMG_LO & IMG_LOW & _ & AK & TDN & _).
  pose proof WF as (WE & WR & WC & _). destruct (proj2 WR c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). cbv zeta in A1, A2, A3, A4, A5, A6, A7, A8.
  unfold region_of in A1, A2, A3, A4, A5, A6, A7, A8. fold r in A1, A2, A3, A4, A5, A6, A7, A8.
  pose proof REP as (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ). pose proof RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & _).
  assert (LL : length l = (2 * Z.to_nat h)%nat) by (unfold zlen, max_count in ZL; fold h in ZL; clear -ZL HR; lia).
  assert (LCH : length ch = Z.to_nat h) by (subst ch; unfold dr_chunks; rewrite length_skipn, Hkeep; fold l; clear -LL HR; lia).
  assert (LK : length (firstn (Z.to_nat h) l) = Z.to_nat h) by (rewrite length_firstn; clear -LL; lia).
  assert (NF : rg_num_freed r = Z.of_nat (length (rg_free r))) by reflexivity.
  assert (MFA' : 4 * (Z.of_nat (length (rg_free r)) + h) <= mfa' /\ rg_mapped_fa r <= mfa' /\ mfa' <= kFreeArraySize /\ mfa' mod kFreeArrayMapSize = 0 /\ 0 <= mfa').
  { rewrite length_app, Nat2Z.inj_add, LCH, Z2Nat.id in NCfl by (clear -HR; lia). subst mfa'. unfold kFreeArrayMapSize, kFreeArraySize in *.
    destruct g; [specialize (ROOMg eq_refl)|]; clear -NCfl A5 A6 A7 ROOMg; repeat split; try (Z.div_mod_to_equations; lia). }
  destruct MFA' as (M1 & M2 & M3 & M4 & M5).
  assert (GSZ : g = true -> mfa' = rg_mapped_fa r + kFreeArrayMapSize) by (intros G; subst mfa'; rewrite G; reflexivity).
  assert (GSZ0 : g = false -> mfa' = rg_mapped_fa r) by (intros G; subst mfa'; rewrite G; cbn; clear; lia).
  (* [comment removed for export] *)
  pose proof Tpl as [[T1 T2] T3].
  assert (Ecache' : forall c', c' <> c -> get_cache a' c' = get_cache a c').
  { intros c' NE. subst a' a2 a1. unfold push_st, rta_st, st_fa, dr_st. destruct g; destruct a; unfold get_cache; cbn; rewrite !lookup_insert_ne by congruence; reflexivity. }
  assert (Ecache_c : get_cache a' c = firstn (Z.to_nat h) l ++ [compact_of_chunk SB c p]).
  { subst a' a2 a1. rewrite <- Hkeep. unfold push_st, rta_st, st_fa, dr_st. destruct g; destruct a; unfold get_cache, dr_keep; cbn; rewrite !lookup_insert_eq; cbn; rewrite ?lookup_insert_eq; reflexivity. }
  assert (Ereg' : forall c', c' <> c -> region_of a' c' = region_of a c').
  { intros c' NE. subst a' a2 a1. unfold push_st, rta_st, st_fa, dr_st, region_of, get_region. destruct g; destruct a; cbn; rewrite !lookup_insert_ne by congruence; reflexivity. }
  assert (ECI : as_cache_inited a' = true) by (subst a' a2 a1; unfold push_st, rta_st, st_fa, dr_st; destruct g; destruct a; cbn; exact CI).
  assert (ECAL : as_cache_allocated a' = as_cache_allocated a - class_size c) by (subst a' a2 a1; unfold push_st, rta_st, st_fa, dr_st; destruct g; destruct a; reflexivity).
  assert (ECM : as_cache_mapped a' = as_cache_mapped a) by (subst a' a2 a1; unfold push_st, rta_st, st_fa, dr_st; destruct g; destruct a; reflexivity).
  assert (ETS : as_ts a' = if g then ts_on_mmap kFreeArrayMapSize (as_ts a) else as_ts a) by (subst a' a2 a1; unfold push_st, rta_st, st_fa, dr_st; destruct g; destruct a; reflexivity).
  assert (Er'' : region_of a' c = get_region a' c) by reflexivity.
  (* [comment removed for export] *)
  assert (AGR : forall z, 0 <= z < 2^64 -> ~ AsanRepRefill2B.FPWref E0 a a' lo c (length (rg_free r)) z -> m' (wa z) = m (wa z)).
  { intros z Hz NFz. apply AG; [exact Hz|]. intros X. apply NFz. unfold AsanRepRefill2B.FPWref. unfold FPW6 in X. cbv zeta in X. fold r in X.
    rewrite Er'', Er'. cbn [rg_mapped_user rg_mapped_fa]. unfold region_of. fold r. rewrite NF in X. rewrite NF in A8.
    destruct X as [X|[X|[X|[X|[X|[G [X|[X|X]]]]]]]].
    - left; exact X.
    - do 3 right; left; exact X.
    - do 4 right; left. clear -X; lia.
    - right; left; exact X.
    - do 7 right; left. clear -X M1. lia.
    - do 5 right; left. exact X.
    - do 7 right; left. rewrite (GSZ G). clear -X A8. lia.
    - do 9 right. rewrite (GSZ G). unfold kFreeArrayMapSize in *. clear -X A6. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (NCrow' : rw_cells bsegs m' (T + kThrCache + kPerClassSize * c) (percls_cells a' c)
                   /\ exists junk', u32arr bsegs m' (T + kThrCache + kPerClassSize * c + 16) (map wz (get_cache a' c) ++ junk') /\ (length (get_cache a' c) + length junk' = 16)%nat).
  { unfold percls_cells. rewrite Ecache_c, ECI, (row_max_count_reg E0 c HC), (row_class_size_reg E0 c HC).
    replace (zlen (firstn (Z.to_nat h) l ++ [compact_of_chunk SB c p])) with (h + 1) by (unfold zlen; rewrite length_app, LK; cbn [length]; clear -HR; lia).
    split; [exact NCrow|]. exists junk. split; [exact NCarr|]. rewrite length_app, LK. cbn [length]. clear -NClen. lia. }
  assert (AGT : forall z, T <= z < T + 4096 -> ~ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + kPerClassSize) ->
                ~ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24) -> ~ (g = true /\ T + kThrStats + 72 <= z < T + kThrStats + 88) -> m' (wa z) = m (wa z)).
  { intros z Hz N1 N2 N3. apply AG; [clear -Hz T1 T3 CR; lia|]. unfold FPW6. cbv zeta. fold r. rewrite NF.
    assert (FAhi : SB + kRegionSize <= free_array SB c /\ free_array SB c + kFreeArraySize <= SB + kSpaceSize).
    { unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize, kLargestClassID in *. clear -HC. lia. }
    intros [X|[X|[X|[X|[X|[G [X|[X|X]]]]]]]].
    - clear -X Hz T3 LOC. lia.
    - exact (N1 X).
    - exact (N2 X).
    - unfold ae_region_info, kRegSize, kSpaceSize, kLargestClassID in *. clear -X Hz E19 E3 E4 HC. lia.
    - unfold kSpaceSize, kFreeArraySize, kRegionSize in *. clear -X Hz FAhi E19 E3 E4 M1 M3 HR. subst h. lia.
    - exact (N3 (conj G X)).
    - rewrite (GSZ G) in M3. unfold kSpaceSize, kFreeArraySize, kFreeArrayMapSize, kRegionSize in *. clear -X Hz FAhi E19 E3 E4 A5 M3. lia.
    - rewrite (GSZ G) in M3. unfold app_mem in E14. rewrite kHighMemBeg_val, kLowAppEnd_val in E14. unfold kShadowBase, kSpaceSize, kFreeArraySize, kFreeArrayMapSize, kRegionSize in *.
      rewrite kHighMemBeg_val in E2. clear -X Hz FAhi E14 E2 E3 E4 E5 A5 M3 CR. Z.div_mod_to_equations. lia. }
  assert (NCrows : forall i, 0 <= i < kNumClasses -> i <> c -> rw_cells bsegs m' (T + kThrCache + kPerClassSize * i) (percls_cells a' i)).
  { intros i Hi NE. destruct (D4 i Hi) as [X _]. unfold percls_cells in X |- *. rewrite (Ecache' i NE), ECI. rewrite CI in X.
    eapply rw_cells_agree'; [| exact X]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros z Hz.
    unfold kNumClasses, kThrCache, kPerClassSize, kThrCacheStats, kThrStats, kLargestClassID in *. apply AGT; clear -Hz Hi NE HC; first [lia | intros [? Y]; lia]. }
  assert (NCcst' : rw_cells bsegs m' (T + kThrCacheStats + 16) [C8 (wz (as_cache_allocated a')); C8 (wz (as_cache_mapped a'))]).
  { rewrite ECAL, ECM. apply AsanRepHitB.rh_split with (cs1 := [C8 (AsanRep.zw (as_cache_allocated a))]) in D5. destruct D5 as [_ D5].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in D5.
    apply (AsanRepHitB.rh_join_at bsegs m' _ (T + kThrCacheStats + 16 + 8) [C8 (wz (as_cache_allocated a - class_size c))]); [exact NCcst| | cbn; lia].
    eapply rw_cells_agree'; [| exact D5]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros z Hz.
    unfold kThrCache, kPerClassSize, kThrCacheStats, kThrStats, kLargestClassID in *. apply AGT; clear -Hz HC; first [lia | intros [? Y]; lia]. }
  assert (NCthr : rw_cells bsegs m' (T + kThrStats + 72) [C8 (wz (ts_mmaps (as_ts a'))); C8 (wz (ts_mmaped (as_ts a')))]).
  { rewrite ETS. destruct g.
    - cbn [ts_mmaps ts_mmaped ts_on_mmap]. exact (proj1 (NCg eq_refl)).
    - pose proof (AsanRepHitB.u64arr_cell bsegs m _ _ 9 _ D6 eq_refl) as X9. pose proof (AsanRepHitB.u64arr_cell bsegs m _ _ 10 _ D6 eq_refl) as X10.
      apply (AsanRepHitB.rh_join_at bsegs m' _ (T + kThrStats + 80) [C8 (wz (ts_mmaps (as_ts a)))]); [| | cbn; lia].
      + eapply rw_cells_agree'; [| exact X9]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros z Hz.
        unfold kThrCache, kPerClassSize, kThrCacheStats, kThrStats, kLargestClassID in *. apply AGT; clear -Hz HC; first [lia | intros [Y ?]; discriminate].
      + replace (T + kThrStats + 80) with (T + kThrStats + 8 * Z.of_nat 10) by (clear; lia). eapply rw_cells_agree'; [| exact X10].
        cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros z Hz.
        unfold kThrCache, kPerClassSize, kThrCacheStats, kThrStats, kLargestClassID in *. apply AGT; clear -Hz HC; first [lia | intros [Y ?]; discriminate]. }
  assert (ETSA : AsanRepRefill2B.ts_nomap_agree (as_ts a) (as_ts a')).
  { rewrite ETS. destruct g; [apply AsanRepRefill2B.ts_nomap_agree_mmap|]; apply AsanRepRefill2B.ts_nomap_agree_refl. }
  assert (NCum : wr_at bsegs m' (region_beg SB c) (rg_mapped_user (region_of a' c))).
  { rewrite Er'', Er'. cbn [rg_mapped_user]. destruct (RC c ltac:(unfold kNumClasses, kLargestClassID in *; clear -HC; lia)) as [W _]. unfold region_of in W. fold r in W. eapply wr_at_transport; [exact W| exact WM]. }
  assert (NCfa' : exists junk', u32arr bsegs m' FA (map AsanRep.zw (rg_free (region_of a' c)) ++ junk') /\ 4 * Z.of_nat (length (rg_free (region_of a' c)) + length junk') = rg_mapped_fa (region_of a' c)).
  { rewrite Er'', Er'. cbn [rg_free rg_mapped_fa]. exists fjunk. split; [exact NCfa|]. rewrite Nat2Z.inj_add. exact NCfl. }
  assert (NCshu : rw_cells bsegs m' (kShadowBase + (region_beg SB c + rg_mapped_user r) / 8)
            [CB (Z.to_nat ((rg_mapped_user (region_of a' c) - rg_mapped_user r) / 8)) (repeat (AsanRep.zb kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_user (region_of a' c) - rg_mapped_user r) / 8)))]).
  { rewrite Er'', Er'. cbn [rg_mapped_user]. rewrite Z.sub_diag. cbn [Z.div Z.to_nat repeat]. apply BF_popT.rw_cells_CB0;
      unfold kShadowBase, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize, kLargestClassID in *; rewrite kHighMemBeg_val in E2; clear -A1 A3 E2 E3 E4 E5 HC CR; Z.div_mod_to_equations; lia. }
  assert (NCshf : rw_cells bsegs m' (kShadowBase + (FA + rg_mapped_fa r) / 8)
            [CB (Z.to_nat ((rg_mapped_fa (region_of a' c) - rg_mapped_fa r) / 8)) (repeat (AsanRep.zb kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (region_of a' c) - rg_mapped_fa r) / 8)))]).
  { rewrite Er'', Er'. cbn [rg_mapped_fa]. destruct g.
    - rewrite (GSZ eq_refl). replace (rg_mapped_fa r + kFreeArrayMapSize - rg_mapped_fa r) with kFreeArrayMapSize by (clear; lia). exact (proj2 (NCg eq_refl)).
    - rewrite (GSZ0 eq_refl), Z.sub_diag. cbn [Z.div Z.to_nat repeat]. apply BF_popT.rw_cells_CB0;
        subst FA; unfold kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize, kLargestClassID in *; rewrite kHighMemBeg_val in E2; clear -A5 A7 E2 E3 E4 E5 HC CR; Z.div_mod_to_equations; lia. }
  assert (REG' : 0 <= rg_alloc_user (region_of a' c) <= rg_mapped_user (region_of a' c) /\ rg_mapped_user (region_of a' c) mod kUserMapSize = 0 /\ rg_mapped_user (region_of a' c) <= kFreeArrayOffset
    /\ rg_alloc_user (region_of a' c) mod class_size c = 0
    /\ 0 <= rg_mapped_fa (region_of a' c) /\ rg_mapped_fa (region_of a' c) mod kFreeArrayMapSize = 0 /\ rg_mapped_fa (region_of a' c) <= kFreeArraySize
    /\ 4 * rg_num_freed (region_of a' c) <= rg_mapped_fa (region_of a' c)).
  { rewrite Er'', Er'. unfold rg_num_freed. cbn [rg_alloc_user rg_mapped_user rg_mapped_fa rg_free]. rewrite length_app, Nat2Z.inj_add, LCH, Z2Nat.id by (clear -HR; lia).
    clear -A1 A2 A3 A4 M1 M3 M4 M5. repeat split; assumption || lia. }
  refine (ARep_refill2 bsegs E0 [] D a a' m m' lo c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ereg' Ecache' _ _ (length (rg_free r)) _ HC WF REG' WM AGR LOC REP BS Tpl IMG_IN IMG_LO IMG_LOW AK TDN _ NCrows NCrow' NCcst' NCthr ETSA NCum NCfa' NCshu NCshf);
    try (subst a' a2 a1; unfold push_st, rta_st, st_fa, dr_st; destruct g; destruct a; reflexivity).
  - rewrite Er'', Er'. cbn [rg_mapped_user]. unfold region_of. fold r. clear; lia.
  - rewrite Er'', Er'. cbn [rg_mapped_fa]. unfold region_of. fold r. exact M2.
  - rewrite Er'', Er'. cbn [rg_free]. unfold region_of. fold r. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, length_app. split; [reflexivity| split; clear; lia].
  - rewrite Er''. exact NCri.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FPW5a (lo cb ab g l8 : Z) (z : Z) : Prop :=
     lo <= z \/ (cb <= z < cb + 4) \/ (ab <= z < ab + 8)
  \/ (kShadowBase + g <= z < kShadowBase + g + l8)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56).

(* [comment removed for export] *)
Theorem R5a_holds :
  forall (a : astate) (m m' : mem) (lo cb c i j g : Z) (D : list batch) (cm : chunkmeta),
  let n := cm_n cm in let ab := cm_alloc_beg cm in let l8 := (n + 7) / 8 in
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> cm_prim cm = Some c -> 8 * g = cb + 16 ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPW5a lo cb ab g l8 z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (kShadowBase + g) [CB (Z.to_nat l8) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat l8))] ->
  rw_cells bsegs m' (T + kThrStats + 40) [C8 (wz (ts_real_frees (as_ts a) + 1)); C8 (wz (ts_really_freed (as_ts a) + n))] ->
  ARep bsegs E0 (DepotR bsegs E0) (AsanRepRelB.rel_st cb n a) m'.
Proof.
  intros a m m' lo cb c i j g D cm n ab l8 Hcm ST _ G8 REP WF RENV WM AG LO NSH NST.
  exact (AsanRepRelB.ARep_after_rel bsegs E0 D a m m' lo cb cm i j g Hcm ST G8 REP WF RENV WM AG LO NSH NST).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ldl_st (cb : Z) (cm : chunkmeta) (sc : secchunk) (i : nat) (a : astate) : astate :=
  let n := cm_n cm in let msz := sc_map_size sc in
  let a1 := upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a) in
  let secl := as_sec a in let lastc := List.last secl sc in
  let a2 := upd_glob (fun x => x - msz) (fun x => x - msz)
              (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st) (ss_n_frees st + 1) (ss_cur st - msz) (ss_max st) (ss_by_size_log st))
                (upd_sec_stale (fun st => <[Z.of_nat (Nat.pred (length secl)) := sc_map_beg lastc]> st)
                  (upd_sec (fun _ => removelast (list_set secl i lastc)) a1))) in
  upd_ts (ts_on_munmap msz) a2.
Definition FPW7 (a : astate) (lo : Z) (sc : secchunk) (i : nat) (z : Z) : Prop :=
  let A := sc_map_beg sc in let L := sc_map_size sc in let lastc := List.last (as_sec a) sc in
     lo <= z
  \/ (ae_instance E0 + kInsNReserved + 8 <= z < ae_instance E0 + kInsNReserved + 17)
  \/ (ae_instance E0 + kInsSecStats + 8 <= z < ae_instance E0 + kInsSecStats + 24)
  \/ (ae_instance E0 + kInsSecMutex <= z < ae_instance E0 + kInsSecMutex + 4)
  \/ (ae_instance E0 + kInsGlobalStats + 16 <= z < ae_instance E0 + kInsGlobalStats + 32)
  \/ (ae_ptr_array E0 + 8 * Z.of_nat i <= z < ae_ptr_array E0 + 8 * Z.of_nat i + 8)
  \/ (sc_map_beg lastc + 24 <= z < sc_map_beg lastc + 32)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56) \/ (T + kThrStats + 88 <= z < T + kThrStats + 104)
  \/ (kShadowBase + A / 8 <= z < kShadowBase + A / 8 + L / 8)
  \/ (A <= z < A + L).

(* [comment removed for export] *)
Theorem R7_holds :
  (forall r, In r (List.tl (arep_img_ranges E0)) -> fst r + snd r <= ae_instance E0 \/ ae_instance E0 + 3632 <= fst r) ->
  forall (a : astate) (m m' : mem) (lo cb i0 j0 : Z) (i : nat) (D : list batch) (cm : chunkmeta) (sc : secchunk) (junk : list word),
  let n := cm_n cm in let A := sc_map_beg sc in let L := sc_map_size sc in let lastc := List.last (as_sec a) sc in
  let a' := ldl_st cb cm sc i a in let st := as_sec_stats a in let ts := as_ts a in
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i0 j0 -> cm_prim cm = None ->
  nth_error (as_sec a) i = Some sc -> cm_alloc_beg cm = A + kPageSize ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  (forall z, 0 <= z < 2^64 -> ~ FPW7 a lo sc i z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (ae_instance E0 + kInsNReserved) [C8 (wz (as_ptr_committed a)); C8 (wz (n_chunks a - 1)); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecStats) [C8 (wz (ss_n_allocs st)); C8 (wz (ss_n_frees st + 1)); C8 (wz (ss_cur st - L)); C8 (wz (ss_max st))] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecMutex) [C4 (wz 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsGlobalStats + 16) [C8 (wz (as_glob_allocated a - L)); C8 (wz (as_glob_mapped a - L))] ->
  u64arr bsegs m' (ae_ptr_array E0) (map (fun c => wz (sc_map_beg c)) (as_sec a') ++ junk) -> (length (as_sec a') + length junk = Z.to_nat kChunksBlockCount)%nat ->
  (sc_map_beg lastc <> A -> rw_cells bsegs m' (sc_map_beg lastc + 24) [C8 (wz (Z.of_nat i))]) ->
  rw_cells bsegs m' (T + kThrStats + 40) [C8 (wz (ts_real_frees ts + 1)); C8 (wz (ts_really_freed ts + n))] ->
  rw_cells bsegs m' (T + kThrStats + 88) [C8 (wz (ts_munmaps ts + 1)); C8 (wz (ts_munmaped ts + L))] ->
  rw_cells bsegs m' (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))] ->
  ARep bsegs E0 (DepotR bsegs E0) a' m'.
Proof.
  intros IMG_INST a m m' lo cb i0 j0 i D cm sc junk n A L lastc a' st ts Hcm _ PC NTH AB REP WF RENV AG LO N1 N2 N3 N4 N5 N6 N7 N8 N9 N10.
  exact (AsanRepLdlB.ARep_after_ldl bsegs E0 D a m m' lo cb cm sc i junk Hcm PC NTH AB REP WF RENV AG LO IMG_INST N1 N2 N3 N4 N5 N6 N7 N8 N9 N10).
Qed.
End QRepL.
End RC__1.
