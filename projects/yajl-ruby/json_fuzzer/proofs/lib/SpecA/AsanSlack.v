(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanKern AsanBudget AsanBudget2 AsanGap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section SL.
Variable E : aenv.

(* [comment removed for export] *)
Definition amaps (a : astate) : list (word * word) :=
  map (fun sc => went (sc_map_beg sc) (sc_map_size sc)) (as_sec a)
  ++ map (fun b => went b kDepotNodeBlockBytes) (as_node_blocks a)
  ++ map (fun b => went b kStoreBlockBytes) (as_store_blocks a).

Definition aweight (N : Z) (a : astate) : Z := gap_weight N (amaps a).

Lemma zlen_cons' : forall {A} (x : A) l, zlen (x :: l) = zlen l + 1.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.

Lemma gap_weight_map_const : forall N (l : list Z) sz, 0 <= sz < 2^64 ->
  gap_weight N (map (fun b => went b sz) l) = zlen l * (sz + N + 4095).
Proof.
  intros N l sz Hsz. rewrite gap_weight_map. induction l as [|x l IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH, zlen_cons'. unfold went, kwz; cbn [snd]. rewrite gap_u64_lit by lia. lia.
Qed.

Lemma gap_weight_map_sec : forall N (l : list secchunk),
  (forall sc, In sc l -> 0 <= sc_map_size sc < 2^64) ->
  gap_weight N (map (fun sc => went (sc_map_beg sc) (sc_map_size sc)) l)
  = fold_right (fun c acc => sc_map_size c + acc) 0 l + zlen l * (N + 4095).
Proof.
  intros N l Hl. rewrite gap_weight_map. induction l as [|x l IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH by (intros sc Hsc; apply Hl; right; exact Hsc). rewrite zlen_cons'.
  unfold went, kwz; cbn [snd]. rewrite gap_u64_lit by (apply Hl; left; reflexivity). lia.
Qed.

(* [comment removed for export] *)
Lemma aweight_eq : forall N a, (forall sc, In sc (as_sec a) -> 0 <= sc_map_size sc < 2^64) ->
  aweight N a = sec_bytes a + zlen (as_sec a) * (N + 4095)
                + zlen (as_node_blocks a) * (kDepotNodeBlockBytes + N + 4095)
                + zlen (as_store_blocks a) * (kStoreBlockBytes + N + 4095).
Proof.
  intros N a Ha. unfold aweight, amaps, sec_bytes. rewrite !gap_weight_app.
  rewrite (gap_weight_map_sec N (as_sec a) Ha).
  rewrite !gap_weight_map_const by (unfold kDepotNodeBlockBytes, kStoreBlockBytes; lia). lia.
Qed.

Lemma amaps_length : forall a, zlen (amaps a) = zlen (as_sec a) + zlen (as_node_blocks a) + zlen (as_store_blocks a).
Proof. intros a. unfold amaps, zlen. rewrite !app_length, !map_length. lia. Qed.

(* [comment removed for export] *)
Lemma sec_sizes_u64 : forall P D a, AWf E P D a -> forall sc, In sc (as_sec a) -> 0 <= sc_map_size sc < 2^64.
Proof.
  intros P D a WF sc Hsc. destruct WF as (_ & _ & _ & _ & _ & (_ & _ & WS & _) & _).
  destruct (WS sc Hsc) as (_ & AM & TOP & POS & _). pose proof alloc_ceiling_range.
  destruct AM as [[A1 A2]|[A1 A2]]; unfold kLowAppEnd in *; try lia. rewrite kHighMemBeg_val in A1. lia.
Qed.

Lemma sec_bytes_nonneg : forall P D a, AWf E P D a -> 0 <= sec_bytes a.
Proof.
  intros P D a WF. pose proof (sec_sizes_u64 P D a WF) as H. unfold sec_bytes.
  induction (as_sec a) as [|x l IH]; cbn; [lia|]. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros sc Hsc; apply H; right; exact Hsc)). lia.
Qed.

Lemma interiors_nonneg : forall P D a, AWf E P D a -> 0 <= interiors_a a.
Proof.
  intros P D a WF. pose proof (sec_sizes_u64 P D a WF) as H. unfold interiors_a.
  induction (as_sec a) as [|x l IH]; cbn; [lia|]. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros sc Hsc; apply H; right; exact Hsc)).
  destruct (kBigMapSize <=? sc_map_size x); [| lia]. pose proof (Z.div_pos (sc_map_size x) 32768 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma sec_zlen_bound : forall a, AWf E [] [] a -> binv a -> AQbound a -> zlen (as_sec a) <= nbig_live a + 4177.
Proof.
  intros a WF HBI [TQ GQ]. pose proof (sec_count E a WF HBI) as C. unfold kThreadQuarantineMax, kQuarantineMax in *. lia.
Qed.

Lemma node_blocks_bound : forall a, depot_inv E a -> zlen (as_node_blocks a) <= depot_n_ids E a / kDepotNodesPerBlock.
Proof.
  intros a (D1 & _). unfold kDepotNodesPerBlock in *. apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

Lemma store_blocks_bound : forall a, depot_inv E a -> zlen (as_store_blocks a) <= (ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames.
Proof.
  intros a (_ & D2 & D3 & _). unfold kStoreBlockFrames in *. apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Theorem aweight_bound : forall N a, 0 <= N -> AWf E [] [] a -> binv a -> AQbound a -> depot_inv E a ->
  aweight N a <= 4096 * (dep_live a + 100000) + (nbig_live a + 4177) * (N + 4095)
                 + (depot_n_ids E a / kDepotNodesPerBlock) * (kDepotNodeBlockBytes + N + 4095)
                 + ((ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames) * (kStoreBlockBytes + N + 4095).
Proof.
  intros N a HN WF HBI QB DI.
  rewrite (aweight_eq N a (sec_sizes_u64 [] [] a WF)).
  pose proof (M1 E a WF QB HBI) as HM1. pose proof (interiors_nonneg [] [] a WF) as I0.
  pose proof (sec_zlen_bound a WF HBI QB) as SC. pose proof (node_blocks_bound a DI) as NB. pose proof (store_blocks_bound a DI) as STB.
  pose proof (zlen_nonneg (as_sec a)). pose proof (zlen_nonneg (as_node_blocks a)). pose proof (zlen_nonneg (as_store_blocks a)).
  unfold kDepotNodeBlockBytes, kStoreBlockBytes in *.
  assert (A1 : zlen (as_sec a) * (N + 4095) <= (nbig_live a + 4177) * (N + 4095)) by nia.
  assert (A2 : zlen (as_node_blocks a) * (2 ^ 20 + N + 4095) <= depot_n_ids E a / kDepotNodesPerBlock * (2 ^ 20 + N + 4095)) by nia.
  assert (A3 : zlen (as_store_blocks a) * (2 ^ 23 + N + 4095) <= (ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames * (2 ^ 23 + N + 4095)) by nia.
  lia.
Qed.

(* [comment removed for export] *)
Corollary amaps_count_bound : forall a, AWf E [] [] a -> binv a -> AQbound a -> depot_inv E a ->
  zlen (amaps a) <= nbig_live a + 4177 + depot_n_ids E a / kDepotNodesPerBlock + (ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames.
Proof.
  intros a WF HBI QB DI. rewrite amaps_length.
  pose proof (sec_zlen_bound a WF HBI QB). pose proof (node_blocks_bound a DI). pose proof (store_blocks_bound a DI). lia.
Qed.

(* [comment removed for export] *)
Lemma aweight_sec_app : forall N a sc, (forall x, In x (as_sec a) -> 0 <= sc_map_size x < 2^64) -> 0 <= sc_map_size sc < 2^64 ->
  aweight N (upd_sec (fun l => l ++ [sc]) a) = aweight N a + (sc_map_size sc + N + 4095).
Proof.
  intros N a sc Ha Hsc. unfold aweight, amaps. cbn [as_sec as_node_blocks as_store_blocks upd_sec].
  rewrite map_app, !gap_weight_app. cbn [map gap_weight went kwz snd]. unfold went, kwz. cbn [snd]. rewrite gap_u64_lit by lia. lia.
Qed.

End SL.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PSA (N : Z) (h : VmMaps) : Prop :=
  4096 + N + gap_weight N (vm_reserved h ++ vm_maps h) <= alloc_top h.

Lemma PSA_mono : forall N N' h, 0 <= N' <= N -> PSA N h -> PSA N' h.
Proof. intros N N' h HN HP. unfold PSA in *. pose proof (gap_weight_mono N' N (vm_reserved h ++ vm_maps h) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Theorem PSA_window : forall N h nZ, PSA N h -> 0 <= nZ <= N -> alloc_top h < 2^64 ->
  exists g, g mod page_size = 0 /\ 0 < g /\ g + nZ <= alloc_top h
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros N h nZ HP HnZ HT. apply null_hint_window; [lia| exact HT|].
  pose proof (PSA_mono N nZ h HnZ HP) as HP'. unfold PSA, page_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma PSA_same : forall N h h', vm_reserved h' = vm_reserved h -> vm_maps h' = vm_maps h -> alloc_top h' = alloc_top h -> PSA N h -> PSA N h'.
Proof. intros N h h' R M T HP. unfold PSA in *. rewrite R, M, T. exact HP. Qed.

Lemma PSA_cons : forall N h h' a n,
  vm_reserved h' = vm_reserved h -> vm_maps h' = (a, n) :: vm_maps h -> alloc_top h' = alloc_top h ->
  4096 + N + gap_weight N (vm_reserved h ++ vm_maps h) + (bv_unsigned n + N + 4095) <= alloc_top h -> PSA N h'.
Proof.
  intros N h h' a n R M T HP. unfold PSA. rewrite R, M, T. rewrite gap_weight_app in HP. rewrite gap_weight_app, gap_weight_cons. lia.
Qed.

Lemma PSA_remove : forall N h h' a, 0 <= N ->
  vm_reserved h' = vm_reserved h -> vm_maps h' = map_remove (vm_maps h) a -> alloc_top h' = alloc_top h -> PSA N h -> PSA N h'.
Proof.
  intros N h h' a HN R M T HP. unfold PSA in *. rewrite R, M, T. rewrite gap_weight_app in HP. rewrite gap_weight_app.
  pose proof (gap_weight_remove_le N (vm_maps h) a HN). lia.
Qed.

Lemma PSA_perm : forall N h h' l, vm_reserved h' = vm_reserved h -> Permutation (vm_maps h') l -> alloc_top h' = alloc_top h ->
  4096 + N + gap_weight N (vm_reserved h) + gap_weight N l <= alloc_top h -> PSA N h'.
Proof.
  intros N h h' l R P T HP. unfold PSA. rewrite R, T, gap_weight_app, (gap_weight_perm N _ _ P). lia.
Qed.

(* [comment removed for export] *)
Theorem PSA_of_parts : forall N h R0 L0 fog a WS WF WA,
  vm_reserved h = R0 -> Permutation (vm_maps h) (L0 ++ fog ++ amaps a) ->
  gap_weight N (R0 ++ L0) <= WS -> gap_weight N fog <= WF -> aweight N a <= WA ->
  4096 + N + WS + WF + WA <= alloc_top h -> PSA N h.
Proof.
  intros N h R0 L0 fog a WS WF WA R P HS HF HA HT. unfold PSA, aweight in *.
  rewrite R, gap_weight_app, (gap_weight_perm N _ _ P), !gap_weight_app. rewrite gap_weight_app in HS. lia.
Qed.

(* [comment removed for export] *)
Lemma gap_weight_of_totals : forall N l SZ CNT, 0 <= N -> gw_sizes l <= SZ -> Z.of_nat (length l) <= CNT ->
  gap_weight N l <= SZ + CNT * (N + 4095).
Proof. intros N l SZ CNT HN HS HC. rewrite gap_weight_sizes. nia. Qed.

End RC__1.
