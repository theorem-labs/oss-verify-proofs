(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow StepA StepA2 SysStepA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot
  AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf10 AsanHoare AsanHit AsanRepHit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AF_fakestack_rep AF_unwind AF_kit AF_kit3 A_bundle A_init5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac unset_all := repeat match goal with x := _ |- _ => subst x end.
(* [comment removed for export] *)
Ltac orlia_atom := first [lia | Z.div_mod_to_equations; lia].
Ltac orlia := lazymatch goal with |- _ \/ _ => first [left; orlia_atom | right; orlia] | |- _ => orlia_atom end.
Ltac zshifts := repeat match goal with | H : context [Z.shiftl ?a ?b] |- _ => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v end.
(* [comment removed for export] *)
Ltac prune_lets := repeat match goal with x := _ |- _ => clear x end.
Ltac nrm := rewrite ?kHighMemBeg_val in *; unfold alloc_ceiling, kResvLen, kDepotNodeBlockBytes, kStoreBlockBytes, kPtrArrayLen, kSpaceSize, kPageSize, kStoreBlockFrames, kDepotNodesPerBlock, kStoreBlockCount, kTabSize, kShadowBase, kRegionSize, kFreeArrayOffset, kUserMapSize in *.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma find_segment_In : forall segs a n s, find_segment segs a n = Some s -> In s segs.
Proof.
  induction segs as [|x segs IH]; cbn; intros a n s H; [discriminate|].
  destruct (_ && _); [injection H; auto| right; eapply IH; exact H].
Qed.
Lemma asegs_readable : Forall (fun s => seg_readable s = true) asegs.
Proof. unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. repeat (apply Forall_cons; [reflexivity|]). apply Forall_nil. Qed.
Lemma wr_at_mrd : forall m a n i, wr_at asegs m a n -> 0 <= i < n -> exists b, mrd asegs m (wa (a + i)) = Some b.
Proof.
  intros m a n i (A0 & AN & W) Hi. specialize (W i Hi). unfold mrd. unfold wview in W.
  destruct (m (wa (a + i))) as [b|] eqn:E; [exists b; reflexivity|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment asegs (bv_unsigned (wa (a + i))) 1) as [sg|] eqn:FS; [| exfalso; apply W; reflexivity].
  pose proof (proj1 (Forall_forall _ _) asegs_readable sg (find_segment_In _ _ _ _ FS)) as RD. cbn beta in RD. rewrite RD.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (seg_writable sg); [| exfalso; apply W; reflexivity].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (wa (a + i)) - Z.of_N (seg_base sg)))) as [b|] eqn:SB;
    [| exfalso; apply W; reflexivity].
  cbn. eexists. reflexivity.
Qed.
Lemma wr_at_bytes : forall m a n, wr_at asegs m a n -> 0 <= n -> exists bs, length bs = Z.to_nat n /\ bytes_at asegs m a bs.
Proof.
  intros m a n WR N0. pose proof WR as (A0 & AN & _).
  exists (map (fun i => match mrd asegs m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  split; [rewrite length_map, length_seq; reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq, Z2Nat.id by exact N0; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. replace (Nat.ltb i (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map Nat.add].
  destruct (wr_at_mrd m a n (Z.of_nat i) WR ltac:(lia)) as [b Hb]. rewrite Hb. reflexivity.
Qed.


Lemma bytes_at_sub : forall m A bs k j,
  bytes_at asegs m A bs -> (k + j <= length bs)%nat -> bytes_at asegs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m A bs k j H Hkj.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn j (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

(* [comment removed for export] *)
Lemma u8arr_cell : forall m A bs k (c : cell),
  u8arr asegs m A bs -> (k + csize c <= length bs)%nat -> cell_wf c -> cbytes c = firstn (csize c) (skipn k bs) ->
  rw_cells asegs m (A + Z.of_nat k) [c].
Proof.
  intros m A bs k c [Hb Hw] Hk WF E. split; [split|].
  - cbn. split; [exact WF| exact I].
  - cbn [cells_bytes]. rewrite app_nil_r, E. apply bytes_at_sub; assumption.
  - cbn [cells_size]. rewrite Nat.add_0_r. eapply wr_at_sub; [exact Hw| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma u64arr_cell : forall m A ws i w, u64arr asegs m A ws -> nth_error ws i = Some w -> rw_cells asegs m (A + 8 * Z.of_nat i) [C8 w].
Proof.
  intros m A ws i w [Hb Hw] Hn. pose proof (nth_error_split ws i w Hn) as (l1 & l2 & -> & L1).
  rewrite u64s_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb]. cbn [u64s map flat_map] in Hb.
  change (flat_map le8 l2) with (u64s l2) in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite u64s_length, L1 in Hb. replace (Z.of_nat (8 * i)) with (8 * Z.of_nat i) in Hb by lia.
  split; [split; [cbn; auto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. eapply wr_at_sub; [exact Hw| lia|]. rewrite length_app, <- L1. cbn [length]. lia.
Qed.
Lemma u64arr_prefix3 : forall m A w0 w1 w2 ws, u64arr asegs m A (w0 :: w1 :: w2 :: ws) -> rw_cells asegs m A [C8 w0; C8 w1; C8 w2].
Proof.
  intros m A w0 w1 w2 ws H.
  pose proof (u64arr_cell m A _ 0 w0 H eq_refl) as H0. pose proof (u64arr_cell m A _ 1 w1 H eq_refl) as H1. pose proof (u64arr_cell m A _ 2 w2 H eq_refl) as H2.
  rewrite Z.mul_0_r, Z.add_0_r in H0.
  apply (rwc_join_at asegs m A (A + 8 * Z.of_nat 1) [C8 w0] [C8 w1; C8 w2]); [exact H0| | cbn; lia].
  apply (rwc_join_at asegs m _ (A + 8 * Z.of_nat 2) [C8 w1] [C8 w2]); [exact H1| exact H2| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma wr_at_CB : forall m A n, wr_at asegs m A n -> 0 <= n -> exists junk, rw_cells asegs m A [CB (Z.to_nat n) junk].
Proof.
  intros m A n W Hn. destruct (wr_at_bytes m A n W Hn) as (bs & L & B). exists bs. split; [split|].
  - cbn. split; [exact L| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.
(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (AF_kit3.k_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply AF_kit3.k_Z_to_le_bytes_to_Z.
Qed.
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le2, le_bytes_to_word.
  pose proof (AF_kit3.k_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 2))%Z with (2^16)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply AF_kit3.k_Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma wr_at_hdr : forall m A, wr_at asegs m A 16 -> exists (j0 j1 : byte) (j2 j3 j4 : word), rw_cells asegs m A [C1 j0; C1 j1; C2 j2; C4 j3; C8 j4].
Proof.
  intros m A W. destruct (wr_at_CB m A 16 W ltac:(lia)) as (bs & H). pose proof (proj1 (proj1 (proj1 H))) as L0. assert (L : length bs = 16%nat) by (cbn in L0; first [exact (proj1 L0) | exact L0]). clear L0.
  destruct bs as [|b0 [|b1 bs]]; [cbn in L; lia| cbn in L; lia|].
  exists b0, b1, (le_bytes_to_word (firstn 2 bs)), (le_bytes_to_word (firstn 4 (skipn 2 bs))), (le_bytes_to_word (skipn 6 bs)).
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. cbn in L. rewrite le2_of_bytes, le4_of_bytes, AF_kit3.le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite app_nil_r. f_equal. f_equal. replace (skipn 6 bs) with (skipn 4 (skipn 2 bs)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 4 (skipn 2 bs)). rewrite ?app_nil_r. apply firstn_skipn.
Qed.
Lemma wr_at_node : forall m A, wr_at asegs m A 16 -> exists (d0 : word) (d1 d2 : word), rw_cells asegs m A [C8 d0; C4 d1; C4 d2].
Proof.
  intros m A W. destruct (wr_at_CB m A 16 W ltac:(lia)) as (bs & H). pose proof (proj1 (proj1 (proj1 H))) as L0. assert (L : length bs = 16%nat) by (cbn in L0; first [exact (proj1 L0) | exact L0]). clear L0.
  exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (firstn 4 (skipn 8 bs))), (le_bytes_to_word (skipn 12 bs)).
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite AF_kit3.le8_of_bytes, !le4_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite app_nil_r. replace (skipn 12 bs) with (skipn 4 (skipn 8 bs)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 4 (skipn 8 bs)). rewrite ?app_nil_r. apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma shadow_join : forall m K lo k v,
  (forall g, lo <= g < lo + Z.of_nat k -> rw_cells asegs m (K + g) [C1 (Z_to_bv 8 v)]) -> (0 < k)%nat ->
  rw_cells asegs m (K + lo) [CB k (repeat (Z_to_bv 8 v) k)].
Proof.
  intros m K lo k v H Hk. revert lo H. induction k as [|k IH]; intros lo H; [lia|].
  destruct k as [|k'].
  - pose proof (H lo ltac:(lia)) as X. eapply rw_cells_recast; [exact X| cbn; auto| reflexivity| reflexivity].
  - pose proof (H lo ltac:(lia)) as X. pose proof (IH ltac:(lia) (lo + 1) ltac:(intros g Hg; apply H; lia)) as Y.
    pose proof (rwc_join_at asegs m (K + lo) (K + (lo + 1)) [C1 (Z_to_bv 8 v)] _ X Y ltac:(cbn; lia)) as Z0.
    eapply rw_cells_recast; [exact Z0| cbn; rewrite repeat_length; auto| reflexivity| cbn; lia].
Qed.

Lemma AKern_ext : forall E s s' mo,
  as_regions s' = as_regions s -> as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s ->
  AKern E s mo -> AKern E s' mo.
Proof.
  intros E s s' mo R P S NB SB K.
  assert (GR : forall c, get_region s' c = get_region s c) by (intros c; unfold get_region; rewrite R; reflexivity).
  destruct K; constructor; rewrite ?GR, ?P, ?S, ?NB, ?SB; auto.
  - intros c Hc. rewrite GR. auto.
  - intros c Hc. rewrite GR. auto.
  - intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; intros c Hc; rewrite GR; auto.
Qed.
Lemma AKern_hit : forall E key n s mo, AKern E s mo -> AKern E (amalloc_hit_st E key n s) mo.
Proof.
  intros E key n s mo K. eapply AKern_ext; [apply hit_regions| apply hit_ptr| apply hit_sec| apply hit_node_blocks| apply hit_store_blocks| exact K].
Qed.

Lemma Permutation_filterb : forall {A} (f : A -> bool) (l l' : list A), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip; exact IH| exact IH].
  - destruct (f y); destruct (f x); try apply perm_swap; try apply perm_skip; reflexivity.
  - etransitivity; eassumption.
Qed.
(* [comment removed for export] *)
Lemma live_blocks_hit : forall E key n s, as_chunks s !! hcb E n s = None -> 1 <= n <= 448 ->
  Permutation (live_blocks (amalloc_hit_st E key n s)) ((hub E n s, n) :: live_blocks s).
Proof.
  intros E key n s FR Hn. unfold live_blocks, chunk_list. rewrite hit_chunks.
  pose proof (map_to_list_insert (as_chunks s) (hcb E n s) (hcm E key n s) FR) as P.
  etransitivity. { apply Permutation_map. apply Permutation_filterb. exact P. }
  cbn [List.filter snd hcm cm_state map].
  pose proof (small_primary n Hn) as (_ & _ & P3 & _).
  replace (cm_user_beg (hcm E key n s), cm_n (hcm E key n s)) with (hub E n s, n); [apply perm_skip; reflexivity|].
  unfold hub, cm_user_beg, rz_size. cbn [cm_alloc_beg cm_rz_log cm_n hcm]. rewrite P3. reflexivity.
Qed.

Lemma live_block_loc : forall E (P : list Z) (D : list batch) s blo bsz, AWf E P D s -> In (blo, bsz) (live_blocks s) ->
  exists k cm, as_chunks s !! k = Some cm /\ cm_user_beg cm = blo /\ cm_n cm = bsz /\ 1 <= bsz
    /\ blk_lo cm + 16 <= blo /\ blo + bsz <= blk_hi s cm
    /\ match cm_prim cm with
       | Some c' => 1 <= c' <= kLargestClassID /\ region_beg (ae_space_beg E) c' <= blk_lo cm /\ blk_hi s cm <= region_beg (ae_space_beg E) c' + rg_mapped_user (get_region s c')
       | None => exists sc, In sc (as_sec s) /\ blk_lo cm = sc_map_beg sc + kPageSize /\ blk_hi s cm = sc_map_beg sc + sc_map_size sc
       end.
Proof.
  intros E P D s blo bsz WF Hin. unfold live_blocks, chunk_list in Hin.
  apply in_map_iff in Hin. destruct Hin as ([k cm] & E1 & Hin). cbn in E1. injection E1 as E2 E3.
  apply filter_In in Hin. destruct Hin as [Hin AL]. cbn in AL.
  apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin.
  exists k, cm. split; [exact Hin|]. split; [exact E2|]. split; [exact E3|].
  pose proof (chunk_user_in_block E P D s k cm WF Hin) as (U1 & U2 & _). unfold user_lo, user_hi in U1, U2.
  pose proof (chunk_block_committed E P D s k cm WF Hin) as CB.
  pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 k cm Hin) as (_ & B & _).
  split; [lia|]. split; [lia|]. split; [lia|]. exact CB.
Qed.

Lemma u8arr_of_cells : forall m A cs, rw_cells asegs m A cs -> u8arr asegs m A (cells_bytes cs).
Proof.
  intros m A cs [[WF B] W]. split; [exact B|]. rewrite (cells_bytes_length _ WF). exact W.
Qed.

Lemma zw_wrap_add : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
  intros x k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Section TKit.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

(* [comment removed for export] *)
Definition AHKc : aps -> list ablock -> list fblock -> mem -> Model -> Prop :=
  AHK stdio_rep (rt_misc5 FSB0 PL0) E0 FSB0 HR0 L0 RES0 EB0.

(* [comment removed for export] *)
Definition hit_case (s : aps) (n : Z) : Prop :=
  let a := aps_alloc s in
     1 <= n <= 448
  /\ get_cache a (class_id (needed1 n)) <> []
  /\ as_cache_inited a = true
  /\ (depot_n_ids E0 a + 1) mod kDepotNodesPerBlock <> 0                      (* [comment removed for export] *)
  /\ as_frames a mod kStoreBlockFrames + 31 <= kStoreBlockFrames              (* [comment removed for export] *)
  /\ as_frames a / kStoreBlockFrames < zlen (store_blocks E0 a).              (* [comment removed for export] *)
End TKit.

Lemma nth_error_ziota : forall k a i, (i < k)%nat -> nth_error (ziota a k) i = Some (a + Z.of_nat i).
Proof. induction k as [|k IH]; intros a i Hi; [lia|]. destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia. Qed.
Lemma last_nth_error : forall (l : list Z), l <> [] -> nth_error l (Nat.pred (length l)) = Some (List.last l 0).
Proof.
  induction l as [|y l IH]; intros H; [congruence|]. destruct l as [|z l']; [reflexivity|].
  cbn [length Nat.pred]. cbn [nth_error]. rewrite <- IH by congruence. reflexivity.
Qed.
Lemma nth_error_map_app : forall (l : list Z) junk i y, nth_error l i = Some y -> nth_error (map (fun z => Z_to_bv 64 z) l ++ junk) i = Some (Z_to_bv 64 y).
Proof. intros l junk i y H. rewrite nth_error_app1 by (rewrite length_map; exact (nth_error_lt _ _ _ H)). rewrite nth_error_map, H. reflexivity. Qed.
End RC__1.
