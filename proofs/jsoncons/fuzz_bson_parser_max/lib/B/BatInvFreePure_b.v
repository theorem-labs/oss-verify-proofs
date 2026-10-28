(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceABx As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b
     BatClsRefill_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFxQ_b BatFxBatch2_b BatFxBatch3_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_bt_bytes (b : art_batch) : Z := 8192 + fold_right (fun it z => snd it + z) 0 (bt_items b).
Definition art_qb (b : art_batch) : art_qbatch := (bt_addr b, map fst (bt_items b), art_bt_bytes b).

Lemma art_qhead_map : forall bs, art_qhead (map art_qb bs) = match bs with [] => 0 | b' :: _ => bt_addr b' end.
Proof. intros [|b r]; reflexivity. Qed.

Lemma art_batch_list_q : forall M bs f l, art_batch_list M bs f l <-> art_qlist M (map art_qb bs) f l.
Proof.
  intros M bs. induction bs as [|b r IH]; intros f l; cbn [art_batch_list art_qlist map]; [tauto|].
  rewrite art_qhead_map. unfold art_qrec. cbn [art_qb qb_addr qb_items qb_size fst snd]. rewrite length_map. fold (art_bt_bytes b).
  split.
  - intros (E & Hl & C1 & C2 & CI & LK & R). split; [exact E|]. split.
    { split; [exact Hl|]. split; [exact C1|]. split; [exact C2|]. intros j it Hj. rewrite nth_error_map in Hj.
      destruct (nth_error (bt_items b) j) as [it0|] eqn:Ej; cbn in Hj; [|discriminate]. injection Hj as <-. exact (CI j it0 Ej). }
    destruct r as [|b' r']; cbn [map].
    + destruct LK as (El & C0). split; [exact El|]. split; [exact C0|]. apply IH. exact R.
    + split; [exact I|]. split; [exact LK|]. apply IH. exact R.
  - intros (E & (Hl & C1 & C2 & CI) & LK & C0 & R). split; [exact E|]. split; [exact Hl|]. split; [exact C1|]. split; [exact C2|]. split.
    { intros j it Hj. apply (CI j (fst it)). rewrite nth_error_map, Hj. reflexivity. }
    destruct r as [|b' r']; cbn [map] in *.
    + split; [split; [exact LK|exact C0]|]. apply IH. exact R.
    + split; [exact C0|]. apply IH. exact R.
Qed.

Lemma art_batches_bytes_q : forall bs, art_batches_bytes bs = art_qbytes (map art_qb bs).
Proof. induction bs as [|b r IH]; cbn [art_batches_bytes art_qbytes fold_right map]; [reflexivity|]. unfold art_batches_bytes in IH. rewrite IH. reflexivity. Qed.

Lemma art_batches_bytes_app : forall a b, art_batches_bytes (a ++ b) = art_batches_bytes a + art_batches_bytes b.
Proof. intros a b. rewrite !art_batches_bytes_q, map_app. apply art_qbytes_app. Qed.

Lemma art_nq_app : forall a b, art_nq (a ++ b) = art_nq a + art_nq b.
Proof. intros a b. unfold art_nq. induction a as [|x r IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma art_nq_nonneg' : forall bs, 0 <= art_nq bs.
Proof. induction bs as [|b r IH]; cbn [art_nq fold_right]; [lia|]. unfold art_nq in IH. lia. Qed.

(* [comment removed for export] *)
Inductive art_fk : Type := FKP (c w : Z) | FKS (i : nat).

Definition art_lastb (bs : list art_batch) : art_batch := last bs (BATCH 0 []).
(* [comment removed for export] *)
Definition art_free_newb (qt : list art_batch) : bool :=
  art_enq_newb (Z.of_nat (length qt)) (Z.of_nat (length (bt_items (art_lastb qt)))).
Definition art_qt_add (qt : list art_batch) (b : Z) (it : Z * Z) : list art_batch :=
  if art_free_newb qt then qt ++ [BATCH b [it]]
  else removelast qt ++ [BATCH (bt_addr (art_lastb qt)) (bt_items (art_lastb qt) ++ [it])].
Fixpoint art_sec_quar (i : nat) (l : list art_sec) : list art_sec :=
  match l, i with
  | [], _ => []
  | s :: r, O => SEC (sc_map s) (sc_msize s) (sc_u s) (sc_n s) true :: r
  | s :: r, Datatypes.S j => s :: art_sec_quar j r
  end.

Definition art_gs_free {FSG : Type} (G : art_gs FSG) (spb : Z) (k : art_fk) (u n : Z) (kb : nat) : art_gs FSG :=
  let cl24 := g_cls FSG G 24 in
  let newb := art_free_newb (g_qt FSG G) in
  let wb := art_ca_cptr 24 cl24 in
  GS FSG (g_log FSG G ++ art_enq_events newb spb cl24) (newb || g_inited FSG G)
     (fun c0 => if c0 =? 24 then art_enq_cls newb cl24 else g_cls FSG G c0)
     (fun c0 w0 => if newb && (c0 =? 24) && (w0 =? wb) then CBatch
                   else match k with FKP c w => if (c0 =? c) && (w0 =? w) then CQuar u n else g_st FSG G c0 w0 | FKS _ => g_st FSG G c0 w0 end)
     (match k with FKP _ _ => g_sec FSG G | FKS i => art_sec_quar i (g_sec FSG G) end)
     (g_sec_committed FSG G)
     (art_qt_add (g_qt FSG G) (spb + 24 * 2 ^ 32 + 16 * wb) (u - 16, n))
     (g_qg FSG G) kb true (g_fs FSG G).

Definition art_gs_drain {FSG : Type} (G : art_gs FSG) : art_gs FSG :=
  GS FSG (g_log FSG G) (g_inited FSG G) (g_cls FSG G) (g_st FSG G) (g_sec FSG G) (g_sec_committed FSG G)
     [] (g_qg FSG G ++ g_qt FSG G) (g_depot FSG G) (g_ia FSG G) (g_fs FSG G).

(* [comment removed for export] *)
Lemma art_lastb_snoc : forall bs b, art_lastb (bs ++ [b]) = b.
Proof. intros bs b. unfold art_lastb. apply last_last. Qed.

Lemma art_qt_split : forall qt, qt <> [] -> qt = removelast qt ++ [art_lastb qt].
Proof. intros qt H. unfold art_lastb. apply app_removelast_last. exact H. Qed.

Lemma art_free_newb_nil : art_free_newb [] = true.
Proof. reflexivity. Qed.

Lemma art_free_newb_false : forall qt, art_free_newb qt = false -> qt <> [] /\ Z.of_nat (length (bt_items (art_lastb qt))) <> 1021.
Proof.
  intros qt H. unfold art_free_newb, art_enq_newb in H. apply orb_false_iff in H. destruct H as (H1 & H2).
  apply Z.eqb_neq in H1, H2. split; [|exact H2]. intros ->. apply H1. reflexivity.
Qed.

Lemma art_bt_bytes_add : forall a its it, art_bt_bytes (BATCH a (its ++ [it])) = art_bt_bytes (BATCH a its) + snd it.
Proof. intros a its it. unfold art_bt_bytes. cbn [bt_items]. induction its as [|x r IH]; cbn [app fold_right]; lia. Qed.

Lemma art_batches_bytes_one : forall b, art_batches_bytes [b] = art_bt_bytes b.
Proof. intros b. unfold art_batches_bytes, art_bt_bytes. cbn [fold_right]. lia. Qed.

Lemma art_qt_add_bytes : forall qt b it,
  art_batches_bytes (art_qt_add qt b it) = art_batches_bytes qt + snd it + (if art_free_newb qt then 8192 else 0).
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite art_batches_bytes_app, art_batches_bytes_one. unfold art_bt_bytes. cbn [bt_items fold_right]. lia.
  - destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
    rewrite !art_batches_bytes_app, !art_batches_bytes_one. rewrite art_bt_bytes_add. unfold art_bt_bytes. cbn [bt_items]. lia.
Qed.

Lemma art_qt_add_nq : forall qt b it, art_nq (art_qt_add qt b it) = art_nq qt + 1 + (if art_free_newb qt then 1 else 0).
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite art_nq_app. cbn [art_nq fold_right bt_items length]. lia.
  - destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc. rewrite !art_nq_app.
    cbn [art_nq fold_right bt_items]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma art_qt_add_length : forall qt b it, Z.of_nat (length (art_qt_add qt b it)) = Z.of_nat (length qt) + (if art_free_newb qt then 1 else 0).
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite length_app. cbn [length]. lia.
  - destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last. rewrite !length_app. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Section Open.
Variable FSG : Type.
Definition art_rt_quar_b (bound : Z) (rn : art_run) (G : art_gs FSG) (M : word -> option byte) : Prop :=
  (exists f l, cellA M (rn_t rn + 80) 8 (Z.of_nat (length (g_qt FSG G))) /\ cellA M (rn_t rn + 88) 8 f /\ cellA M (rn_t rn + 96) 8 l
               /\ cellA M (rn_t rn + 104) 8 (art_batches_bytes (g_qt FSG G)) /\ art_batch_list M (g_qt FSG G) f l)
  /\ (exists f l, cellA M (0x13c8b0 + 160) 8 (Z.of_nat (length (g_qg FSG G))) /\ cellA M (0x13c8b0 + 168) 8 f /\ cellA M (0x13c8b0 + 176) 8 l
               /\ cellA M (0x13c8b0 + 184) 8 (art_batches_bytes (g_qg FSG G)) /\ art_batch_list M (g_qg FSG G) f l)
  /\ art_batches_bytes (g_qt FSG G) <= bound /\ art_batches_bytes (g_qg FSG G) <= 2 ^ 28
  /\ cellA M (0x13c8b0 + 152) 4 0
  /\ NoDup (map bt_addr (g_qt FSG G ++ g_qg FSG G))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) -> bt_items b <> [])
  /\ (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) ->
        (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CQuar (fst it + 16) (snd it))
        \/ (exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
  /\ NoDup (map fst (flat_map bt_items (g_qt FSG G ++ g_qg FSG G)))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) ->
        exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CBatch).
Definition art_alloc_rep_b (bound : Z) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary FSG rn G M /\ art_rt_chunks FSG rn G LB M
  /\ art_rt_sec FSG rn G LB M /\ art_rt_quar_b bound rn G M /\ art_rt_depot FSG rn G M /\ art_rt_ia FSG G M /\ art_rt_blocks FSG rn G LB
  /\ art_rt_ghost FSG rn G M.

#[using="Type"] Lemma art_alloc_rep_b_closed : forall rn G LB M, art_alloc_rep_b (2 ^ 20) rn G LB M = art_alloc_rep FSG rn G LB M.
Proof. reflexivity. Qed.
#[using="Type"] Lemma art_alloc_rep_b_ghost : forall b rn G LB M, art_alloc_rep_b b rn G LB M -> art_rt_ghost FSG rn G M.
Proof. intros b rn G LB M (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GH). exact GH. Qed.
#[using="Type"] Lemma art_alloc_rep_b_mono : forall b b' rn G LB M, b <= b' -> art_alloc_rep_b b rn G LB M -> art_alloc_rep_b b' rn G LB M.
Proof.
  intros b b' rn G LB M Hb (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7). split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
  split; [|exact R7]. destruct R6 as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [exact Q2|]. split; [lia|exact Q4].
Qed.
End Open.

(* [comment removed for export] *)
Lemma art_qt_add_flat : forall qt b it, flat_map bt_items (art_qt_add qt b it) = flat_map bt_items qt ++ [it].
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite flat_map_app. cbn [flat_map bt_items app]. rewrite ?app_nil_r. reflexivity.
  - destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
    rewrite !flat_map_app. cbn [flat_map bt_items]. rewrite ?app_nil_r. rewrite app_assoc. reflexivity.
Qed.

Lemma art_qt_add_addrs : forall qt b it, map bt_addr (art_qt_add qt b it) = map bt_addr qt ++ (if art_free_newb qt then [b] else []).
Proof.
  intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - rewrite map_app. reflexivity.
  - destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
    rewrite !map_app. cbn [map bt_addr]. rewrite app_nil_r. reflexivity.
Qed.

Lemma art_qt_add_in : forall qt b it b0, In b0 (art_qt_add qt b it) ->
  (art_free_newb qt = true /\ b0 = BATCH b [it]) \/ In b0 qt
  \/ (art_free_newb qt = false /\ qt <> [] /\ b0 = BATCH (bt_addr (art_lastb qt)) (bt_items (art_lastb qt) ++ [it])).
Proof.
  intros qt b it b0 H. unfold art_qt_add in H. destruct (art_free_newb qt) eqn:E.
  - apply in_app_or in H. destruct H as [H|[H|[]]]; [right; left; exact H|left; split; [reflexivity|symmetry; exact H]].
  - destruct (art_free_newb_false qt E) as (NE & _). apply in_app_or in H. destruct H as [H|[H|[]]].
    + right; left. rewrite (art_qt_split qt NE). apply in_or_app. left. exact H.
    + right; right. split; [reflexivity|]. split; [exact NE|symmetry; exact H].
Qed.

Lemma art_qt_add_keep : forall qt b it b0, In b0 qt -> exists b0', In b0' (art_qt_add qt b it) /\ bt_addr b0' = bt_addr b0 /\ incl (bt_items b0) (bt_items b0').
Proof.
  intros qt b it b0 H. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
  - exists b0. split; [apply in_or_app; left; exact H|]. split; [reflexivity|apply incl_refl].
  - destruct (art_free_newb_false qt E) as (NE & _). rewrite (art_qt_split qt NE) in H. apply in_app_or in H. destruct H as [H|[H|[]]].
    + exists b0. split; [apply in_or_app; left; exact H|]. split; [reflexivity|apply incl_refl].
    + subst b0. eexists. split; [apply in_or_app; right; left; reflexivity|]. cbn [bt_addr bt_items]. split; [reflexivity|apply incl_appl, incl_refl].
Qed.

Lemma art_in_batches_add : forall qt qg b it h m, art_in_batches (qt ++ qg) h m -> art_in_batches (art_qt_add qt b it ++ qg) h m.
Proof.
  intros qt qg b it h m (b0 & Hb0 & Hi). apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0].
  - destruct (art_qt_add_keep qt b it b0 Hb0) as (b0' & H1 & _ & H3). exists b0'. split; [apply in_or_app; left; exact H1|apply H3; exact Hi].
  - exists b0. split; [apply in_or_app; right; exact Hb0|exact Hi].
Qed.

Lemma art_in_batches_new : forall qt qg b it, art_in_batches (art_qt_add qt b it ++ qg) (fst it) (snd it).
Proof.
  intros qt qg b it. unfold art_in_batches, art_qt_add. destruct (art_free_newb qt) eqn:E.
  - exists (BATCH b [it]). split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|]. cbn [bt_items]. left. destruct it; reflexivity.
  - eexists. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|]. cbn [bt_items]. apply in_or_app. right. left. destruct it; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_batch_list_last : forall M bs f l, bs <> [] -> art_batch_list M bs f l -> l = bt_addr (art_lastb bs).
Proof.
  intros M bs. induction bs as [|x r IH]; intros f l NE BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & LK & R).
  destruct r as [|y r']; [destruct LK as (El & _); exact El|]. unfold art_lastb. change (last (x :: y :: r') (BATCH 0 [])) with (last (y :: r') (BATCH 0 [])).
  apply (IH (bt_addr y) l); [discriminate|exact R].
Qed.

Lemma art_nth_error_lt : forall (A : Type) (l : list A) j x, nth_error l j = Some x -> (j < length l)%nat.
Proof. intros A l j x H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma art_batch_list_snoc : forall M M' bs f l bn,
  bs <> [] -> NoDup (map bt_addr bs) -> art_batch_list M bs f l ->
  (forall b0, In b0 bs -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64) ->
  (forall b0 (x : word), In b0 bs -> bt_addr b0 <= U x < bt_addr b0 + 8192 -> ~ (bt_addr b0 = l /\ U x < l + 8) -> M' x = M x) ->
  cellA M' l 8 (bt_addr bn) -> art_batch_list M' [bn] (bt_addr bn) (bt_addr bn) ->
  art_batch_list M' (bs ++ [bn]) f (bt_addr bn).
Proof.
  intros M M' bs. induction bs as [|x r IH]; intros f l bn NE ND BL RNG EQ CL BN; [contradiction|].
  cbn [art_batch_list] in BL. destruct BL as (Ef & Hl & C1 & C2 & CI & LK & R).
  destruct (RNG x (or_introl eq_refl)) as (R0 & R1).
  assert (TX : forall a (j : nat) v, bt_addr x + 8 <= a -> a + Z.of_nat j <= bt_addr x + 8192 -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hj C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros y Hy. apply (EQ x y (or_introl eq_refl)); [lia|]. intros (E & Y). lia. }
  assert (TI : forall j it, nth_error (bt_items x) j = Some it -> cellA M' (bt_addr x + 24 + 8 * Z.of_nat j) 8 (fst it)).
  { intros j it Hj. pose proof (art_nth_error_lt _ _ _ _ Hj) as Hlt. apply TX; [lia|cbn; lia|exact (CI j it Hj)]. }
  destruct r as [|y r'].
  - destruct LK as (El & C0). cbn [app art_batch_list]. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|]. split; [apply TX; [lia|cbn; lia|exact C2]|].
    split; [exact TI|]. split; [rewrite <- El; exact CL|]. exact BN.
  - assert (El : l = bt_addr (art_lastb (y :: r'))) by (apply (art_batch_list_last M (y :: r') (bt_addr y) l); [discriminate|exact R]).
    assert (Nx : bt_addr x <> l).
    { rewrite El. intros E. cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. apply Hni. apply list_elem_of_In. rewrite E. change (bt_addr y :: map bt_addr r') with (map bt_addr (y :: r')). apply in_map. unfold art_lastb. apply BatFxQ_b.art_last_in. discriminate. }
    change ((x :: y :: r') ++ [bn]) with (x :: y :: (r' ++ [bn])). cbn [art_batch_list]. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|].
    split; [apply TX; [lia|cbn; lia|exact C2]|]. split; [exact TI|].
    split. { apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact LK]. intros z Hz. apply (EQ x z (or_introl eq_refl)); [cbn in Hz; lia|]. intros (E & _). exact (Nx E). }
    change (y :: (r' ++ [bn])) with ((y :: r') ++ [bn]). apply (IH (bt_addr y) l bn); [discriminate| | exact R | | | exact CL | exact BN].
    + cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. exact HND.
    + intros b0 Hb0. apply RNG. right. exact Hb0.
    + intros b0 z Hb0. apply EQ. right. exact Hb0.
Qed.

Lemma art_batch_list_upd_last : forall M M' r lb lb' f l,
  art_batch_list M (r ++ [lb]) f l -> bt_addr lb' = bt_addr lb ->
  (forall b0, In b0 (r ++ [lb]) -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64) ->
  (forall b0 (x : word), In b0 r -> bt_addr b0 <= U x < bt_addr b0 + 8192 -> M' x = M x) ->
  (forall x : word, bt_addr lb <= U x < bt_addr lb + 8 -> M' x = M x) ->
  (length (bt_items lb') <= 1021)%nat ->
  cellA M' (bt_addr lb' + 16) 8 (Z.of_nat (length (bt_items lb'))) -> cellA M' (bt_addr lb' + 8) 8 (8192 + fold_right (fun it z => snd it + z) 0 (bt_items lb')) ->
  (forall j it, nth_error (bt_items lb') j = Some it -> cellA M' (bt_addr lb' + 24 + 8 * Z.of_nat j) 8 (fst it)) ->
  art_batch_list M' (r ++ [lb']) f l.
Proof.
  intros M M' r. induction r as [|x r IH]; intros lb lb' f l BL Ea RNG EQ EQL Hl' C1' C2' CI'.
  - cbn [app art_batch_list] in BL |- *. destruct BL as (Ef & _ & _ & _ & _ & (El & C0) & _). destruct (RNG lb (or_introl eq_refl)) as (R0 & R1).
    split; [rewrite Ea; exact Ef|]. split; [exact Hl'|]. split; [exact C1'|]. split; [exact C2'|]. split; [exact CI'|].
    split; [|reflexivity]. split; [rewrite Ea; exact El|]. rewrite Ea. apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact C0]. intros z Hz. apply EQL. cbn in Hz. lia.
  - change ((x :: r) ++ [lb]) with (x :: (r ++ [lb])) in BL. change ((x :: r) ++ [lb']) with (x :: (r ++ [lb'])).
    cbn [art_batch_list] in BL |- *. destruct BL as (Ef & Hl & C1 & C2 & CI & LK & R).
    destruct (RNG x (or_introl eq_refl)) as (R0 & R1).
    assert (TX : forall a (j : nat) v, bt_addr x <= a -> a + Z.of_nat j <= bt_addr x + 8192 -> cellA M a j v -> cellA M' a j v).
    { intros a j v Ha Hj C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros y Hy. apply (EQ x y (or_introl eq_refl)). lia. }
    split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|]. split; [apply TX; [lia|cbn; lia|exact C2]|].
    split. { intros j it Hj. pose proof (art_nth_error_lt _ _ _ _ Hj) as Hlt. apply TX; [lia|cbn; lia|exact (CI j it Hj)]. }
    assert (Hd : match r ++ [lb'] with [] => 0 | b' :: _ => bt_addr b' end = match r ++ [lb] with [] => 0 | b' :: _ => bt_addr b' end).
    { destruct r as [|y r']; cbn [app]; [exact Ea|reflexivity]. }
    split.
    { destruct (r ++ [lb]) as [|y0 t0] eqn:E0; [destruct r; discriminate|]. destruct (r ++ [lb']) as [|y1 t1] eqn:E1; [destruct r; discriminate|].
      cbn in Hd. rewrite Hd. apply TX; [lia|cbn; lia|exact LK]. }
    rewrite Hd. apply (IH lb lb' _ l R Ea); [intros b0 Hb0; apply RNG; right; exact Hb0|intros b0 z Hb0; apply EQ; right; exact Hb0|exact EQL|exact Hl'|exact C1'|exact C2'|exact CI'].
Qed.

(* [comment removed for export] *)
Lemma art_sec_quar_length : forall i l, length (art_sec_quar i l) = length l.
Proof. induction i as [|i IH]; intros [|s r]; cbn [art_sec_quar length]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma art_sec_quar_nth_same : forall i l s, nth_error l i = Some s ->
  nth_error (art_sec_quar i l) i = Some (SEC (sc_map s) (sc_msize s) (sc_u s) (sc_n s) true).
Proof. induction i as [|i IH]; intros [|s0 r] s H; cbn [nth_error art_sec_quar] in *; try discriminate. - injection H as ->. reflexivity. - apply IH. exact H. Qed.

Lemma art_sec_quar_nth_other : forall i l j, j <> i -> nth_error (art_sec_quar i l) j = nth_error l j.
Proof.
  induction i as [|i IH]; intros [|s0 r] j N; cbn [art_sec_quar]; try reflexivity.
  - destruct j as [|j]; [contradiction|reflexivity].
  - destruct j as [|j]; [reflexivity|]. cbn [nth_error]. apply IH. intros ->. apply N. reflexivity.
Qed.

Lemma art_sec_quar_in_other : forall i l si s, nth_error l i = Some si -> In s l -> sc_u s <> sc_u si -> In s (art_sec_quar i l).
Proof.
  induction i as [|i IH]; intros [|s0 r] si s H Hs N; cbn [nth_error art_sec_quar] in *; try discriminate.
  - injection H as ->. destruct Hs as [->|Hs]; [contradiction|right; exact Hs].
  - destruct Hs as [->|Hs]; [left; reflexivity|right; exact (IH r si s H Hs N)].
Qed.

Lemma art_sec_quar_in : forall i l s', In s' (art_sec_quar i l) ->
  In s' l \/ (exists s, nth_error l i = Some s /\ s' = SEC (sc_map s) (sc_msize s) (sc_u s) (sc_n s) true).
Proof.
  induction i as [|i IH]; intros [|s0 r] s' H; cbn [art_sec_quar] in H; try contradiction.
  - destruct H as [<-|H]; [right; exists s0; split; reflexivity|left; right; exact H].
  - destruct H as [<-|H]; [left; left; reflexivity|]. destruct (IH r s' H) as [X|(s & X1 & X2)]; [left; right; exact X|right; exists s; split; assumption].
Qed.
