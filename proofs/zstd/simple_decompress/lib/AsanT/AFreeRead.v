(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes AQConst ARep ARepQ ARepQP ARepFrame ARepKit ALayout AHeapP
     AModelFacts AFreeModel AFreeRep AFreeGeo F_afree_tail F_afree_icpt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enq_is_app (st : astate) : bool :=
  match rev (a_qloc st) with b :: _ => negb (b_count b =? Q_BATCH) | [] => false end.

Lemma enq_is_app_spec : forall st1 ch,
  (enq_is_app st1 = true <-> exists s, enq_app st1 ch = Some s).
Proof.
  intros st1 ch. unfold enq_is_app, enq_app. destruct (rev (a_qloc st1)) as [|b rl]; [split; [discriminate| intros [s H]; discriminate]|].
  destruct (Z.eqb_spec (b_count b) Q_BATCH); cbn; split.
  - discriminate.
  - intros [s H]; discriminate.
  - intros _; eexists; reflexivity.
  - reflexivity.
Qed.

Definition dummy_batch : abatch := mkABatch 0 0 [].
Definition dummy_qb : qbatchc := mkQB 0 [].

Definition ek_of (L : alayout) (st : astate) (X : aconc) (Q : qconc) (n k24 : Z) (stj : word) (chunks : list word) : enq_kind :=
  let cnt24 := c_count (get_cls st K_BATCH_CLASS) in
  let maxc := Z_to_bv 64 (max_count st K_BATCH_CLASS) in
  let csz := Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0) in
  let bl := List.last (a_qloc st) dummy_batch in
  let qz := List.last (q_loc Q) dummy_qb in
  let hs := map (Z_to_bv 64) (qhdrs L (b_chunks bl) (qb_ks qz)) in
  if enq_is_app st then EkAppend 0 (b_size bl) (b_count bl) hs cnt24 maxc csz stj
  else EkNew (match a_qloc st with [] => false | _ => true end) 0 (b_size bl) cnt24 maxc csz stj
             (Z_to_bv 64 (acompact K_BATCH_CLASS k24)) chunks (al_space_beg L) (abatch_addr L k24) hs.

Definition g_of (L : alayout) (st : astate) (Q : qconc) (delta : Z) : gqd :=
  mkGQ (Q_CACHE <? a_qloc_bytes st + delta) (match a_qglob st with [] => false | _ => true end)
       (Z.of_nat (length (a_qglob st))) (qfirst L (q_glob Q)) (qlast L (q_glob Q)) (a_qglob_bytes st) 0.

Definition fhm (L : alayout) (c k n : Z) : Z := aslot_addr L c k + rz_size n - 16.

(* [comment removed for export] *)
Lemma st_enq_bytes : forall st p ch L X Q k24 stj chunks,
  let st1 := set_live (delete p (a_live st)) st in
  (enq_app st1 ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  a_qloc_bytes (st_enq st1 ch) = a_qloc_bytes st + ek_delta (ek_of L st X Q (chunk_size ch) k24 stj chunks) (chunk_size ch)
  /\ a_qglob_bytes (st_enq st1 ch) = a_qglob_bytes st /\ a_qglob (st_enq st1 ch) = a_qglob st.
Proof.
  intros st p ch L X Q k24 stj chunks st1 CNT. unfold ek_of. cbv zeta.
  assert (EQ : enq_is_app st = enq_is_app st1) by reflexivity. rewrite EQ.
  unfold st_enq. destruct (enq_app st1 ch) as [s|] eqn:EA.
  - replace (enq_is_app st1) with true by (symmetry; apply (enq_is_app_spec st1 ch); eexists; exact EA). cbn [ek_delta].
    destruct (enq_app_Some st1 ch s EA) as (l & bl & QL & NF & ->). subst st1. cbn [a_qloc_bytes a_qglob_bytes a_qglob set_live set_qloc]. repeat split; reflexivity.
  - destruct (enq_is_app st1) eqn:E2; [exfalso; destruct (proj1 (enq_is_app_spec st1 ch) E2) as [s Hs]; congruence|]. cbn [ek_delta].
    pose proof (enq_new_core ch st1) as (_ & G1 & G2 & _ & _ & L2 & _). rewrite G1, G2, L2. subst st1. cbn [a_qloc_bytes a_qglob_bytes a_qglob set_live].
    unfold Q_BATCH_BYTES. repeat split; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Batches.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

Lemma K24 : 1 <= K_BATCH_CLASS < K_NUM_CLASSES. Proof. unfold K_BATCH_CLASS, K_NUM_CLASSES; lia. Qed.

Lemma bslot_busy : forall q, In q (q_loc Q ++ q_glob Q) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof. intros q Hq. exact (qcoupled_bslot_busy L st X Q q CP Hq). Qed.

Lemma bslot_range : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= qb_slot q < ndist st K_BATCH_CLASS.
Proof.
  intros q Hq. destruct (bslot_busy q Hq) as (b & Hb & Sb & Cb & Kb).
  destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
  apply RANGE. apply in_or_app. right. apply in_or_app. right. unfold busy_slots. rewrite <- Kb. apply in_map. apply List.filter_In.
  split; [exact Hb| rewrite Cb; apply Z.eqb_refl].
Qed.

(* [comment removed for export] *)
Lemma bslot_geo : forall kk, 0 <= kk < ndist st K_BATCH_CLASS ->
     0x10007fff8000 <= abatch_addr L kk /\ abatch_addr L kk + 8192 <= ATOP /\ abatch_addr L kk mod 16 = 0
  /\ (al_t L + 4096 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= al_t L)
  /\ (al_nodes L + 1048576 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= al_nodes L)
  /\ (al_store L + 8388608 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= al_store L)
  /\ (forall RNG, arng L RNG st -> rng RNG (abatch_addr L kk) 8192).
Proof.
  intros kk KK. unfold abatch_addr.
  pose proof (slot_geo L st X K_BATCH_CLASS kk ALO WF K24 KK) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (slot_sep_objects L st X K_BATCH_CLASS kk ALO WF K24 KK) as (D1 & D2 & D3 & D4 & D5).
  rewrite size_of_class_24 in *.
  repeat (split; [assumption|]). intros RNG AR. pose proof (proj1 (slot_rng L st X K_BATCH_CLASS kk ALO WF K24 KK RNG AR)) as R.
  rewrite size_of_class_24 in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma bslots_nodup_split : forall qs1 qa qs2 qb qs3,
  q_loc Q ++ q_glob Q = qs1 ++ qa :: qs2 ++ qb :: qs3 -> qb_slot qa <> qb_slot qb.
Proof.
  intros qs1 qa qs2 qb qs3 E NE. destruct CP as (_ & _ & _ & _ & ND2 & _). rewrite E, !map_app in ND2. cbn [map] in ND2.
  apply NoDup_mid in ND2. destruct ND2 as [NI _]. apply NI. apply in_or_app. right. rewrite map_app. apply in_or_app. right. left. symmetry. exact NE.
Qed.
End Batches.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma length_block_shadow_bytes : forall n, 0 <= n -> length (block_shadow_bytes n) = Z.to_nat (granules n).
Proof.
  intros n Hn. unfold block_shadow_bytes. rewrite length_app, repeat_length, (granules_eq n Hn), shlen_floor.
  pose proof (shlen_nonneg n Hn). destruct (n mod 8 =? 0); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma cb_split3_gen : forall m A n1 n2 n3 (bs1 bs2 bs3 : list byte),
  length bs1 = n1 -> length bs2 = n2 -> length bs3 = n3 ->
  rw_cells bsegs m A [CB (n1 + n2 + n3)%nat (bs1 ++ bs2 ++ bs3)] ->
  rw_cells bsegs m A [CB n1 bs1] /\ rw_cells bsegs m (A + Z.of_nat n1) [CB n2 bs2] /\ rw_cells bsegs m (A + Z.of_nat n1 + Z.of_nat n2) [CB n3 bs3].
Proof.
  intros m A n1 n2 n3 bs1 bs2 bs3 L1 L2 L3 H.
  pose proof (rw_cells_split_CB bsegs m A [] _ _ [] [n1; n2; n3]%nat H ltac:(cbn; lia)) as SP. cbn [app mk_CB_cells] in SP.
  rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in SP by lia.
  rewrite skipn_app, L1, Nat.sub_diag, skipn_O, skipn_all2 in SP by lia. cbn [app] in SP.
  rewrite firstn_app, L2, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in SP by lia.
  rewrite skipn_app, L2, Nat.sub_diag, skipn_O, skipn_all2 in SP by lia. cbn [app] in SP.
  rewrite firstn_all2 in SP by lia.
  change [CB n1 bs1; CB n2 bs2; CB n3 bs3] with ([CB n1 bs1] ++ [CB n2 bs2] ++ [CB n3 bs3]) in SP.
  apply rw_cells_app in SP. destruct SP as [H1 SP]. apply rw_cells_app in SP. destruct SP as [H2 H3].
  cbn [cells_size csize] in H2, H3. rewrite !Nat.add_0_r in H2. rewrite !Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (m : amem) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis XB : x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2.
Hypothesis CLS : aslots L st X m c /\ aslot_shadow L st X m c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.

Lemma freed_range : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof.
  pose proof (quar_class L st X p c k n b1 ctx l1 l2 XB WF) as HC. split; [exact HC|].
  destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
  apply RANGE. apply in_or_app. right. apply in_or_app. right.
  rewrite (busy_slots_split X p c k n b1 ctx l1 l2 XB), Z.eqb_refl. apply in_or_app. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_chunk :
     rw_cells bsegs m (UB - 16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ (exists uw : word, rw_cells bsegs m UB [C8 uw]) /\ junk_at m (UB + 8) (S - rz_size n - 8)
  /\ (16 < rz_size n -> rw_cells bsegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz_size n - 32))
  /\ rw_cells bsegs m (shad AB) [CB (Z.to_nat (shlen (rz_size n))) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n))))]
  /\ rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ rw_cells bsegs m (shad UB + shlen (rup n 8)) [CB (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8)))
                                                      (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))].
Proof.
  destruct freed_range as [HC KR]. destruct CLS as [[SL _] [SH _]].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bfreed bstate_byte xb_alloc xb_slot] in SL.
  destruct SL as (LH & [stb [E HDR]] & UJ). injection E as <-.
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S8).
  destruct (junk_split m _ 8 (S - rz_size n - 8) ltac:(replace (8 + (S - rz_size n - 8)) with (S - rz_size n) by lia; exact UJ) ltac:(lia) ltac:(subst S; lia)) as [U8 UR].
  destruct (c8_of_junk m _ U8) as [uw HUW].
  subst S AB UB. replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exists uw; exact HUW|]. split; [exact UR|]. split; [exact LH|].
  (* [comment removed for export] *)
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & _).
  cbn [slot_shadow_bytes xb_n xb_st bfreed] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  assert (LB : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; exact (proj1 N0)).
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LB ltac:(apply repeat_length) SH) as (SHA & SHU & SHR).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR. rewrite <- GE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.
End Chunk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma last_app1 : forall {A} (l : list A) x d, List.last (l ++ [x]) d = x.
Proof. intros. apply last_last. Qed.

Section Variant.
(* [comment removed for export] *)
Variables (H : aholes) (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) (RNG : footprint)
          (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis ARNG : arng L RNG st.
Hypothesis AR : AREP H L st X m.
Hypothesis AQ : AQUAR_at L st X Q m.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis NBT : s0 <> BBatch.
Hypothesis N1 : 1 <= n.

Lemma WF : awf L st X. Proof. exact (proj1 AR). Qed.
Lemma CP : qcoupled L st X Q. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 AQ))))). Qed.
Lemma HCKR : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof. exact (any_range L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

(* [comment removed for export] *)
Lemma other_key : forall y, In y (x_busy X) -> xb_st y <> s0 -> c <> xb_class y \/ k <> xb_slot y.
Proof.
  intros y Hy Sy. apply (In_X_g X s0 c k n b1 ctx l1 l2 XB) in Hy. destruct Hy as [Hy| ->]; [| cbn in Sy; congruence].
  destruct (Z.eq_dec c (xb_class y)) as [E|NE]; [| left; exact NE]. right. intros K.
  exact (key_fresh_g L st X s0 c k n b1 ctx l1 l2 XB WF y Hy (eq_sym E) (eq_sym K)).
Qed.

(* [comment removed for export] *)
Lemma freed_vs_slot24 : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> (c <> K_BATCH_CLASS \/ k <> kk) ->
  fhm L c k n + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= fhm L c k n.
Proof.
  intros kk KK NE. destruct HCKR as [HC KR].
  pose proof (any_facts L st X s0 c k n b1 ctx l1 l2 XB WF NBT) as (N0 & FIT0 & _).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & G3 & G4 & _ & G6 & _ & _ & _ & _ & _ & G12 & _ & G14).
  pose proof (slots_sep_any L st X c k K_BATCH_CLASS kk ALO WF HC (K24) KR KK NE) as D.
  rewrite size_of_class_24 in D. unfold fhm, abatch_addr. generalize D G3 G4 G6 G12 G14. clear. intros. lia.
Qed.

(* [comment removed for export] *)
Lemma read_ek_app : forall stj chunks k24,
  enq_is_app st = true ->
  let ek := ek_of L st X Q n k24 stj chunks in
  forall (maxc csz : word) (cnt24 : Z),
  rw_cells bsegs m (al_t L + 2128) [C4 (Z_to_bv 64 (c_count (get_cls st K_BATCH_CLASS))); C4 (Z_to_bv 64 (max_count st K_BATCH_CLASS));
                                     C8 (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0))] ->
  rw_cells bsegs m (al_t L + 2784) [C8 stj] ->
     ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m
  /\ ek_seps ek L (fhm L c k n) (qlast L (q_loc Q))
  /\ ek_delta ek n = n /\ ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
  /\ (exists l bl ql qz, a_qloc st = l ++ [bl] /\ q_loc Q = ql ++ [qz] /\ length ql = length l /\ b_count bl <> Q_BATCH
        /\ ek = EkAppend 0 (b_size bl) (b_count bl) (map (Z_to_bv 64) (qhdrs L (b_chunks bl) (qb_ks qz)))
                        (c_count (get_cls st K_BATCH_CLASS)) (Z_to_bv 64 (max_count st K_BATCH_CLASS))
                        (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0)) stj).
Proof.
  intros stj chunks k24 EA ek maxc csz cnt24 CR STS. subst ek. unfold ek_of. rewrite EA. cbv zeta.
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & _).
  destruct AQ as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  (* [comment removed for export] *)
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
  assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
  destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
  set (l := rev rl) in *. set (bl := blr) in *.
  assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
  destruct (q_loc Q) as [|q0 qs0] eqn:QQ0; [cbn in LQ; lia|]. rewrite <- QQ0 in *.
  assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
  { apply app_removelast_last. rewrite QQ0. discriminate. }
  set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
  assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
  rewrite QL, last_app1.
  (* [comment removed for export] *)
  unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
  cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
  assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
  (* [comment removed for export] *)
  assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
  pose proof (bslot_range L st X Q WF CP qz INz) as KZ.
  pose proof (bslot_geo L st X ALO WF (qb_slot qz) KZ) as (B0 & B1 & BAL & BT & BN & BS & BR).
  destruct (bslot_busy L st X Q CP qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
  pose proof (freed_vs_slot24 (qb_slot qz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DH.
  (* [comment removed for export] *)
  assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
  pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
  assert (SZ2 : b_size bl <= a_qloc_bytes st).
  { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
  pose proof (any_facts L st X s0 c k n b1 ctx l1 l2 XB WF NBT) as (N0 & FIT0 & _).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _).
  rewrite QLST. unfold fhm in *.
  split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
  - (* [comment removed for export] *)
    cbn [ek_pre]. unfold Q_BATCH, Q_BATCH_BYTES, Q_CACHE in *.
    split; [rewrite ?QL, length_app; cbn; lia|]. split; [exact Z1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; rewrite Z4; lia|].
    split; [exact Z3|]. split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [generalize DH; clear; intros; lia|].
    split; [exact CR|]. split; [exact STS|]. apply BR. exact ARNG.
  - cbn [ek_seps]. split; [exact DH|]. split; [exact BN| exact BS].
  - exists l, bl, ql, qz. split; [first [exact QL| reflexivity]|]. split; [exact QQ|]. split; [exact LNl|]. split; [exact NFULL|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma max_count_24 : max_count st K_BATCH_CLASS <= 2.
Proof. unfold max_count, max_cached. rewrite size_of_class_24. change (1024 / 8192) with 0. destruct (a_cinit st); lia. Qed.

Lemma cnt24_le16 : c_count (get_cls st K_BATCH_CLASS) <= 16.
Proof.
  pose proof max_count_24 as MC. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia.
Qed.

Lemma read_ek_new : forall stj,
  enq_is_app st = false -> 0 < c_count (get_cls st K_BATCH_CLASS) ->
  rw_cells bsegs m (al_t L + 2784) [C8 stj] ->
  exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
     ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m
  /\ ek_seps ek L (fhm L c k n) (qlast L (q_loc Q))
  /\ ek_delta ek n = n + 8192 /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24
  /\ nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
  /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
  /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
  /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
  /\ a_cinit st = true
  /\ ((a_qloc st = [] /\ q_loc Q = [])
      \/ (exists l bl ql qz, a_qloc st = l ++ [bl] /\ q_loc Q = ql ++ [qz] /\ length ql = length l /\ b_count bl = Q_BATCH
            /\ qlast L (q_loc Q) = abatch_addr L (qb_slot qz) /\ 0 <= qb_slot qz < ndist st K_BATCH_CLASS /\ qb_slot qz <> k24))
  /\ ek = EkNew (match a_qloc st with [] => false | _ => true end) 0 (b_size (List.last (a_qloc st) dummy_batch))
               (c_count (get_cls st K_BATCH_CLASS)) (Z_to_bv 64 (max_count st K_BATCH_CLASS))
               (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0)) stj
               (Z_to_bv 64 (acompact K_BATCH_CLASS k24)) chunks (al_space_beg L) (abatch_addr L k24)
               (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))).
Proof.
  intros stj EA POS STS.
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  destruct (kit_cache_pop H L st X m K_BATCH_CLASS (c_count (get_cls st K_BATCH_CLASS)) AR K24 eq_refl POS)
    as (k24 & chunks & NK & NB & KK & CR & CH & LCH & NTH & JK & FSH).
  rewrite size_of_class_24 in JK, FSH.
  assert (CIN : a_cinit st = true).
  { pose proof max_count_24 as MC. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
    destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _).
    unfold max_count in CNTB |- *. destruct (a_cinit st); [reflexivity| exfalso; lia]. }
  exists k24, chunks. cbv zeta. unfold ek_of. rewrite EA. cbv zeta.
  (* [comment removed for export] *)
  assert (NIB : ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))).
  { intros Hin. apply (BS k24) in Hin. destruct Hin as (y & Hy & Sy & Cy & Ky).
    enough (E : busy_of X K_BATCH_CLASS k24 <> None) by (apply E; exact NB).
    intros E. unfold busy_of in E. destruct (List.find _ _) eqn:FE; [discriminate|].
    apply (List.find_none _ _ FE) in Hy. rewrite Cy, Ky, !Z.eqb_refl in Hy. discriminate. }
  (* [comment removed for export] *)
  pose proof (bslot_geo L st X ALO WF k24 KK) as (B0 & B1 & BAL & BT & BN & BSR & BR).
  pose proof (freed_vs_slot24 k24 KK ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE];
      intros ->; pose proof (busy_of_X_self_g L st X s0 K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E; rewrite NB in E; discriminate)) as DHB.
  pose proof (any_facts L st X s0 c k n b1 ctx l1 l2 XB WF NBT) as (N0 & FIT0 & _).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & _ & _ & G5 & _ & _ & _ & G9 & _).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  destruct AR as (_ & _ & INST & _). destruct INST as (I32 & _).
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH by (unfold acache_addr, K_BATCH_CLASS; lia).
  replace (al_t L + 2128 + 16) with (al_t L + 2128 + 16) in CH by lia.
  assert (IXS : bv_unsigned (Z_to_bv 64 (acompact K_BATCH_CLASS k24)) = k24 * 512 /\ k24 * 512 < 2^32).
  { unfold acompact. rewrite size_of_class_24. change (8192 / 16) with 512.
    assert (KB : k24 < 2^19).
    { pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF K24 KK) as (_ & _ & _ & SG1 & SG2 & SG3 & SG4 & _).
      rewrite size_of_class_24 in SG2. unfold aslot_addr, K_FREEARR_OFF in *. rewrite size_of_class_24 in SG2. generalize SG1 SG2 SG3 SG4 KK. clear. intros. nia. }
    rewrite unsigned_lit by lia. lia. }
  destruct IXS as [IX1 IX2].
  assert (HBq : abatch_addr L k24 = al_space_beg L + 24 * 2 ^ 32 + 16 * bv_unsigned (Z_to_bv 64 (acompact K_BATCH_CLASS k24))).
  { rewrite IX1. unfold abatch_addr, aslot_addr, aregion. rewrite size_of_class_24. unfold K_REGION, K_BATCH_CLASS. lia. }
  (* [comment removed for export] *)
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (a_qloc st) as [|b0 bs0] eqn:QL0.
  - (* [comment removed for export] *)
    assert (QQ0 : q_loc Q = []) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]).
    rewrite QQ0. cbn [qlast last qaddrs map List.last b_chunks qb_ks qhdrs dummy_batch dummy_qb b_size length Z.of_nat].
    unfold fhm in *.
    split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
    + cbn [ek_pre]. atop_facts. rewrite CIN.
      split; [split; reflexivity|]. split; [exact I32|]. split; [rewrite ?CIN in CR; exact CR|]. split; [exact CH|]. split; [exact LCH|].
      split; [split; [exact POS| exact cnt24_le16]|]. split; [exact NTH|]. split; [lia|]. split; [exact STS|].
      split; [exact HBq|]. split; [exact JK|]. split; [lia|]. split; [exact B0|]. split; [exact B1|].
      split; [exact BT|]. split; [generalize (proj1 (alayout_t L ALO)); clear; intros; lia|]. split; [lia|].
      split; [generalize DHB; clear; intros; lia|]. split; [lia|]. apply BR. exact ARNG.
    + cbn [ek_seps]. split; [exact DHB|]. split; [exact BN|]. split; [exact BSR|]. intros; discriminate.
    + split; [exact NK|]. split; [exact NB|]. split; [exact KK|]. split; [rewrite QQ0 in NIB; exact NIB|]. split; [exact JK|]. split; [exact FSH|].
      split; [exact CIN|]. split; [left; split; [reflexivity| first [exact QQ0| reflexivity]]|]. rewrite CIN. reflexivity.
  - (* [comment removed for export] *)
    rewrite <- QL0 in *.
    destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [exfalso; rewrite <- (rev_involutive (a_qloc st)), RV in QL0; discriminate|].
    assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
    destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [FULL|]; [| discriminate]. clear EA0.
    set (l := rev rl) in *. set (bl := blr) in *.
    assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
    assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_loc Q); [cbn in LQ; lia| discriminate]. }
    set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
    assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
    unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
    assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
    assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WF CP qz INz) as KZ.
    pose proof (bslot_geo L st X ALO WF (qb_slot qz) KZ) as (Z0' & Z1' & ZAL & ZT & ZN & ZS & ZR).
    destruct (bslot_busy L st X Q CP qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (freed_vs_slot24 (qb_slot qz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DHL.
    assert (NEz : qb_slot qz <> k24) by (intros E; apply NIB; rewrite <- E; apply in_map; exact INz).
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot qz) k24 ltac:(lia) ltac:(lia) NEz ltac:(rewrite size_of_class_24; lia)) as DBL.
    rewrite size_of_class_24 in DBL.
    assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
    pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
    assert (SZ2 : b_size bl <= a_qloc_bytes st).
    { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
    assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1).
    rewrite QLST, !LST. fold qz. unfold fhm in *.
    split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
    + cbn [ek_pre]. unfold Q_CACHE, Q_BATCH, Q_BATCH_BYTES in *. rewrite CIN.
      split.
      { split; [rewrite QL, length_app; cbn; lia|]. split; [rewrite <- FULL; exact Z1|]. split; [lia|]. split; [lia|]. split; [exact Z0'|]. split; [exact Z1'|].
        split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; apply Nat2Z.inj; rewrite <- Z4, FULL; reflexivity|]. apply ZR. exact ARNG. }
      split; [exact I32|]. split; [rewrite ?CIN in CR; exact CR|]. split; [exact CH|]. split; [exact LCH|].
      split; [split; [exact POS| exact cnt24_le16]|]. split; [exact NTH|]. split; [lia|]. split; [exact STS|].
      split; [exact HBq|]. split; [exact JK|]. split; [lia|]. split; [exact B0|]. split; [exact B1|].
      split; [exact BT|]. split; [clear -ZT; lia|]. split; [generalize DBL; clear; unfold abatch_addr; intros; lia|].
      split; [generalize DHB; clear; intros; lia|]. split; [generalize DHL; clear; intros; lia|]. apply BR. exact ARNG.
    + cbn [ek_seps]. split; [exact DHB|]. split; [exact BN|]. split; [exact BSR|]. intros _. split; [exact DHL|]. split; [exact ZN| exact ZS].
    + split; [exact NK|]. split; [exact NB|]. split; [exact KK|]. split; [exact NIB|]. split; [exact JK|]. split; [exact FSH|]. split; [exact CIN|].
      split; [right; exists l, bl, ql, qz; repeat (split; [first [assumption| reflexivity]|]); exact NEz|].
      rewrite CIN. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_last : enq_is_app st = false ->
  let lst := qlast L (q_loc Q) in
  let bl := List.last (a_qloc st) dummy_batch in
  let hs := map (Z_to_bv 64) (qhdrs L (b_chunks bl) (qb_ks (List.last (q_loc Q) dummy_qb))) in
     (if match a_qloc st with [] => false | _ :: _ => true end
      then 0 < Z.of_nat (length (a_qloc st))
           /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size bl)); C8 (Z_to_bv 64 1021)]
           /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           /\ 0 <= b_size bl < 2^64
      else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0)
  /\ (al_t L + 4096 <= lst \/ lst + 8192 <= al_t L \/ lst = 0) /\ (fhm L c k n + 24 <= lst \/ lst + 8192 <= fhm L c k n)   (* [comment removed for export] *)
  /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  /\ 0 <= lst < 2^64.
Proof.
  intros EA. cbv zeta.
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. unfold aobj in ON, OS.
  pose proof (any_facts L st X s0 c k n b1 ctx l1 l2 XB WF NBT) as (N0 & FIT0 & _).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & _ & _ & G5 & _ & _ & G8 & _).
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (a_qloc st) as [|b0 bs0] eqn:QL0.
  - assert (QQ0 : q_loc Q = []) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]).
    rewrite QQ0. cbn [qlast last qaddrs map length Z.of_nat]. unfold fhm in *.
    split; [split; reflexivity|]. generalize TL1 G5 ON OS. clear. intros. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. lia.   (* [comment removed for export] *)
  - rewrite <- QL0 in *.
    destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [exfalso; rewrite <- (rev_involutive (a_qloc st)), RV in QL0; discriminate|].
    assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
    destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [FULL|]; [| discriminate]. clear EA0.
    set (l := rev rl) in *. set (bl := blr) in *.
    assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
    assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_loc Q); [cbn in LQ; lia| discriminate]. }
    set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
    assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
    unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
    assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
    assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WF CP qz INz) as KZ.
    pose proof (bslot_geo L st X ALO WF (qb_slot qz) KZ) as (Z0' & Z1' & ZAL & ZT & ZN & ZS & ZR).
    destruct (bslot_busy L st X Q CP qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (freed_vs_slot24 (qb_slot qz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DHL.
    assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
    pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
    assert (SZ2 : b_size bl <= a_qloc_bytes st).
    { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
    assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1).
    rewrite QLST, !LST. fold qz. unfold fhm, Q_CACHE, Q_BATCH, Q_BATCH_BYTES in *.
    split.
    + split; [rewrite QL, length_app; cbn; lia|]. split; [rewrite <- FULL; exact Z1|]. split; [exact Z0'|]. split; [exact Z1'|].
      split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; apply Nat2Z.inj; rewrite <- Z4, FULL; reflexivity|].
      split; [apply ZR; exact ARNG| lia].
    + split; [clear -ZT; lia|]. split; [generalize DHL; clear; intros; lia|]. split; [exact ZN|]. split; [exact ZS| lia].
Qed.

(* [comment removed for export] *)
Lemma qfirst_cases : forall qs, qfirst L qs = 0 \/ exists q, In q qs /\ qfirst L qs = abatch_addr L (qb_slot q).
Proof. intros [|q qs]; [left; reflexivity| right; exists q; split; [left; reflexivity| reflexivity]]. Qed.
Lemma qlast_cases : forall qs, qlast L qs = 0 \/ exists q, In q qs /\ qlast L qs = abatch_addr L (qb_slot q).
Proof.
  intros qs. destruct qs as [|q0 qs0] eqn:E; [left; reflexivity| right]. rewrite <- E.
  assert (NE : qs <> []) by (subst; discriminate).
  exists (List.last qs dummy_qb). pose proof (app_removelast_last dummy_qb NE) as D. split.
  - rewrite D at 2. apply in_or_app. right. left. reflexivity.
  - rewrite D at 1. apply qlast_app1.
Qed.

Lemma read_dk : forall (eb delta : Z) (ek : enq_kind),
  0 <= delta ->
  (eb = qlast L (q_loc Q) \/ exists kk, eb = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))) ->
  (Q_CACHE < a_qloc_bytes st + delta -> a_qglob_bytes st + (a_qloc_bytes st + delta) <= Q_MAX) ->
  ek_b ek (qlast L (q_loc Q)) = eb ->
  let g := g_of L st Q delta in
     dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + delta) m
  /\ dk_seps g L (fhm L c k n)
  /\ g_lst g = qlast L (q_glob Q) /\ dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + delta then qlast L (q_glob Q) else qlast L (q_loc Q)).
Proof.
  intros eb delta ek D0 EB NOREC EKB g. subst g. unfold g_of. cbv beta iota zeta delta [dk_pre dk_seps g_drain g_full g_nb g_fst g_lst g_qb g_nx dk_glst].
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GC ABG] & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  apply Forall_app in NF. destruct NF as [NFl NFg].
  pose proof (batches_bytes_lb _ NFg) as GLB0. rewrite <- NB2 in GLB0.
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (GF64 : 0 <= qfirst L (q_glob Q) < 2^64).
  { destruct (qfirst_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  assert (GL64 : 0 <= qlast L (q_glob Q) < 2^64).
  { destruct (qlast_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (GFULL : a_qglob st <> [] ->
      0 < Z.of_nat (length (a_qglob st))
   /\ rw_cells bsegs m (qlast L (q_glob Q)) [C8 (Z_to_bv 64 0)]
   /\ 0x10007fff8000 <= qlast L (q_glob Q) /\ qlast L (q_glob Q) + 8192 <= ATOP
   /\ (al_t L + 4096 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_t L)
   /\ (fhm L c k n + 24 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= fhm L c k n)
   /\ (qlast L (q_loc Q) + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= qlast L (q_loc Q))
   /\ (eb + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= eb)
   /\ (al_nodes L + 1048576 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_nodes L)
   /\ (al_store L + 8388608 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_store L)
   /\ rng RNG (qlast L (q_glob Q)) 8192).
  { intros GNE.
    assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
    assert (LQ : (0 < length (q_glob Q))%nat) by (rewrite LN2; destruct (a_qglob st); [congruence| cbn; lia]).
    assert (QQ : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_glob Q); [cbn in LQ; lia| discriminate]. }
    set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
    set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
    assert (LNg : length qg = length lg) by (rewrite QQ, QG, !length_app in LN2; cbn in LN2; lia).
    unfold abatches in ABG. rewrite QG, QQ in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [_ ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & _) _].
    assert (QLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQ; apply qlast_app1). rewrite QLST.
    assert (INz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WF CP qgz INz) as KZ.
    pose proof (bslot_geo L st X ALO WF (qb_slot qgz) KZ) as (B0 & B1 & BAL & BT & BN & BSR & BR).
    destruct (bslot_busy L st X Q CP qgz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (freed_vs_slot24 (qb_slot qgz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DH.
    (* [comment removed for export] *)
    assert (DL : qlast L (q_loc Q) + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= qlast L (q_loc Q)).
    { destruct (qlast_cases (q_loc Q)) as [E0 |(q & Hq & Eq)]; [rewrite E0; left; lia| rewrite Eq].
      assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
      pose proof (bslot_range L st X Q WF CP q INq) as KQ.
      assert (NEq : qb_slot q <> qb_slot qgz).
      { apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ qg) qgz []). rewrite EQl, QQ. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
      pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q) (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    assert (DE : eb + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= eb).
    { destruct EB as [-> |(kk & -> & KK & NIK)]; [exact DL|].
      assert (NEq : kk <> qb_slot qgz) by (intros ->; apply NIK; apply in_map; exact INz).
      pose proof (slots_disjoint L K_BATCH_CLASS kk (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    split; [rewrite QG, length_app; cbn; lia|].
    split; [pose proof Z1 as Z1'; rw_split Z1' 1%nat ZN ZR; exact ZN|].
    split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [exact DH|]. split; [exact DL|]. split; [exact DE|].
    split; [exact BN|]. split; [exact BSR|]. apply BR. exact ARNG. }
  (* [comment removed for export] *)
  unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *.
  split; [| split; [| split; [reflexivity| reflexivity]]].
  - split; [exact MX|]. split; [exact GC|].
    split; [lia|]. split; [lia|]. split; [exact GF64|]. split; [exact GL64|].
    destruct (Z.ltb_spec 1048576 (a_qloc_bytes st + delta)) as [LT|GE]; [| lia].
    split; [exact LT|]. split; [lia|].
    destruct (a_qglob st) as [|bg lg0] eqn:QG0.
    + split; [reflexivity|]. assert (QQ0 : q_glob Q = []) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). rewrite QQ0. reflexivity.
    + rewrite <- QG0 in *. destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      rewrite EKB. unfold fhm in *.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [generalize F6; clear; intros; lia|].
      split; [exact F7|]. split; [exact F8|]. exact F11.
  - intros DR FU. destruct (a_qglob st) as [|bg lg0] eqn:QG0; [discriminate|]. rewrite <- QG0 in *.
    destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    unfold fhm in *. split; [generalize F6; clear; intros; lia|]. split; [exact F9| exact F10].
Qed.
End Variant.
End CANSEC1.
