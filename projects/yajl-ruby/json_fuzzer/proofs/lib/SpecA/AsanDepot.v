(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanRepFrame AsanBudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition kTabSizeLog : Z := 20.
Definition kTabSize : Z := 2^20.
Definition kNodesMap1 : Z := 2^15.
Definition kStoreBlockCount : Z := 0x1000.
Definition kDepotStaticBytes : Z := 0x440010.
Definition kStoreStaticBytes : Z := 0x10010.

Definition bucket_of (h : Z) : Z := h mod kTabSize.

(* [comment removed for export] *)
Fixpoint head_aux (hs : list Z) (i : Z) (b : Z) (acc : Z) : Z :=
  match hs with
  | [] => acc
  | h :: t => head_aux t (i + 1) b (if bucket_of h =? b then i else acc)
  end.
Definition bucket_head (hs : list Z) (b : Z) : Z := head_aux hs 1 b 0.
(* [comment removed for export] *)
Definition nth_hash (hs : list Z) (i : Z) : Z := nth (Z.to_nat (i - 1)) hs 0.
Definition node_link (hs : list Z) (i : Z) : Z := bucket_head (firstn (Z.to_nat (i - 1)) hs) (bucket_of (nth_hash hs i)).

(* [comment removed for export] *)
Fixpoint last_pos (f : Z -> bool) (l : list Z) : option nat :=
  match l with
  | [] => None
  | h :: t => match last_pos f t with Some p => Some (S p) | None => if f h then Some O else None end
  end.

Lemma last_pos_spec : forall f l,
  match last_pos f l with
  | Some p => (p < length l)%nat /\ f (nth p l 0) = true /\ forall q, (p < q < length l)%nat -> f (nth q l 0) = false
  | None => forall q, (q < length l)%nat -> f (nth q l 0) = false
  end.
Proof.
  induction l as [|h t IH]; cbn; [intros q Hq; lia|].
  destruct (last_pos f t) as [p|].
  - destruct IH as (A & B & C). split; [lia|]. split; [exact B|]. intros [|q] Hq; [lia|]. apply C. lia.
  - destruct (f h) eqn:Fh.
    + split; [lia|]. split; [exact Fh|]. intros [|q] Hq; [lia|]. apply IH. lia.
    + intros [|q] Hq; [exact Fh|]. apply IH. lia.
Qed.

Lemma head_aux_last : forall hs i0 b acc,
  head_aux hs i0 b acc = match last_pos (fun h => bucket_of h =? b) hs with Some p => i0 + Z.of_nat p | None => acc end.
Proof.
  induction hs as [|h t IH]; intros i0 b acc; cbn; [reflexivity|].
  rewrite IH. destruct (last_pos _ t) as [p|]; [lia|]. destruct (bucket_of h =? b); [lia| reflexivity].
Qed.

Lemma nth_firstn_lt : forall {X} (l : list X) n m d, (n < m)%nat -> nth n (firstn m l) d = nth n l d.
Proof.
  induction l as [|x l IH]; intros [|n] [|m] d H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma bucket_head_spec : forall hs b,
  let r := bucket_head hs b in
  0 <= r <= zlen hs
  /\ (0 < r -> bucket_of (nth_hash hs r) = b)
  /\ (forall j, 1 <= j <= zlen hs -> bucket_of (nth_hash hs j) = b -> j <= r).
Proof.
  intros hs b. unfold bucket_head. rewrite head_aux_last. pose proof (last_pos_spec (fun h => bucket_of h =? b) hs) as SP.
  unfold zlen, nth_hash. destruct (last_pos _ hs) as [p|].
  - destruct SP as (A & B & C). apply Z.eqb_eq in B. split; [lia|]. split.
    + intros _. replace (Z.to_nat (1 + Z.of_nat p - 1)) with p by lia. exact B.
    + intros j Hj Hb. destruct (Z_lt_le_dec (1 + Z.of_nat p) j); [|lia]. exfalso.
      specialize (C (Z.to_nat (j - 1)) ltac:(lia)). apply Z.eqb_neq in C. exact (C Hb).
  - split; [lia|]. split; [lia|]. intros j Hj Hb. exfalso. specialize (SP (Z.to_nat (j - 1)) ltac:(lia)). apply Z.eqb_neq in SP. exact (SP Hb).
Qed.

(* [comment removed for export] *)
Lemma node_link_spec : forall hs i, 1 <= i <= zlen hs ->
  let r := node_link hs i in
  0 <= r < i
  /\ (0 < r -> bucket_of (nth_hash hs r) = bucket_of (nth_hash hs i))
  /\ (forall j, 1 <= j < i -> bucket_of (nth_hash hs j) = bucket_of (nth_hash hs i) -> j <= r).
Proof.
  intros hs i Hi. unfold node_link. set (b := bucket_of (nth_hash hs i)).
  pose proof (bucket_head_spec (firstn (Z.to_nat (i - 1)) hs) b) as (A & B & C).
  assert (LF : zlen (firstn (Z.to_nat (i - 1)) hs) = i - 1) by (unfold zlen in *; rewrite length_firstn; lia). rewrite LF in A, C.
  assert (NF : forall j, 1 <= j <= i - 1 -> nth_hash (firstn (Z.to_nat (i - 1)) hs) j = nth_hash hs j).
  { intros j Hj. unfold nth_hash. apply nth_firstn_lt. lia. }
  split; [lia|]. split.
  - intros Hr. rewrite <- (NF (bucket_head (firstn (Z.to_nat (i - 1)) hs) b) ltac:(lia)). exact (B Hr).
  - intros j Hj Hb. apply C; [lia|]. rewrite (NF j ltac:(lia)). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma bucket_ids_above_head : forall hs b j, 1 <= j <= zlen hs -> bucket_of (nth_hash hs j) = b -> j <= bucket_head hs b.
Proof. intros hs b j Hj Hb. exact (proj2 (proj2 (bucket_head_spec hs b)) j Hj Hb). Qed.

Lemma index_of_spec : forall h l i0,
  match index_of h l i0 with
  | Some j => i0 <= j < i0 + zlen l /\ depot_hash (nth (Z.to_nat (j - i0)) l []) = h
  | None => forall q, (q < length l)%nat -> depot_hash (nth q l []) <> h
  end.
Proof.
  intros h l. induction l as [|k t IH]; intros i0; cbn; [intros q Hq; lia|].
  destruct (depot_hash k =? h) eqn:EQ.
  - apply Z.eqb_eq in EQ. unfold zlen. cbn [length]. split; [lia|]. replace (Z.to_nat (i0 - i0)) with 0%nat by lia. exact EQ.
  - apply Z.eqb_neq in EQ. specialize (IH (i0 + 1)). destruct (index_of h t (i0 + 1)) as [j|].
    + destruct IH as [A B]. unfold zlen in *. cbn [length]. split; [lia|].
      replace (Z.to_nat (j - i0)) with (S (Z.to_nat (j - (i0 + 1)))) by lia. exact B.
    + intros [|q] Hq; [exact EQ|]. apply IH. lia.
Qed.

Lemma nth_hash_map : forall ks i, 1 <= i <= zlen ks -> nth_hash (map depot_hash ks) i = depot_hash (nth (Z.to_nat (i - 1)) ks []).
Proof.
  intros ks i Hi. unfold nth_hash, zlen in *.
  rewrite (nth_indep _ 0 (depot_hash [])) by (rewrite length_map; lia). apply map_nth.
Qed.

Lemma lxor_lt_pow2 : forall a b n, 0 < n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lxor a b < 2^n.
Proof.
  intros a b n Hn Ha Hb.
  assert (NN : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact NN|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
  assert (Z.log2 a < n) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < n) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

Lemma depot_hash_range : forall k, 0 <= depot_hash k < 2^64.
Proof.
  intros k. unfold depot_hash, mur_get.
  match goal with |- context [Z.lxor (w64 ?x) (Z.shiftr (w64 ?x) 47)] => set (X := w64 x) end.
  assert (HX : 0 <= X < 2^64) by (subst X; unfold w64; apply Z.mod_pos_bound; lia).
  apply lxor_lt_pow2; [lia| exact HX|].
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. change (2^47 * 2^64) with (2^111). assert (2^64 < 2^111) by (apply Z.pow_lt_mono_r; lia). lia.
Qed.

Lemma nth_hash_range : forall ks i, 0 <= nth_hash (map depot_hash ks) i < 2^64.
Proof.
  intros ks i. unfold nth_hash. destruct (Nat.lt_ge_cases (Z.to_nat (i - 1)) (length (map depot_hash ks))) as [L|L].
  - rewrite (nth_indep _ 0 (depot_hash [])) by exact L. rewrite map_nth. apply depot_hash_range.
  - rewrite nth_overflow by exact L. lia.
Qed.

(* [comment removed for export] *)
Definition stored_of (f k : Z) : Z := Z.min kStoreBlockFrames (Z.max 0 (f - k * kStoreBlockFrames)).

Section DEPOT.
Variable segs : list Segment.
Variable E : aenv.
Let IC := ae_ic E.
Let TD : Z := aic_theDepot IC.
Let SS : Z := aic_stackStore IC.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).

Definition depot_keys (s : astate) : list (list Z) := ae_keys0 E ++ as_keys s.
Definition depot_hashes (s : astate) : list Z := map depot_hash (depot_keys s).
Definition node_blocks (s : astate) : list Z := ae_depot_nodes E :: as_node_blocks s.
Definition store_blocks (s : astate) : list Z := ae_store_blk E :: as_store_blocks s.
Definition nthz (l : list Z) (k : Z) : Z := if (0 <=? k) && (k <? zlen l) then nth (Z.to_nat k) l 0 else 0.
Definition node_addr (s : astate) (i : Z) : Z := nthz (node_blocks s) (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock).

Definition DepotRep (s : astate) (m : mem) : Prop :=
     (forall b, 0 <= b < kTabSize -> RW m (TD + 4 * b) [C4 (zw (bucket_head (depot_hashes s) b))])
  /\ RW m (TD + 0x400000) [C4 (zw (zlen (depot_keys s)))]
  /\ (forall k, 0 <= k < kNodesMap1 -> RW m (TD + 0x400010 + 8 * k) [C8 (zw (nthz (node_blocks s) k))])
  /\ (forall i, 1 <= i <= zlen (depot_keys s) ->
        exists sid, RW m (node_addr s i) [C8 (zw (nth_hash (depot_hashes s) i)); C4 (zw (node_link (depot_hashes s) i)); C4 sid])
  /\ (forall b, In b (node_blocks s) -> wr_at segs m b kDepotNodeBlockBytes)
  /\ RW m SS [C8 (zw (as_frames s))]
  /\ (exists al, RW m (SS + 8) [C8 al])
  /\ (forall k, 0 <= k < kStoreBlockCount ->
        RW m (SS + 16 + 16 * k) [C8 (zw (nthz (store_blocks s) k)); C4 (zw (stored_of (as_frames s) k))]
        /\ exists mx, RW m (SS + 28 + 16 * k) [C4 mx])
  /\ (forall b, In b (store_blocks s) -> exists bs, u8arr segs m b bs /\ Z.of_nat (length bs) = kStoreBlockBytes)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ RW m (TD + 0x400008) [C4 (zw 0)]
  /\ (forall k, 0 <= k < kStoreBlockCount -> RW m (SS + 28 + 16 * k) [C4 (zw 0)]).

(* [comment removed for export] *)
Definition DepotFPd (s : astate) (a : Z) : Prop :=
     in_ranges [(TD, kDepotStaticBytes); (SS, kStoreStaticBytes)] a
  \/ (exists b, In b (node_blocks s) /\ b <= a < b + kDepotNodeBlockBytes)
  \/ (exists b, In b (store_blocks s) /\ b <= a < b + kStoreBlockBytes).

Lemma node_addr_in_block : forall s i, 1 <= i -> i / kDepotNodesPerBlock < zlen (node_blocks s) ->
  exists b, In b (node_blocks s) /\ b <= node_addr s i /\ node_addr s i + 16 <= b + kDepotNodeBlockBytes.
Proof.
  intros s i Hi Hb. unfold node_addr, nthz.
  assert (0 <= i / kDepotNodesPerBlock) by (apply Z.div_pos; unfold kDepotNodesPerBlock; lia).
  replace ((0 <=? i / kDepotNodesPerBlock) && (i / kDepotNodesPerBlock <? zlen (node_blocks s))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  exists (nth (Z.to_nat (i / kDepotNodesPerBlock)) (node_blocks s) 0). split.
  - apply nth_In. unfold zlen in Hb. lia.
  - pose proof (Z.mod_pos_bound i kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)).
    unfold kDepotNodeBlockBytes, kDepotNodesPerBlock in *. lia.
Qed.

(* [comment removed for export] *)
Theorem DepotRep_frame : forall s (m m' : mem),
  (forall i, 1 <= i <= zlen (depot_keys s) -> i / kDepotNodesPerBlock < zlen (node_blocks s)) ->
  DepotRep s m -> wmono segs m m' -> (forall a, DepotFPd s a -> m' (wa a) = m (wa a)) -> DepotRep s m'.
Proof.
  intros s m m' NB (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) WM AG.
  assert (AGS : forall A n, TD <= A -> A + n <= TD + kDepotStaticBytes -> agree_on m m' A n).
  { intros A n H1 H2 x Hx. apply AG. left. exists (TD, kDepotStaticBytes). split; [left; reflexivity| cbn [fst snd]; lia]. }
  assert (AGT : forall A n, SS <= A -> A + n <= SS + kStoreStaticBytes -> agree_on m m' A n).
  { intros A n H1 H2 x Hx. apply AG. left. exists (SS, kStoreStaticBytes). split; [right; left; reflexivity| cbn [fst snd]; lia]. }
  unfold kDepotStaticBytes, kStoreStaticBytes in *.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
  - intros b Hb. eapply rw_cells_agree'; [| exact (R1 b Hb)]. apply AGS; cbn; unfold kTabSize in Hb; lia.
  - eapply rw_cells_agree'; [| exact R2]. apply AGS; cbn; lia.
  - intros k Hk. eapply rw_cells_agree'; [| exact (R3 k Hk)]. apply AGS; cbn; unfold kNodesMap1 in Hk; lia.
  - intros i Hi. destruct (R4 i Hi) as (sid & X). exists sid. eapply rw_cells_agree'; [| exact X].
    destruct (node_addr_in_block s i ltac:(lia) (NB i Hi)) as (b & Hb & L1 & L2).
    intros x Hx. apply AG. right; left. exists b. split; [exact Hb| cbn in Hx; lia].
  - intros b Hb. eapply wr_at_transport; [exact (R5 b Hb)| exact WM].
  - eapply rw_cells_agree'; [| exact R6]. apply AGT; cbn; lia.
  - destruct R7 as (al & X). exists al. eapply rw_cells_agree'; [| exact X]. apply AGT; cbn; lia.
  - intros k Hk. destruct (R8 k Hk) as (X1 & mx & X2). unfold kStoreBlockCount in Hk. split; [| exists mx].
    + eapply rw_cells_agree'; [| exact X1]. apply AGT; cbn; lia.
    + eapply rw_cells_agree'; [| exact X2]. apply AGT; cbn; lia.
  - intros b Hb. destruct (R9 b Hb) as (bs & U & L). exists bs. split; [| exact L]. eapply u8arr_agree; [| exact U].
    intros x Hx. apply AG. right; right. exists b. split; [exact Hb| lia].
  - eapply rw_cells_agree'; [| exact R10]. apply AGS; cbn; lia.
  - intros k Hk. eapply rw_cells_agree'; [| exact (R11 k Hk)]. unfold kStoreBlockCount in Hk. apply AGT; cbn; lia.
Qed.

(* [comment removed for export] *)
Corollary DepotRep_frame' : forall s (m m' : mem),
  depot_inv E s -> DepotRep s m -> wmono segs m m' -> (forall a, DepotFPd s a -> m' (wa a) = m (wa a)) -> DepotRep s m'.
Proof.
  intros s m m' (_ & _ & _ & _ & NB & _) R WM AG. eapply DepotRep_frame; [| exact R| exact WM| exact AG].
  intros i Hi. unfold depot_keys, node_blocks, zlen in *. unfold depot_n_ids in NB. cbn [length]. rewrite length_app in Hi.
  rewrite Nat2Z.inj_succ. apply Z.div_lt_upper_bound; [unfold kDepotNodesPerBlock; lia|]. unfold kDepotNodesPerBlock in *. lia.
Qed.

(* [comment removed for export] *)
Lemma DepotFPd_where : forall s a, DepotFPd s a ->
  in_ranges (depot_static E) a
  \/ (exists b, In b (ae_depot_nodes E :: as_node_blocks s) /\ b <= a < b + kDepotNodeBlockBytes)
  \/ (exists b, In b (ae_store_blk E :: as_store_blocks s) /\ b <= a < b + kStoreBlockBytes).
Proof. intros s a H. exact H. Qed.

(* [comment removed for export] *)
Definition DepotR : astate -> mem -> Prop := fun s m => depot_inv E s /\ DepotRep s m.
Definition DepotFP : astate -> Z -> Prop := DepotFPd.
Lemma DepotR_frame : forall s (m m' : mem),
  DepotR s m -> wmono segs m m' -> (forall a, DepotFP s a -> m' (wa a) = m (wa a)) -> DepotR s m'.
Proof. intros s m m' [DI R] WM AG. split; [exact DI| eapply DepotRep_frame'; eauto]. Qed.
Lemma DepotFP_where : forall s a, DepotFP s a ->
  in_ranges (depot_static E) a
  \/ (exists b, In b (ae_depot_nodes E :: as_node_blocks s) /\ b <= a < b + kDepotNodeBlockBytes)
  \/ (exists b, In b (ae_store_blk E :: as_store_blocks s) /\ b <= a < b + kStoreBlockBytes).
Proof. intros s a H. exact H. Qed.

End DEPOT.
End RC__1.
