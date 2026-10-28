(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith List Bool Lia Permutation.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_Blist HM AW_Merge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma w64_unsigned : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Hz. Qed.

#[using="Type"] Lemma map_unsigned_w64 : forall (l : list Z), Forall (fun e => 0 <= e < 2^64) l -> map bv_unsigned (map (Z_to_bv 64) l) = l.
Proof.
  intros l H. induction l as [|e l IH]; [reflexivity|]. inversion H; subst. cbn [map]. rewrite w64_unsigned by assumption. f_equal. apply IH. assumption.
Qed.

#[using="Type"] Lemma map_w64_unsigned : forall (l : list word), map (Z_to_bv 64) (map bv_unsigned l) = l.
Proof. intros l. induction l as [|e l IH]; [reflexivity|]. cbn [map]. rewrite Z_to_bv_bv_unsigned. f_equal. exact IH. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma sum_app : forall a b, sum (a ++ b) = sum a + sum b.
Proof. intros a b. unfold sum. induction a as [|x a IH]; cbn; [lia|]. rewrite IH. lia. Qed.


#[using="Type"] Lemma in_flat_map_unique : forall {A B} (f : A -> list B) (l : list A) b1 b2 (e : B),
  NoDup (flat_map f l) -> In b1 l -> In b2 l -> In e (f b1) -> In e (f b2) -> b1 = b2.
Proof.
  intros A B f l. induction l as [|a l IH]; intros b1 b2 e ND H1 H2 E1 E2; [destruct H1|].
  cbn in ND. pose proof (NoDup_app_remove_l _ _ ND) as NDl.
  assert (DJ : forall x, In x (f a) -> In x (flat_map f l) -> False).
  { intros x Xa Xl. induction (f a) as [|y ys IHy]; [destruct Xa|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
    destruct Xa as [->|Xa]; [apply NI; apply in_app_iff; right; exact Xl| exact (IHy ND' Xa)]. }
  destruct H1 as [->|H1], H2 as [->|H2]; [reflexivity| | | exact (IH b1 b2 e NDl H1 H2 E1 E2)].
  - exfalso. apply (DJ e E1). apply in_flat_map. exists b2. exact (conj H2 E2).
  - exfalso. apply (DJ e E2). apply in_flat_map. exists b1. exact (conj H1 E1).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ba_of (b : bnode) : batch := BA (bn_addr b) (map bv_unsigned (bn_elems b)) (bn_size b).

#[using="Type"] Lemma bn_of_ba_of : forall b, bn_of (ba_of b) = b.
Proof. intros [a sz es]. unfold bn_of, ba_of. cbn. rewrite map_w64_unsigned. reflexivity. Qed.
#[using="Type"] Lemma map_bn_of_ba_of : forall l, map bn_of (map ba_of l) = l.
Proof. intros l. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite bn_of_ba_of, IH. reflexivity. Qed.
#[using="Type"] Lemma b_count_ba_of : forall b, b_count (ba_of b) = bn_count b.
Proof. intros b. unfold b_count, bn_count, ba_of. cbn. rewrite length_map. reflexivity. Qed.
#[using="Type"] Lemma map_b_addr_ba_of : forall l, map b_addr (map ba_of l) = map bn_addr l.
Proof. intros l. rewrite map_map. apply map_ext. intros b. reflexivity. Qed.
#[using="Type"] Lemma sum_b_size_ba_of : forall l, sum (map b_size (map ba_of l)) = bsum l.
Proof. intros l. induction l as [|b l IH]; [reflexivity|]. cbn [map bsum]. unfold sum in *. cbn [fold_right]. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma flat_map_b_elems_ba_of : forall l, flat_map b_elems (map ba_of l) = map bv_unsigned (flat_map bn_elems l).
Proof. intros l. induction l as [|b l IH]; [reflexivity|]. cbn [map flat_map]. rewrite map_app, IH. reflexivity. Qed.
#[using="Type"] Lemma map_b_addr_bn_of : forall l, map bn_addr (map bn_of l) = map b_addr l.
Proof. intros l. rewrite map_map. apply map_ext. intros b. reflexivity. Qed.
#[using="Type"] Lemma flat_map_bn_elems_bn_of : forall l, flat_map bn_elems (map bn_of l) = map (Z_to_bv 64) (flat_map b_elems l).
Proof. intros l. induction l as [|b l IH]; [reflexivity|]. cbn [map flat_map bn_of bn_elems]. rewrite map_app, IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mloop_inv : forall (P Q : bnode -> Prop),
  (forall c x, bn_count c + bn_count x <= 1021 -> P c -> P x -> P (mnode c x)) ->
  (forall c x, bn_count c + bn_count x <= 1021 -> P c -> P x -> Q (xnode x)) ->
  forall r c, P c -> Forall P r -> Forall P (fst (mloop c r)) /\ Forall Q (snd (mloop c r)).
Proof.
  intros P Q HP HQ r. induction r as [|x r IH]; intros c Pc Pr.
  - cbn. split; [constructor; [exact Pc| constructor]| constructor].
  - inversion Pr as [|? ? Px Pr']; subst. cbn [mloop]. destruct (Z.ltb_spec 1021 (bn_count c + bn_count x)) as [LT|LE].
    + destruct (IH x Px Pr') as [A B]. cbn [fst snd]. split; [constructor; [exact Pc| exact A]| exact B].
    + destruct (IH (mnode c x) (HP c x LE Pc Px) Pr') as [A B]. cbn [fst snd]. split; [exact A|]. constructor; [exact (HQ c x LE Pc Px)| exact B].
Qed.

#[using="Type"] Lemma merge_out_inv : forall (P Q : bnode -> Prop),
  (forall c x, bn_count c + bn_count x <= 1021 -> P c -> P x -> P (mnode c x)) ->
  (forall c x, bn_count c + bn_count x <= 1021 -> P c -> P x -> Q (xnode x)) ->
  forall gs, Forall P gs -> Forall P (fst (merge_out gs)) /\ Forall Q (snd (merge_out gs)).
Proof.
  intros P Q HP HQ [|b r] H; [cbn; split; constructor|]. inversion H; subst. cbn [merge_out]. apply (mloop_inv P Q HP HQ); assumption.
Qed.

(* [comment removed for export] *)
Definition usz (h : ahst) (e : Z) : Z :=
  match find (fun k => ck_hdr k =? e) (h_chunks h) with Some k => used_size (ck_n k) | None => 0 end.
Definition bP (h : ahst) (b : bnode) : Prop := 1 <= bn_count b /\ bn_size b = kBatchSize + sum (map (usz h) (map bv_unsigned (bn_elems b))).

#[using="Type"] Lemma bP_mnode : forall h c x, bn_count c + bn_count x <= 1021 -> bP h c -> bP h x -> bP h (mnode c x).
Proof.
  intros h c x _ [C1 C2] [X1 X2]. unfold bP, mnode, bn_count in *. cbn [bn_elems bn_size]. rewrite length_app, !map_app, sum_app.
  unfold kBatchSize in *. split; lia.
Qed.
#[using="Type"] Lemma bQ_xnode : forall h c x, bn_count c + bn_count x <= 1021 -> bP h c -> bP h x -> (fun b => bn_elems b = [] /\ bn_size b = kBatchSize) (xnode x).
Proof. intros. cbn. split; reflexivity. Qed.

#[using="Type"] Lemma bP_orig : forall h b, wf_batch h b -> Forall (fun e => 0 <= e < 2^64) (b_elems b) -> bP h (bn_of b).
Proof.
  (intros h b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4); intros R). unfold bP, bn_count. cbn [bn_of bn_elems bn_size]. rewrite length_map, (map_unsigned_w64 _ R).
  split; [unfold b_count in B1; lia|]. rewrite B2. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wf_quar_cc (h : ahst) (ct cg : Z) : Prop :=
  wf_qcache h (h_tq h) ct /\ wf_qcache h (h_gq h) cg
  /\ NoDup (map b_addr (q_batches (h_tq h) ++ q_batches (h_gq h)))
  /\ (forall k, In k (h_chunks h) -> ck_st k = CHUNK_QUARANTINE ->
        exists! b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) /\ In (ck_hdr k) (b_elems b)).
Definition WFC (h : ahst) (ct cg : Z) : Prop :=
  wf_L' (h_L h) /\ wf_cache h /\ wf_region h /\ wf_chunks' h /\ wf_quar_cc h ct cg /\ wf_sec h /\ wf_depot' h /\ wf_budget h /\ wf_big h /\ wf_x h /\ wf_ghost h.

#[using="Type"] Lemma awf'_iff_WFC : forall h, awf' h <-> WFC h kQuarantineCache kQuarantineMax.
Proof. intros h. unfold awf', WFC, wf_quar, wf_quar_cc. tauto. Qed.



(* [comment removed for export] *)
#[using="Type"] Lemma WFC_cap : forall h ct cg ct' cg', WFC h ct cg -> q_bytes (h_tq h) <= ct' -> q_bytes (h_gq h) <= cg' -> WFC h ct' cg'.
Proof.
  (intros h ct cg ct' cg' dd_H; ddestruct dd_H as (W1 & W2 & W3 & W4 & ((A1 & A2 & A3) & (B1 & B2 & B3) & Q3 & Q4) & W6); intros LT LG).
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [| exact W6].
  split; [split; [exact A1| split; [exact A2| lia]]|]. split; [split; [exact B1| split; [exact B2| lia]]|]. exact (conj Q3 Q4).
Qed.

#[using="Type"] Lemma WFK_of_WFC : forall h ct cg, WFC h ct cg -> h_havol h <= AVOL_MAX -> WFK h.
Proof.
  (intros h ct cg dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG); intros HV). destruct WX as [WX1 WX2].
  split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WG HV)))))].
  intros c Hc. pose proof (WR c Hc) as R. cbn zeta in R. ddestruct R as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _).
  cbn zeta. split; [exact R0|]. split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [exact R6|]. split; [exact R7| exact R8].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_range : forall h k, wf_L (h_L h) -> wf_region h -> wf_chunks' h -> In k (h_chunks h) -> 0 <= ck_hdr k < 2^64.
Proof.
  intros h k WL WR WK Hk. ddestruct (chunk_ext' h k WL WR WK Hk) as (X0 & E1 & E2 & E3 & E4 & E5 & E6 & E7). destruct E5 as [E5 E5'].
  pose proof aceil_lt47. clear E7. lia.
Qed.

#[using="Type"] Lemma batch_elems_range : forall h b, wf_L (h_L h) -> wf_region h -> wf_chunks' h -> wf_batch h b -> Forall (fun e => 0 <= e < 2^64) (b_elems b).
Proof.
  (intros h b WL WR WK dd_H; ddestruct dd_H as (_ & _ & B3 & _)). apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k & Hk & _ & <-).
  exact (hdr_range h k WL WR WK Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RQ.
  Variables (h : ahst) (ct cg : Z) (G X gs1 gs2 : list bnode).
  Let gbs := map bn_of (q_batches (h_gq h)).
  Hypothesis WF : WFC h ct cg.
  Hypothesis TQ0 : q_batches (h_tq h) = [].
  Hypothesis FM : flat_map bn_elems G = flat_map bn_elems gbs.
  Hypothesis FT : flat_map bn_elems X = [].
  Hypothesis ADDR : forall b', In b' (X ++ G) -> exists b, In b gbs /\ bn_addr b' = bn_addr b.
  Hypothesis LEN : length (X ++ G) = length gbs.
  Hypothesis BWF : bwf (X ++ G).
  Hypothesis PG : Forall (bP h) G.
  Hypothesis EG : G = gs1 ++ gs2.
  Hypothesis CAP : bsum gs2 <= kQuarantineMax.

  Definition h_rq : ahst := set_gq (set_tq h (QC (map ba_of (X ++ gs1)) 0)) (QC (map ba_of gs2) (bsum gs2)).

  #[using="Type"] Lemma rq_L : h_L h_rq = h_L h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_chunks : h_chunks h_rq = h_chunks h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_reg : h_reg h_rq = h_reg h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_cache : h_cache h_rq = h_cache h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_cinit : h_cinit h_rq = h_cinit h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_sec : h_sec h_rq = h_sec h. Proof. reflexivity. Qed.
        #[using="Type"] Lemma rq_pa : h_pa_committed h_rq = h_pa_committed h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_havol : h_havol h_rq = h_havol h. Proof. reflexivity. Qed.
    #[using="Type"] Lemma rq_tq : q_batches (h_tq h_rq) = map ba_of (X ++ gs1). Proof. reflexivity. Qed.
    #[using="Type"] Lemma rq_gq : q_batches (h_gq h_rq) = map ba_of gs2. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_gqb : q_bytes (h_gq h_rq) = bsum gs2. Proof. reflexivity. Qed.
  #[using="Type"] Lemma rq_carved : forall c, carved h_rq c = carved h c. Proof. reflexivity. Qed.
    #[using="Type"] Lemma rq_hzones : hzones h_rq = hzones h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma kview_rq : kview_eq h h_rq. Proof. unfold kview_eq. repeat split; reflexivity. Qed.
  #[using="EG"] Lemma rq_all : q_batches (h_tq h_rq) ++ q_batches (h_gq h_rq) = map ba_of (X ++ G).
  Proof. rewrite rq_tq, rq_gq, EG, <- map_app, app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma rq_tq_bn : map bn_of (q_batches (h_tq h_rq)) = X ++ gs1. Proof. rewrite rq_tq. apply map_bn_of_ba_of. Qed.
  #[using="Type"] Lemma rq_gq_bn : map bn_of (q_batches (h_gq h_rq)) = gs2. Proof. rewrite rq_gq. apply map_bn_of_ba_of. Qed.

  Let WL : wf_L (h_L h). Proof. ddestruct WF as ((A & _) & _). exact A. Qed.
  Let WR : wf_region h. Proof. ddestruct WF as (_ & _ & A & _). exact A. Qed.
  Let WK : wf_chunks' h. Proof. ddestruct WF as (_ & _ & _ & A & _). exact A. Qed.
  Let WGQ : wf_qcache h (h_gq h) cg. Proof. ddestruct WF as (_ & _ & _ & _ & (_ & A & _) & _). exact A. Qed.

  #[using="hAR ct cg WF WL WR WK WGQ"] Lemma gq_range : Forall (fun e => 0 <= e < 2^64) (flat_map b_elems (q_batches (h_gq h))).
  Proof.
    apply Forall_forall. intros e He. apply in_flat_map in He as (b & Hb & He). destruct WGQ as (G1 & _).
    exact (proj1 (Forall_forall _ _) (batch_elems_range h b WL WR WK (proj1 (Forall_forall _ _) G1 b Hb)) e He).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR ct cg gbs WF FM FT WL WR WK WGQ"] Lemma rq_flat : flat_map b_elems (map ba_of (X ++ G)) = flat_map b_elems (q_batches (h_gq h)).
  Proof.
    rewrite flat_map_b_elems_ba_of, flat_map_app, FT, FM. cbn [app]. unfold gbs. rewrite flat_map_bn_elems_bn_of. apply map_unsigned_w64. exact gq_range.
  Qed.

  #[using="hAR ADDR LEN BWF"] Lemma rq_addrs_perm : Permutation (map bn_addr (X ++ G)) (map bn_addr gbs).
  Proof.
    apply NoDup_Permutation_bis.
    - destruct BWF as [_ [ND _]]. exact ND.
    - rewrite !length_map, LEN. apply le_n.
    - intros a Ha. apply in_map_iff in Ha as (b' & <- & Hb'). ddestruct (ADDR b' Hb') as (b & Hb & ->). apply in_map. exact Hb.
  Qed.

  #[using="hAR G gbs TQ0 ADDR LEN BWF EG"] Lemma rq_batch_set : forall c, Permutation (batch_set h_rq c) (batch_set h c).
  Proof.
    intros c. unfold batch_set. rewrite rq_all, TQ0, rq_L. cbn [app]. destruct (c =? kBatchClass); [| apply Permutation_refl].
    rewrite <- (map_map b_addr (fun a => compact (h_L h) c a) (map ba_of (X ++ G))), <- (map_map b_addr (fun a => compact (h_L h) c a) (q_batches (h_gq h))).
    apply Permutation_map. rewrite map_b_addr_ba_of. unfold gbs in *. rewrite <- map_b_addr_bn_of. exact rq_addrs_perm.
  Qed.

  #[using="hAR G gbs TQ0 ADDR LEN BWF EG"] Lemma rq_owned : forall c, Permutation (owned h_rq c) (owned h c).
  Proof. intros c. unfold owned, fa_set, cache_set, chunk_set. rewrite rq_reg, rq_cache, rq_chunks, rq_L. repeat apply Permutation_app_head. apply rq_batch_set. Qed.

  (* [comment removed for export] *)
  #[using="hAR ct cg gbs WF FM FT ADDR LEN BWF WL WR WK WGQ"] Lemma rq_node : forall n, In n (X ++ G) ->
    Forall (fun e => exists k, In k (h_chunks h) /\ ck_st k = CHUNK_QUARANTINE /\ ck_hdr k = e) (b_elems (ba_of n))
    /\ (exists i, 0 <= i < carved h kBatchClass /\ b_addr (ba_of n) = chunk_at (h_L h) kBatchClass i)
    /\ b_count (ba_of n) <= kBatchCap.
  Proof.
    intros n Hn. destruct WGQ as (G1 & _). split; [| split].
    - apply Forall_forall. intros e He.
      assert (He' : In e (flat_map b_elems (q_batches (h_gq h)))).
      { rewrite <- rq_flat. apply in_flat_map. exists (ba_of n). split; [apply in_map; exact Hn| exact He]. }
      apply in_flat_map in He' as (b & Hb & Heb). destruct (proj1 (Forall_forall _ _) G1 b Hb) as (_ & _ & B3 & _).
      exact (proj1 (Forall_forall _ _) B3 e Heb).
    - ddestruct (ADDR n Hn) as (b & Hb & E). unfold gbs in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). cbn [bn_addr bn_of] in E.
      destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4). cbn [b_addr ba_of]. rewrite E. exact B4.
    - rewrite b_count_ba_of. pose proof (bwf_ok_in _ _ BWF Hn) as OK. unfold bn_ok in OK. unfold kBatchCap. lia.
  Qed.

  #[using="hAR h ct cg gbs WF TQ0 FM FT WL WR WK WGQ"] Lemma rq_nodup_elems : NoDup (flat_map b_elems (map ba_of (X ++ G))).
  Proof. rewrite rq_flat. ddestruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & WX2 & _) & _). rewrite TQ0 in WX2. exact WX2. Qed.

  #[using="ct cg G gbs WF TQ0 FM FT ADDR LEN BWF PG EG CAP WL WR WK WGQ"] Theorem WFR_rq : WFR h_rq.
  Proof.
    dpose WF as (WL' & WC & WR' & WK' & WQ & WS & WD & WB & WBIG & WX & WG). ddestruct WQ as (WT & WGQ' & NDA & UQ).
    split; [exact WL'|]. split; [exact WC|].
    split. { (* [comment removed for export] *)
      intros c Hc. pose proof (WR' c Hc) as R. cbn zeta in R |- *. rewrite rq_reg, rq_carved.
      ddestruct R as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
      split; [exact X7|]. split; [exact X8|]. split; [exact X9|].
      split; [exact (Permutation_NoDup (Permutation_sym (rq_owned c)) X10)|].
      intros kk. rewrite (X11 kk). split; intros H; [eapply Permutation_in; [apply Permutation_sym, rq_owned| exact H]| eapply Permutation_in; [apply rq_owned| exact H]]. }
    split; [exact WK'|].
    split. { (* [comment removed for export] *)
      assert (ALLR : Forall (wf_batch_r h_rq) (map ba_of (X ++ gs1))).
      { apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (n & <- & Hn).
        ddestruct (rq_node n ltac:(rewrite EG; apply in_app_iff; apply in_app_iff in Hn as [Hn|Hn]; [left; exact Hn| right; apply in_app_iff; left; exact Hn])) as (N1 & N2 & N3).
        split; [exact N3|]. split; [rewrite rq_chunks; exact N1| rewrite rq_carved, rq_L; exact N2]. }
      split; [| split; [| split]].
      - rewrite rq_tq. destruct (map ba_of (X ++ gs1)) as [|b tb]; [exact I|]. inversion ALLR; subst. split; assumption.
      - (* [comment removed for export] *)
        split; [| split; [rewrite rq_gq, rq_gqb; symmetry; apply sum_b_size_ba_of| rewrite rq_gqb; split; [apply bsum_nonneg; rewrite EG in BWF; exact (proj1 (bwf_app_r _ _ (bwf_app_r _ _ BWF)))| exact CAP]]].
        rewrite rq_gq. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (n & <- & Hn).
        assert (HnG : In n G) by (rewrite EG; apply in_app_iff; right; exact Hn).
        ddestruct (rq_node n ltac:(apply in_app_iff; right; exact HnG)) as (N1 & N2 & N3).
        destruct (proj1 (Forall_forall _ _) PG n HnG) as [P1 P2].
        split; [rewrite b_count_ba_of in N3 |- *; split; [exact P1| exact N3]|].
        split; [| split; [rewrite rq_chunks; exact N1| rewrite rq_carved, rq_L; exact N2]].
        cbn [b_size b_elems ba_of]. rewrite rq_chunks. exact P2.
      - rewrite rq_all, map_b_addr_ba_of. destruct BWF as [_ [ND _]]. exact ND.
      - intros k Hk Sk. rewrite rq_chunks in Hk. rewrite rq_all.
        ddestruct (UQ k Hk Sk) as (b0 & [Hb0 Hin0] & _). rewrite TQ0 in Hb0. cbn [app] in Hb0.
        assert (IN : In (ck_hdr k) (flat_map b_elems (map ba_of (X ++ G)))).
        { rewrite rq_flat. apply in_flat_map. exists b0. exact (conj Hb0 Hin0). }
        apply in_flat_map in IN as (b & Hb & Hin). exists b. split; [exact (conj Hb Hin)|].
        intros b' [Hb' Hin']. exact (in_flat_map_unique b_elems _ b b' (ck_hdr k) rq_nodup_elems Hb Hb' Hin Hin'). }
    split; [unfold wf_sec; rewrite rq_sec, rq_pa; exact WS|].
    split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
    split. { ddestruct WX as (WX1 & WX2 & WX3). split; [exact WX1|]. split; [rewrite rq_all; exact rq_nodup_elems| exact WX3]. }
    exact WG.
  Qed.

  (* [comment removed for export] *)
  End RQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition h_drainq (h : ahst) : ahst := set_tq (set_gq h (q_transfer (h_gq h) (h_tq h))) qcache0.

Section DQ.
  Variables (h : ahst) (ct cg : Z).
  Hypothesis WF : WFC h ct cg.

  #[using="Type"] Lemma dq_all_perm : Permutation (q_batches (h_tq (h_drainq h)) ++ q_batches (h_gq (h_drainq h))) (q_batches (h_tq h) ++ q_batches (h_gq h)).
  Proof. unfold h_drainq, q_transfer. cbn. apply Permutation_app_comm. Qed.

  #[using="Type"] Lemma dq_batch_set : forall c, Permutation (batch_set (h_drainq h) c) (batch_set h c).
  Proof.
    intros c. unfold batch_set. change (h_L (h_drainq h)) with (h_L h). destruct (c =? kBatchClass); [| apply Permutation_refl].
    apply Permutation_map. apply dq_all_perm.
  Qed.

  #[using="Type"] Lemma dq_owned : forall c, Permutation (owned (h_drainq h) c) (owned h c).
  Proof. intros c. unfold owned, fa_set, cache_set, chunk_set. cbn -[batch_set]. repeat apply Permutation_app_head. apply dq_batch_set. Qed.

  #[using="Type"] Lemma kview_dq : kview_eq h (h_drainq h). Proof. unfold kview_eq. repeat split; reflexivity. Qed.

  #[using="ct cg WF"] Theorem WFC_drainq : WFC (h_drainq h) 0 (q_bytes (h_gq h) + q_bytes (h_tq h)).
  Proof.
    dpose WF as (WL' & WC & WR' & WK' & WQ & WS & WD & WB & WBIG & WX & WG). ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & NDA & UQ).
    split; [exact WL'|]. split; [exact WC|].
    split. { (* [comment removed for export] *)
      intros c Hc. pose proof (WR' c Hc) as R. cbn zeta in R |- *. change (h_reg (h_drainq h)) with (h_reg h). change (carved (h_drainq h) c) with (carved h c).
      ddestruct R as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
      split; [exact X7|]. split; [exact X8|]. split; [exact X9|].
      split; [exact (Permutation_NoDup (Permutation_sym (dq_owned c)) X10)|].
      intros kk. rewrite (X11 kk). split; intros H; [eapply Permutation_in; [apply Permutation_sym, dq_owned| exact H]| eapply Permutation_in; [apply dq_owned| exact H]]. }
    split; [exact WK'|].
    split. { split; [| split; [| split]].
      - split; [constructor|]. split; [reflexivity| cbn; lia].
      - split; [| split].
        + unfold h_drainq, q_transfer. cbn. apply Forall_app. exact (conj G1 T1).
        + unfold h_drainq, q_transfer. cbn. rewrite map_app, sum_app, <- G2, <- T2. reflexivity.
        + unfold h_drainq, q_transfer. cbn. lia.
      - eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; apply dq_all_perm| exact NDA].
      - change (h_chunks (h_drainq h)) with (h_chunks h). intros k Hk Sk. ddestruct (UQ k Hk Sk) as (b & [Hb Hin] & U).
        exists b. split; [split; [eapply Permutation_in; [apply Permutation_sym; apply dq_all_perm| exact Hb]| exact Hin]|].
        intros b' [Hb' Hin']. apply U. split; [eapply Permutation_in; [apply dq_all_perm| exact Hb']| exact Hin']. }
    split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
    split. { ddestruct WX as (WX1 & WX2 & WX3). split; [exact WX1|]. split; [| exact WX3].
             change (h_chunks (h_drainq h)) with (h_chunks h).
             eapply Permutation_NoDup; [apply Permutation_flat_map; apply Permutation_sym; apply dq_all_perm| exact WX2]. }
    exact WG.
  Qed.
End DQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition h_rx (h : ahst) : ahst := set_tq h qcache0.

#[using="Type"] Lemma kview_rx : forall h, kview_eq h (h_rx h). Proof. intros h. apply kview_set_tq. Qed.

#[using="Type"] Lemma awf'_rx : forall h, WFR h -> q_batches (h_tq h) = [] -> awf' (h_rx h).
Proof.
  (intros h dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG); intros TQ). ddestruct WQ as (WT & WGQ & NDA & UQ).
  assert (OW : forall c, owned (h_rx h) c = owned h c).
  { intros c. unfold owned, fa_set, cache_set, chunk_set, batch_set, h_rx. cbn. rewrite TQ. reflexivity. }
  split; [exact WL|]. split; [exact WC|].
  split. { intros c Hc. cbn zeta. pose proof (WR c Hc) as R. cbn zeta in R. unfold carved in *. cbn [h_rx set_tq h_reg]. rewrite OW. exact R. }
  split; [exact WK|].
  split. { split; [| split; [exact WGQ| split]].
    - split; [constructor|]. split; [reflexivity| unfold kQuarantineCache; cbn; lia].
    - cbn. rewrite TQ in NDA. exact NDA.
    - cbn. intros k Hk Sk. rewrite TQ in UQ. exact (UQ k Hk Sk). }
  split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
  split. { ddestruct WX as (WX1 & WX2 & WX3). split; [exact WX1|]. split; [cbn; rewrite TQ in WX2; exact WX2| exact WX3]. }
  exact WG.
Qed.

End ARUN_1.
