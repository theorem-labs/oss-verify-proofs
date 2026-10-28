(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memset Fz_kit_ra.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)








(* [comment removed for export] *)






(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma own_apart : forall s LBall m (p1 : bptr) A1 n1 (p2 : bptr) A2 n2, RHEAP s LBall m -> In (p1, A1, n1) LBall -> In (p2, A2, n2) LBall -> p1 <> p2 ->
  A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof.
  intros s LBall m p1 A1 n1 p2 A2 n2 HP I1 I2 NE. pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p1, A1, n1) (p2, A2, n2) HP I1 I2) as D.
  unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. exact NE.
Qed.

Lemma lseg_owns : forall DV m LBall L ns c c', lseg DV m LBall L c ns c' -> forall p A, In (p, A) ns -> cown LBall L p A 24 24.
Proof.
  intros DV m LBall L ns. induction ns as [|[q B] ns IH]; intros c c' H p A Hin; [destruct Hin|]. cbn [lseg] in H. destruct H as (_ & O & _ & _ & R).
  destruct Hin as [E|Hin]; [inversion E; subst; exact O| exact (IH _ _ R p A Hin)].
Qed.
Lemma chain_owns : forall DV m LBall L ns c, chain DV m LBall L c ns -> forall p A, In (p, A) ns -> cown LBall L p A 24 24.
Proof. intros DV m LBall L ns c (c' & S & _). exact (lseg_owns _ _ _ _ _ _ _ S). Qed.

Lemma nodes_fop : forall s LBall m (ns : list (bptr * Z)), RHEAP s LBall m -> (forall p A, In (p, A) ns -> In (p, A, 24) LBall) -> List.NoDup (map fst ns) ->
  ForallOrdPairs apart24 (map snd ns).
Proof.
  intros s LBall m ns HP. induction ns as [|[p A] ns IH]; intros OW ND; cbn [map snd]; [constructor|]. cbn [map fst] in ND. inversion ND as [|x l NI ND']; subst.
  constructor; [| apply IH; [intros q Bq Hq; apply OW; right; exact Hq| exact ND']].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([q Bq] & E & Hq). cbn [snd] in E. subst X.
  unfold apart24. eapply (own_apart s LBall m p A 24 q Bq 24 HP); [apply OW; left; reflexivity| apply OW; right; exact Hq|].
  intros E. apply NI. subst q. apply in_map_iff. exists (p, Bq). auto.
Qed.

(* [comment removed for export] *)
Lemma lh_sep : forall s DV m LBall L f lh pl pb B nmb g bks, RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks ->
  (lh + 104 <= B \/ B + 8 * g_na g <= lh)
  /\ (forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * g_na g <= A))
  /\ (forall i j x y, (i < length bks)%nat -> (j < length bks)%nat -> i <> j -> In x (nth i bks []) -> In y (nth j bks []) -> apart24 (snd x) (snd y))
  /\ (forall i, (i < length bks)%nat -> ForallOrdPairs apart24 (map snd (nth i bks []))).
Proof.
  intros s DV m LBall L f lh pl pb B nmb g bks HP (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
  assert (OWN : forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> In (p, A, 24) LBall).
  { intros i p A Hi Hin. assert (IR : 0 <= Z.of_nat i < g_na g) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C.
    exact (proj1 (chain_owns _ _ _ _ _ _ C p A Hin)). }
  assert (IDS : forall i p A, In (p, A) (nth i bks []) -> In p (map fst (concat bks))).
  { intros i p A Hin. apply in_map_iff. exists (p, A). split; [reflexivity| eapply in_nth_concat; exact Hin]. }
  split. { eapply (own_apart s LBall m pl lh 104 pb B (8 * g_na g) HP); [exact (proj1 OL)| exact (proj1 OB)|]. intros E. apply NI1. left. symmetry. exact E. }
  split. { intros i p A Hi Hin. split.
    - eapply (own_apart s LBall m p A 24 pl lh 104 HP); [exact (OWN i p A Hi Hin)| exact (proj1 OL)|]. intros E. apply NI1. right. subst p. exact (IDS i pl A Hin).
    - eapply (own_apart s LBall m p A 24 pb B (8 * g_na g) HP); [exact (OWN i p A Hi Hin)| exact (proj1 OB)|]. intros E. apply NI2. subst p. exact (IDS i pb A Hin). }
  split. { intros i j [p A] [q Bq] Hi Hj NE Hx Hy. cbn [snd]. unfold apart24.
    eapply (own_apart s LBall m p A 24 q Bq 24 HP); [exact (OWN i p A Hi Hx)| exact (OWN j q Bq Hj Hy)|].
    exact (nodup_concat_ne bks i j (p, A) (q, Bq) ND2 NE Hx Hy). }
  intros i Hi. eapply (nodes_fop s LBall m); [exact HP| intros p A Hin; exact (OWN i p A Hi Hin)| exact (nodup_concat_nth bks i ND2)].
Qed.

(* [comment removed for export] *)
Lemma bucket_nsep : forall s DV m LBall L f lh pl pb B nmb g bks i j, RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks ->
  0 <= i < g_na g -> 0 <= j < g_na g -> i <> j -> nsep (nth (Z.to_nat i) bks []) (B + 8 * i) (B + 8 * j).
Proof.
  intros s DV m LBall L f lh pl pb B nmb g bks i j HP REP Hi Hj NE.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (_ & SN & _ & SF). destruct REP as (G & _ & _ & _ & _ & _ & LEN & _).
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  split; [exact (SF _ LI)|]. split; [| lia].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([p A] & E & Hin). cbn [snd] in E. subst X.
  destruct (SN _ p A LI Hin) as [_ SB]. unfold apartc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lseg_end_loc : forall DV m LBall L ns c c', lseg DV m LBall L c ns c' ->
  (ns = [] /\ c' = c) \/ (exists pre p A, ns = pre ++ [(p, A)] /\ c' = A + 8).
Proof.
  intros DV m LBall L ns. induction ns as [|[q Bq] ns IH]; intros c c' H; cbn [lseg] in H; [left; auto|].
  destruct H as (_ & _ & _ & _ & R). right. destruct (IH _ _ R) as [[-> ->]|(pre & p & A & -> & ->)].
  - exists [], q, Bq. auto.
  - exists ((q, Bq) :: pre), p, A. auto.
Qed.

(* [comment removed for export] *)
Lemma cfr_agree_lh : forall T W SP LBall m m' lh B g (bks : list (list (bptr * Z))) (pl pb : bptr),
  cfr T W SP LBall m m' -> In (pl, lh, 104) LBall -> In (pb, B, 8 * g_na g) LBall ->
  (forall p A, In (p, A) (concat bks) -> In (p, A, 24) LBall) ->
  (forall q, lh_T pl pb bks q -> ~ T q) ->
  agree_on (lh_fp lh B g bks) m m'.
Proof.
  intros T W SP LBall m m' lh B g bks pl pb H IL IB IN NT. eapply agree_on_mono; [exact H|]. intros a [Ha|[Ha|(p & A & Hp & Ha)]]; right; left.
  - exists (pl, lh, 104). split; [exact IL|]. split; [apply NT; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
  - exists (pb, B, 8 * g_na g). split; [exact IB|]. split; [apply NT; right; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
  - exists (p, A, 24). split; [exact (IN p A Hp)|]. split; [apply NT; right; right; apply in_map_iff; exists (p, A); auto|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
Qed.

Lemma lh_rep_owned : forall DV m LBall L f lh pl pb B nmb g bks, lh_rep DV m LBall L f lh pl pb B nmb g bks ->
  forall p A, In (p, A) (concat bks) -> cown LBall L p A 24 24.
Proof.
  intros DV m LBall L f lh pl pb B nmb g bks (G & _ & _ & _ & _ & _ & LEN & CH & _) p A Hin.
  apply in_concat in Hin. destruct Hin as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & E). subst ns.
  assert (IR : 0 <= Z.of_nat i < g_na g) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C. exact (chain_owns _ _ _ _ _ _ C p A Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bucket_fp (B : Z) (bks : list (list (bptr * Z))) (i : Z) (a : Z) : Prop :=
  (B + 8 * i <= a < B + 8 * i + 8) \/ exists p A, In (p, A) (nth (Z.to_nat i) bks []) /\ A <= a < A + 24.

Lemma lh_rep_upd : forall DV m m' LBall L LBall' L' f lh pl pb B nmb g g' bks bks' (J : Z -> Prop),
  lh_rep DV m LBall L f lh pl pb B nmb g bks -> (forall i, J i \/ ~ J i) ->
  g_na g' = g_na g -> lh_geo_ok g' ->
  (exists x40 x48 err pad, rw_cells usegs m' lh (lh_cells f B g' x40 x48 err pad)) ->
  (forall q A n nm, lh_T pl pb bks q -> cown LBall L q A n nm -> cown LBall' L' q A n nm) ->
  Z.of_nat (length bks') = g_na g ->
  (forall i, 0 <= i < g_na g -> J i -> chain DV m' LBall' L' (B + 8 * i) (nth (Z.to_nat i) bks' [])) ->
  (forall i, 0 <= i < g_na g -> ~ J i -> nth (Z.to_nat i) bks' [] = nth (Z.to_nat i) bks [] /\ agree_on (bucket_fp B bks i) m m') ->
  (forall i, g_nn g' <= i < g_na g -> nth (Z.to_nat i) bks' [] = []) ->
  List.NoDup (pl :: pb :: map fst (concat bks')) ->
  lh_rep DV m' LBall' L' f lh pl pb B nmb g' bks'.
Proof.
  intros DV m m' LBall L LBall' L' f lh pl pb B nmb g g' bks bks' J (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND) JDEC ENA G' SC' HO LEN' CHJ CHO EMP' ND'.
  split; [exact G'|]. split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|]. split; [exact SC'|].
  rewrite ENA. split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN'|].
  split; [| split; [exact EMP'| exact ND']].
  intros i Hi. destruct (JDEC i) as [HJ|HJ]; [exact (CHJ i Hi HJ)|].
  destruct (CHO i Hi HJ) as [E AG]. rewrite E. eapply chain_agree; [exact (CH i Hi)| exact AG|].
  intros p A Hp. apply HO. right; right. apply in_map_iff. exists (p, A). split; [reflexivity|]. eapply in_nth_concat. exact Hp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_assemble : forall (n : nat) m B, 0 <= B -> B + 8 * Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> exists w : word, rw_cells usegs m (B + 8 * Z.of_nat i) [C8 w]) ->
  exists src, rw_cells usegs m B [CB (8 * n) src].
Proof.
  induction n as [|n IH]; intros m B HB HH H.
  - exists []. apply rw_cells_CB0. lia.
  - destruct (IH m B HB ltac:(lia) (fun i Hi => H i ltac:(lia))) as [src HS]. destruct (H n ltac:(lia)) as [w C].
    exists (src ++ le8 w). replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
    eapply rw_cells_CB_join; [exact HS|]. replace (B + Z.of_nat (8 * n)) with (B + 8 * Z.of_nat n) by lia.
    eapply rw_cells_recast; [exact C| change (length (le8 w) = 8%nat /\ True); split; [apply length_le8| exact I]| reflexivity| reflexivity].
Qed.

Lemma cells_read_back : forall m m' B A' (n N : nat) src tail (i : nat) (w : word),
  rw_cells usegs m B [CB (8 * n) src] -> rw_cells usegs m (B + 8 * Z.of_nat i) [C8 w] -> (i < n)%nat ->
  rw_cells usegs m' A' [CB N (src ++ tail)] ->
  rw_cells usegs m' (A' + 8 * Z.of_nat i) [C8 w].
Proof.
  intros m m' B A' n N src tail i w HS C Hi HS'.
  pose proof (rw_cells_CB_length usegs m B _ _ HS) as LS. pose proof (rw_cells_CB_length usegs m' A' _ _ HS') as LN. rewrite length_app in LN.
  (* [comment removed for export] *)
  assert (E : firstn 8 (skipn (8 * i) src) = le8 w).
  { pose proof (rw_cells_bytes_at usegs m B _ HS) as BS. cbn [cells_bytes cbytes] in BS. rewrite app_nil_r in BS.
    pose proof (rw_cells_bytes_at usegs m _ _ C) as BC. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC.
    rewrite <- (firstn_skipn (8 * i) src) in BS. apply bytes_at_app in BS. destruct BS as [_ BS]. rewrite firstn_length, Nat.min_l in BS by lia.
    rewrite <- (firstn_skipn 8 (skipn (8 * i) src)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    replace (B + Z.of_nat (8 * i)) with (B + 8 * Z.of_nat i) in BS by lia.
    apply (bytes_at_inj m (B + 8 * Z.of_nat i)); [exact BS| exact BC|]. rewrite firstn_length, skipn_length, length_le8. lia. }
  destruct (rw_cells_CB_split_at usegs m' A' N (src ++ tail) (8 * i) ltac:(lia) HS') as [_ S2].
  destruct (rw_cells_CB_split_at usegs m' (A' + Z.of_nat (8 * i)) (N - 8 * i) (skipn (8 * i) (src ++ tail)) 8 ltac:(lia) S2) as [S3 _].
  replace (A' + Z.of_nat (8 * i)) with (A' + 8 * Z.of_nat i) in S3 by lia.
  eapply rw_cells_recast; [exact S3| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes]. f_equal.
  rewrite skipn_app, firstn_app, skipn_length. replace (8 - (length src - 8 * i))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. symmetry. exact E.
Qed.



(* [comment removed for export] *)
Lemma cells_zero : forall m A (n i : nat), rw_cells usegs m A [CB (8 * n) (repeat (Z_to_bv 8 0) (8 * n))] -> (i < n)%nat ->
  rw_cells usegs m (A + 8 * Z.of_nat i) [C8 (Z_to_bv 64 0)].
Proof.
  intros m A n i HS Hi.
  destruct (rw_cells_CB_split_at usegs m A (8 * n) (repeat (Z_to_bv 8 0) (8 * n)) (8 * i) ltac:(lia) HS) as [_ S2].
  destruct (rw_cells_CB_split_at usegs m (A + Z.of_nat (8 * i)) (8 * n - 8 * i) (skipn (8 * i) (repeat (Z_to_bv 8 0) (8 * n))) 8 ltac:(lia) S2) as [S3 _].
  replace (A + Z.of_nat (8 * i)) with (A + 8 * Z.of_nat i) in S3 by lia.
  eapply rw_cells_recast; [exact S3| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes]. f_equal.
  rewrite firstn_skipn_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lh_raw (DV : Z -> Prop) (m : mem) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb na : Z) (bks : list (list (bptr * Z))) : Prop :=
  cown LBall L pl lh 104 104 /\ (0 < lh /\ lh + 104 <= alloc_ceiling)
  /\ cown LBall L pb B (8 * na) nmb /\ (0 < B /\ B + 8 * na <= alloc_ceiling)
  /\ Z.of_nat (length bks) = na
  /\ (forall i, 0 <= i < na -> chain DV m LBall L (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ List.NoDup (pl :: pb :: map fst (concat bks)).

Lemma lh_rep_raw : forall DV m LBall L f lh pl pb B nmb g bks, lh_rep DV m LBall L f lh pl pb B nmb g bks -> lh_raw DV m LBall L lh pl pb B nmb (g_na g) bks.
Proof. intros DV m LBall L f lh pl pb B nmb g bks (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND). unfold lh_raw. auto 10. Qed.

Lemma lh_rep_of_raw : forall DV m LBall L f lh pl pb B nmb g bks, lh_raw DV m LBall L lh pl pb B nmb (g_na g) bks -> lh_geo_ok g ->
  (exists x40 x48 err pad, rw_cells usegs m lh (lh_cells f B g x40 x48 err pad)) ->
  (forall i, g_nn g <= i < g_na g -> nth (Z.to_nat i) bks [] = []) ->
  lh_rep DV m LBall L f lh pl pb B nmb g bks.
Proof. intros DV m LBall L f lh pl pb B nmb g bks (OL & RL & OB & RB & LEN & CH & ND) G SC EMP. unfold lh_rep. auto 12. Qed.

Lemma lh_raw_upd : forall DV m m' LBall L LBall' L' lh pl pb B nmb na bks bks' (J : Z -> Prop),
  lh_raw DV m LBall L lh pl pb B nmb na bks -> (forall i, J i \/ ~ J i) ->
  (forall q A n nm, lh_T pl pb bks q -> cown LBall L q A n nm -> cown LBall' L' q A n nm) ->
  Z.of_nat (length bks') = na ->
  (forall i, 0 <= i < na -> J i -> chain DV m' LBall' L' (B + 8 * i) (nth (Z.to_nat i) bks' [])) ->
  (forall i, 0 <= i < na -> ~ J i -> nth (Z.to_nat i) bks' [] = nth (Z.to_nat i) bks [] /\ agree_on (bucket_fp B bks i) m m') ->
  List.NoDup (pl :: pb :: map fst (concat bks')) ->
  lh_raw DV m' LBall' L' lh pl pb B nmb na bks'.
Proof.
  intros DV m m' LBall L LBall' L' lh pl pb B nmb na bks bks' J (OL & RL & OB & RB & LEN & CH & ND) JDEC HO LEN' CHJ CHO ND'.
  split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|]. split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN'|].
  split; [| exact ND'].
  intros i Hi. destruct (JDEC i) as [HJ|HJ]; [exact (CHJ i Hi HJ)|].
  destruct (CHO i Hi HJ) as [E AG]. rewrite E. eapply chain_agree; [exact (CH i Hi)| exact AG|].
  intros p A Hp. apply HO. right; right. apply in_map_iff. exists (p, A). split; [reflexivity|]. eapply in_nth_concat. exact Hp.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition split_ivs (cp cn : Z) (NS : list (bptr * Z)) : list (Z * Z) := (cp, cp + 8) :: (cn, cn + 8) :: map (fun x => (snd x + 8, snd x + 16)) NS.

Lemma split_ivs_outside : forall cp cn NS a, outside (split_ivs cp cn NS) a <-> ~ split_W cp cn NS a.
Proof.
  intros cp cn NS a. unfold split_ivs, split_W. cbn [outside]. induction NS as [|[p A] NS IH]; cbn [map outside snd].
  - split; [intros (H1 & H2 & _) [H|[H|(p & A & [] & _)]]; tauto| intros H; repeat split; intros X; apply H; tauto].
  - split.
    + intros (H1 & H2 & H3 & H4) [H|[H|(q & Bq & [E|Hq] & Ha)]]; [tauto| tauto| inversion E; subst; tauto|].
      apply (proj1 IH); [repeat split; assumption|]. right; right. exists q, Bq. auto.
    + intros H. split; [intros X; apply H; tauto|]. split; [intros X; apply H; tauto|]. split.
      * intros X. apply H. right; right. exists p, A. split; [left; reflexivity| exact X].
      * assert (H' : ~ ((cp <= a < cp + 8) \/ (cn <= a < cn + 8) \/ exists q Bq, In (q, Bq) NS /\ Bq + 8 <= a < Bq + 16)).
        { intros [X|[X|(q & Bq & Hq & X)]]; apply H; [tauto| tauto| right; right; exists q, Bq; split; [right; exact Hq| exact X]]. }
        exact (proj2 (proj2 (proj2 IH H'))).
Qed.

Lemma split_munch : forall cp cn NS m m', agree_on (fun a => ~ split_W cp cn NS a) m m' -> munch (split_ivs cp cn NS) m m'.
Proof.
  intros cp cn NS m m' AG x Hx. apply split_ivs_outside in Hx. pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
  destruct (AG (bv_unsigned x) XR Hx) as [E _]. rewrite wa_unsigned_id in E. exact E.
Qed.
(* [comment removed for export] *)
Lemma lh_sep_raw : forall s DV m LBall L lh pl pb B nmb na bks, RHEAP s LBall m -> lh_raw DV m LBall L lh pl pb B nmb na bks ->
  (lh + 104 <= B \/ B + 8 * na <= lh)
  /\ (forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * na <= A))
  /\ (forall i j x y, (i < length bks)%nat -> (j < length bks)%nat -> i <> j -> In x (nth i bks []) -> In y (nth j bks []) -> apart24 (snd x) (snd y))
  /\ (forall i, (i < length bks)%nat -> ForallOrdPairs apart24 (map snd (nth i bks []))).
Proof.
  intros s DV m LBall L lh pl pb B nmb na bks HP (OL & RL & OB & RB & LEN & CH & ND).
  inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
  assert (OWN : forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> In (p, A, 24) LBall).
  { intros i p A Hi Hin. assert (IR : 0 <= Z.of_nat i < Z.of_nat (length bks)) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C.
    exact (proj1 (chain_owns _ _ _ _ _ _ C p A Hin)). }
  assert (IDS : forall i p A, In (p, A) (nth i bks []) -> In p (map fst (concat bks))).
  { intros i p A Hin. apply in_map_iff. exists (p, A). split; [reflexivity| eapply in_nth_concat; exact Hin]. }
  split. { eapply (own_apart s LBall m pl lh 104 pb B (8 * Z.of_nat (length bks)) HP); [exact (proj1 OL)| exact (proj1 OB)|]. intros E. apply NI1. left. symmetry. exact E. }
  split. { intros i p A Hi Hin. split.
    - eapply (own_apart s LBall m p A 24 pl lh 104 HP); [exact (OWN i p A Hi Hin)| exact (proj1 OL)|]. intros E. apply NI1. right. subst p. exact (IDS i pl A Hin).
    - eapply (own_apart s LBall m p A 24 pb B (8 * Z.of_nat (length bks)) HP); [exact (OWN i p A Hi Hin)| exact (proj1 OB)|]. intros E. apply NI2. subst p. exact (IDS i pb A Hin). }
  split. { intros i j [p A] [q Bq] Hi Hj NE Hx Hy. cbn [snd]. unfold apart24.
    eapply (own_apart s LBall m p A 24 q Bq 24 HP); [exact (OWN i p A Hi Hx)| exact (OWN j q Bq Hj Hy)|].
    exact (nodup_concat_ne bks i j (p, A) (q, Bq) ND2 NE Hx Hy). }
  intros i Hi. eapply (nodes_fop s LBall m); [exact HP| intros p A Hin; exact (OWN i p A Hi Hin)| exact (nodup_concat_nth bks i ND2)].
Qed.

Lemma bucket_nsep_raw : forall s DV m LBall L lh pl pb B nmb na bks i j, RHEAP s LBall m -> lh_raw DV m LBall L lh pl pb B nmb na bks ->
  0 <= i < na -> 0 <= j < na -> i <> j -> nsep (nth (Z.to_nat i) bks []) (B + 8 * i) (B + 8 * j).
Proof.
  intros s DV m LBall L lh pl pb B nmb na bks i j HP RAW Hi Hj NE.
  destruct (lh_sep_raw _ _ _ _ _ _ _ _ _ _ _ _ HP RAW) as (_ & SN & _ & SF). destruct RAW as (_ & _ & _ & _ & LEN & _).
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  split; [exact (SF _ LI)|]. split; [| lia].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([p A] & E & Hin). cbn [snd] in E. subst X.
  destruct (SN _ p A LI Hin) as [_ SB]. unfold apartc. lia.
Qed.

(* [comment removed for export] *)
Lemma split_raw : forall s DV m m' LBall L lh pl pb B nmb na bks (p nn : Z) stay' moved',
  RHEAP s LBall m -> lh_raw DV m LBall L lh pl pb B nmb na bks ->
  0 <= p < nn -> nn < na -> nth (Z.to_nat nn) bks [] = [] ->
  chain DV m' LBall L (B + 8 * p) stay' -> chain DV m' LBall L (B + 8 * nn) moved' ->
  Permutation (stay' ++ moved') (nth (Z.to_nat p) bks []) ->
  agree_on (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W (B + 8 * p) (B + 8 * nn) (nth (Z.to_nat p) bks []) a)) m m' ->
  lh_raw DV m' LBall L lh pl pb B nmb na (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))
  /\ Permutation (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))) (concat bks).
Proof.
  intros s DV m m' LBall L lh pl pb B nmb na bks p nn stay' moved' HP RAW PR NNA EMP CS CM PM AG.
  destruct (lh_sep_raw _ _ _ _ _ _ _ _ _ _ _ _ HP RAW) as (S_LB & S_N & S_X & S_F).
  pose proof RAW as (OL & RL & OB & RB & LEN & CH & ND).
  assert (LP : (Z.to_nat p < length bks)%nat) by lia. assert (LN : (Z.to_nat nn < length bks)%nat) by lia. assert (NEpn : Z.to_nat p <> Z.to_nat nn) by lia.
  assert (PMC : Permutation (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))) (concat bks)) by (apply concat_lupd2_perm; assumption).
  split; [| exact PMC].
  eapply (lh_raw_upd DV m m' LBall L LBall L lh pl pb B nmb na bks _ (fun i => i = p \/ i = nn) RAW).
  - intros i. lia.
  - intros q A n nm _ X. exact X.
  - rewrite !lupd_length. exact LEN.
  - intros i Hi [-> | ->].
    + rewrite nth_lupd_eq by (rewrite lupd_length; exact LP). exact CS.
    + rewrite nth_lupd_ne by exact NEpn. rewrite nth_lupd_eq by exact LN. exact CM.
  - intros i Hi NJ. assert (LI : (Z.to_nat i < length bks)%nat) by lia.
    split; [rewrite !nth_lupd_ne by lia; reflexivity|].
    eapply agree_on_mono; [exact AG|]. intros a FP. unfold bucket_fp in FP. unfold split_W. intros BAD.
    assert (NP : forall q Aq, In (q, Aq) (nth (Z.to_nat p) bks []) -> (Aq + 24 <= lh \/ lh + 104 <= Aq) /\ (Aq + 24 <= B \/ B + 8 * na <= Aq)) by (intros q Aq Hq; exact (S_N _ q Aq LP Hq)).
    destruct FP as [FP|(q0 & A0 & H0 & FP)].
    + destruct BAD as [BAD|[BAD|[BAD|(q & Aq & Hq & BAD)]]]; try lia. destruct (NP q Aq Hq) as [_ X]. lia.
    + destruct (S_N _ q0 A0 LI H0) as [X1 X2].
      destruct BAD as [BAD|[BAD|[BAD|(q & Aq & Hq & BAD)]]]; try lia.
      assert (X : apart24 (snd (q0, A0)) (snd (q, Aq))) by (apply (S_X (Z.to_nat i) (Z.to_nat p)); try assumption; lia). unfold apart24 in X. cbn [snd] in X. lia.
  - inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
    assert (PMM : Permutation (map fst (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks)))) (map fst (concat bks))) by (apply Permutation_map; exact PMC).
    constructor. { intros [E|X]; [apply NI1; left; exact E| apply NI1; right; eapply Permutation_in; [exact PMM| exact X]]. }
    constructor. { intros X. apply NI2. eapply Permutation_in; [exact PMM| exact X]. }
    eapply Permutation_NoDup; [apply Permutation_sym; exact PMM| exact ND2].
Qed.
(* [comment removed for export] *)
Lemma cl_own_ids : forall LBall LB (L : @clist bptr) q, cl_own LBall LB L -> In q (map fst L) -> In q (map blk_id LBall).
Proof.
  intros LBall LB L q (CLB & PM & E) Hq. rewrite <- E in Hq. eapply Permutation_in; [apply Permutation_sym; apply Permutation_map; exact PM|].
  rewrite map_app. apply in_or_app. left. exact Hq.
Qed.
End WithCeiling0.
