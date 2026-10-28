(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ASec
     ASecFacts ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP AFrameD ARepExt RT_stubs AInstanceF
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1
     ASecRecycle_iface ARecyc1P ACdeallocP ARecGeo F_amerge F_aqrec_iface F_adorec AFreeModel ASF_kit ARepQW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition aqrec_entry : Z := 0x356b4.
Definition aqrec_retpc : Z := 0x35824.     (* [comment removed for export] *)
End CANSEC1.
Notation AQREC_STACK := 1216 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition bqentries (X : list bq) : list (achunk * Z) := qentries (map fst X) (map snd X).
Definition bqslots (X : list bq) : list Z := map (fun x => qb_slot (snd x)) X.
Definition bqlen_ok (x : bq) : Prop := length (qb_ks (snd x)) = length (b_chunks (fst x)).

Lemma bqentries_cons : forall x X, bqentries (x :: X) = combine (b_chunks (fst x)) (qb_ks (snd x)) ++ bqentries X.
Proof. reflexivity. Qed.
Lemma bqentries_app : forall X Y, bqentries (X ++ Y) = bqentries X ++ bqentries Y.
Proof. induction X as [|x X IH]; intros Y; [reflexivity|]. cbn [app]. rewrite !bqentries_cons, IH, app_assoc. reflexivity. Qed.
Lemma bqslots_app : forall X Y, bqslots (X ++ Y) = bqslots X ++ bqslots Y.
Proof. intros. unfold bqslots. apply map_app. Qed.

Lemma combine_app : forall {A B} (l1 l2 : list A) (k1 k2 : list B), length k1 = length l1 ->
  combine (l1 ++ l2) (k1 ++ k2) = combine l1 k1 ++ combine l2 k2.
Proof. induction l1 as [|a l1 IH]; intros l2 [|b k1] k2 LEN; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.

Lemma merge_bq_keeps : forall R cur, Forall bqlen_ok (cur :: R) ->
  let '(l, e) := merge_bq cur R in
     Permutation (bqentries (l ++ e)) (bqentries (cur :: R))
  /\ Permutation (bqslots (l ++ e)) (bqslots (cur :: R))
  /\ Forall bqlen_ok (l ++ e)
  /\ Forall (fun x => b_size (fst x) = Q_BATCH_BYTES /\ b_count (fst x) = 0 /\ b_chunks (fst x) = [] /\ qb_ks (snd x) = []) e
  /\ (Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l)
  /\ batches_bytes (map fst l) + Q_BATCH_BYTES * Z.of_nat (length e) = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur LOK; cbn [merge_bq].
  - cbn [app length Z.of_nat]. split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [exact LOK|]. split; [constructor|].
    split; [intros H; exact H| lia].
  - pose proof (Forall_inv LOK) as L1. pose proof (Forall_inv (Forall_inv_tail LOK)) as L2. pose proof (Forall_inv_tail (Forall_inv_tail LOK)) as L3.
    unfold bqlen_ok in L1, L2.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) ltac:(constructor; [unfold bqlen_ok, bq_merge; cbn; rewrite !length_app; lia| exact L3])).
      destruct (merge_bq (bq_merge cur nx) R) as [l e]. destruct IH as (PE & PS & LO & EM & SZ & BB).
      split; [| split; [| split; [| split; [| split]]]].
      * rewrite bqentries_app, bqentries_cons. cbn [bq_empty fst snd b_chunks qb_ks combine app].
        rewrite <- bqentries_app. eapply Permutation_trans; [exact PE|].
        rewrite !bqentries_cons. cbn [bq_merge fst snd b_chunks qb_ks]. rewrite combine_app by lia.
        rewrite <- !app_assoc. apply Permutation_app_swap_app.
      * rewrite bqslots_app. cbn [bqslots map bq_empty snd qb_slot]. fold (bqslots e). fold (bqslots l).
        eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
        eapply Permutation_trans; [apply perm_skip; rewrite <- bqslots_app; exact PS|].
        cbn [bqslots map bq_merge snd qb_slot]. apply perm_swap.
      * apply Forall_app in LO. destruct LO as [LOl LOe]. apply Forall_app. split; [exact LOl|]. constructor; [| exact LOe]. unfold bqlen_ok, bq_empty. reflexivity.
      * constructor; [| exact EM]. cbn. repeat split; reflexivity.
      * intros SZS. apply SZ. constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZS))].
        cbn [bq_merge fst b_size]. pose proof (Forall_inv SZS) as Z1. pose proof (Forall_inv (Forall_inv_tail SZS)) as Z2. cbn beta in Z1, Z2. lia.
      * cbn [length map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. cbn [bq_merge fst b_size] in BB. unfold Q_BATCH_BYTES in *. lia.
    + specialize (IH nx ltac:(constructor; [exact L2| exact L3])).
      destruct (merge_bq nx R) as [l e]. destruct IH as (PE & PS & LO & EM & SZ & BB).
      split; [| split; [| split; [| split; [| split]]]].
      * cbn [app]. rewrite !bqentries_cons. apply Permutation_app_head. exact PE.
      * cbn [app bqslots map]. apply perm_skip. exact PS.
      * cbn [app]. constructor; [exact L1| exact LO].
      * exact EM.
      * intros SZS. constructor; [exact (Forall_inv SZS)| apply SZ; exact (Forall_inv_tail SZS)].
      * cbn [map app] in BB |- *. rewrite !batches_bytes_cons. rewrite !batches_bytes_cons in BB. unfold Q_BATCH_BYTES in *. lia.
Qed.

Lemma deq_bq_split : forall gl bytes min_size,
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in gl = taken ++ rest /\ bytes2 = bytes - batches_bytes (map fst taken).
Proof.
  induction gl as [|b gl IH]; intros bytes min_size; cbn [deq_bq].
  - cbn. split; [reflexivity| lia].
  - destruct (min_size <? bytes).
    + specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq gl _ _) as [[tk rs] b2]. destruct IH as [E1 E2].
      cbn [app map]. rewrite batches_bytes_cons. split; [rewrite <- E1; reflexivity| lia].
    + cbn. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma qrec_fun_keeps : forall X bytes min_size, Forall bqlen_ok X -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X ->
  bytes = batches_bytes (map fst X) ->
  let '(rest, T, bytes2) := qrec_fun X bytes min_size in
     Permutation (bqentries (rest ++ T)) (bqentries X)
  /\ Permutation (bqslots (rest ++ T)) (bqslots X)
  /\ Forall bqlen_ok (rest ++ T)
  /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest ++ T)
  /\ bytes2 = batches_bytes (map fst rest).
Proof.
  intros X bytes min_size LOK SZ EB. unfold qrec_fun.
  assert (GEN : forall gl ex, Permutation (bqentries (gl ++ ex)) (bqentries X) -> Permutation (bqslots (gl ++ ex)) (bqslots X) ->
             Forall bqlen_ok (gl ++ ex) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (gl ++ ex) ->
             batches_bytes (map fst gl) + Q_BATCH_BYTES * Z.of_nat (length ex) = bytes ->
             let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
             let '(rest0, T, bytes0) := (rest, ex ++ taken, bytes2) in
             Permutation (bqentries (rest0 ++ T)) (bqentries X) /\ Permutation (bqslots (rest0 ++ T)) (bqslots X) /\ Forall bqlen_ok (rest0 ++ T)
             /\ Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (rest0 ++ T) /\ bytes0 = batches_bytes (map fst rest0)).
  { intros gl ex PE PS LO SZS BB.
    pose proof (deq_bq_split gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size) as DS.
    destruct (deq_bq gl _ min_size) as [[taken rest] bytes2]. destruct DS as [EGL EB2]. subst gl.
    assert (P3 : forall {A} (a b c : list A), Permutation (b ++ (c ++ a)) ((a ++ b) ++ c)).
    { intros A a b c. rewrite (app_assoc b c a). eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite app_assoc. apply Permutation_refl. }
    split; [| split; [| split; [| split]]].
    - eapply Permutation_trans; [| exact PE]. rewrite !bqentries_app. apply P3.
    - eapply Permutation_trans; [| exact PS]. rewrite !bqslots_app. apply P3.
    - rewrite !Forall_app in LO |- *. tauto.
    - rewrite !Forall_app in SZS |- *. tauto.
    - rewrite map_app, batches_bytes_app in BB. unfold Q_BATCH_BYTES, bq in *. lia. }
  destruct (qrec_mergeb (Z.of_nat (length X)) bytes).
  - destruct X as [|cur R].
    + cbn. repeat split; try apply Permutation_refl; try constructor. cbn in EB. lia.
    + unfold amerge_fun. pose proof (merge_bq_keeps R cur LOK) as MK. destruct (merge_bq cur R) as [l e]. destruct MK as (PE & PS & LO & EM & SZl & BB).
      assert (SZ2 : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (l ++ e)).
      { apply Forall_app. split; [exact (SZl SZ)|]. eapply Forall_impl; [| exact EM]. cbn beta. intros x (E & _). rewrite E. lia. }
      pose proof (GEN l e PE PS LO SZ2 ltac:(rewrite EB; exact BB)) as G. revert G.
      destruct (deq_bq l _ min_size) as [[taken rest] bytes2]. intros G. exact G.
  - pose proof (GEN X [] ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; apply Permutation_refl) ltac:(rewrite app_nil_r; exact LOK)
                  ltac:(rewrite app_nil_r; exact SZ) ltac:(cbn [length Z.of_nat]; lia)) as G. revert G.
    cbn [length Z.of_nat Z.mul]. destruct (deq_bq X _ min_size) as [[taken rest] bytes2]. cbn [app]. intros G. exact G.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_fst_combine' : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.
Lemma map_snd_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map snd (combine l l') = l'.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

Lemma tfirst_qfirst : forall L X, tfirst L X 0 = qfirst L (map snd X).
Proof. intros L [|x X]; reflexivity. Qed.
Lemma tlast_qlast : forall L X, tlast L X 0 = qlast L (map snd X).
Proof. intros L X. unfold tlast, qlast, qaddrs, baddr. rewrite map_map. reflexivity. Qed.

Lemma chain_bqlen : forall L m X nxt, chain L m X nxt -> Forall bqlen_ok X.
Proof.
  intros L m X. induction X as [|x X IH]; intros nxt CH; [constructor|].
  unfold chain in CH. cbn [map abatches_to] in CH. destruct CH as [AC CH]. constructor; [| eapply IH; exact CH].
  destruct AC as (_ & _ & _ & _ & LEN & _). exact LEN.
Qed.

Lemma map_fst_bqentries : forall X, Forall bqlen_ok X -> map fst (bqentries X) = flat_map b_chunks (map fst X).
Proof.
  induction X as [|x X IH]; intros LOK; [reflexivity|]. rewrite bqentries_cons, map_app. cbn [map flat_map].
  pose proof (Forall_inv LOK) as L1. unfold bqlen_ok in L1. rewrite (map_fst_combine' (b_chunks (fst x)) (qb_ks (snd x)) L1). rewrite IH by exact (Forall_inv_tail LOK). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma deq_bq_stop : forall gl bytes min_size, bytes = batches_bytes (map fst gl) -> Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) gl -> 0 <= min_size ->
  let '(taken, rest, bytes2) := deq_bq gl bytes min_size in (min_size <? bytes2) = false.
Proof.
  induction gl as [|b gl IH]; intros bytes min_size EB SZ M0; cbn [deq_bq].
  - cbn in EB. apply Z.ltb_ge. lia.
  - destruct (min_size <? bytes) eqn:E; [| exact E].
    specialize (IH (bytes - b_size (fst b)) min_size ltac:(cbn [map] in EB; rewrite batches_bytes_cons in EB; lia) (Forall_inv_tail SZ) M0).
    destruct (deq_bq gl _ _) as [[tk rs] b2]. exact IH.
Qed.

(* [comment removed for export] *)
Lemma recycle_eq : forall {RT} st X0 min_size (K : astate -> AM RT),
  map fst X0 = a_qglob st -> a_qglob_bytes st = batches_bytes (a_qglob st) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0 -> Forall bqlen_ok X0 -> 0 <= min_size ->
  let '(rest, T, bytes2) := qrec_fun X0 (a_qglob_bytes st) min_size in
  recycle st min_size K = do_recycle (set_qglob (map fst rest) bytes2 st) (map fst T) K.
Proof.
  intros RT st X0 min_size K EX NB SZ LOK M0.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB, EX; reflexivity)) as KP.
  unfold qrec_fun in KP |- *. unfold recycle. rewrite <- EX, length_map.
  assert (OV : (a_qglob_bytes st <? Q_BATCH_BYTES * Z.of_nat (length X0)) = false).
  { apply Z.ltb_ge. rewrite NB, <- EX. pose proof (batches_bytes_lb (map fst X0) ltac:(apply Forall_map; exact SZ)) as LB. rewrite length_map in LB. lia. }
  rewrite OV.
  replace ((Q_BATCH_BYTES * Z.of_nat (length X0) <? a_qglob_bytes st) && (a_qglob_bytes st * 100 <? Q_BATCH_BYTES * Z.of_nat (length X0) * 200))
    with (qrec_mergeb (Z.of_nat (length X0)) (a_qglob_bytes st)) by reflexivity.
  destruct X0 as [|cur R].
  { (* [comment removed for export] *)
    cbn [map] in EX. assert (B0 : a_qglob_bytes st = 0) by (rewrite NB, <- EX; reflexivity). rewrite B0 in *.
    clear KP. destruct (qrec_mergeb _ _); cbn -[Z.ltb do_recycle set_qglob aundef_ Q_BATCH_BYTES];
      (* [comment removed for export] *)
      try change (Z.of_nat 0) with 0%Z; rewrite ?Z.mul_0_r, ?Z.sub_0_r;
      replace (min_size <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
  unfold bq in *.   (* [comment removed for export] *)
  destruct (qrec_mergeb (Z.of_nat (length (cur :: R))) (a_qglob_bytes st)) eqn:EMB; rewrite ?EMB in KP |- *.
  - cbn [map]. unfold amerge_fun in *. pose proof (merge_bq_fst R cur) as MF. pose proof (merge_bq_keeps R cur LOK) as MK.
    destruct (merge_batches (fst cur) (map fst R)) as [[l ex] exb]. destruct (merge_bq cur R) as [l2 e2]. cbn [fst snd] in MF, KP |- *.
    destruct MF as (<- & <- & ->). destruct MK as (_ & _ & LO2 & EM & SZ2 & BB).
    assert (SZl : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l2) by (apply SZ2; exact SZ).
    assert (EBl : a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2) = batches_bytes (map fst l2)) by (rewrite NB, <- EX; cbn [map] in BB |- *; unfold Q_BATCH_BYTES, bq in *; lia).
    pose proof (deq_bq_stop l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size EBl SZl M0) as STOP.
    pose proof (deq_bq_fst l2 (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length e2)) min_size) as DF.
    destruct (deq_bq l2 _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP. rewrite map_app. reflexivity.
  - replace (a_qglob_bytes st - 0) with (a_qglob_bytes st) by lia.
    replace (a_qglob_bytes st - Q_BATCH_BYTES * Z.of_nat (length (@nil (abatch * qbatchc)))) with (a_qglob_bytes st) in KP |- * by (cbn [length Z.of_nat]; lia).
    pose proof (deq_bq_stop (cur :: R) (a_qglob_bytes st) min_size ltac:(rewrite NB, EX; reflexivity) SZ M0) as STOP.
    pose proof (deq_bq_fst (cur :: R) (a_qglob_bytes st) min_size) as DF.
    destruct (deq_bq (cur :: R) _ min_size) as [[taken rest] bytes2]. rewrite DF, STOP. cbn [app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma AREP_qglob : forall AQ AQ' AS AS' ADp AFp L st X m g gb,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L (set_qglob g gb st) X m -> (AS L st X m -> AS' L (set_qglob g gb st) X m) ->
  AREP (mkAHoles AQ' AS' ADp AFp) L (set_qglob g gb st) X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m g gb (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
Lemma disj_objs_img : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply ARepQP.disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := ARecyc1P.AHr ASECc AD AF.
(* [comment removed for export] *)
Definition AHq (R : qrconc) (mc mr : Z) (cs : list achunk) : aholes := mkAHoles (AQdr R mc mr) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
Hypothesis QREC : qrec_front_stmt.
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1a1bc8 <= a < 0x5f1c10) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
(* [comment removed for export] *)
Hypothesis ASECc_qglob : forall cs L st X X' m g gb, ASECc cs L st X m -> ASECc cs L (set_qglob g gb st) X' m.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

Lemma HLq : forall R mc mr cs, ahole_laws (AHq R mc mr cs).
Proof.
  intros R mc mr cs. destruct (HL R cs) as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHq AHr ARecyc1P.AHr] in *; try assumption.
  intros L st st' X X' m m' W AQ MU WM UT QS. eapply AQdr_frame; eassumption.
Qed.

(* [comment removed for export] *)
Definition aqrec_ret (L : alayout) (RNG : footprint) (LB : list ablock)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (R : qrconc) (lo min_size : Z) (m : amem)
    (st1 : astate) (X1 : aconc) (RNG1 : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 R1,
    ms' = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m1 (seg_rom bsegs)
    /\ fp_le RNG RNG1 /\ arng L RNG1 st1
    /\ qr_tmp R1 = [] /\ qr_pendb R1 = [] /\ qr_pend R1 = [] /\ qr_loc R1 = qr_loc R
    /\ AREP (AHq R1 0 0 (csx st1 R1)) L st1 X1 m1 /\ ablocks L st1 X1 LB /\ AF L LB m1
    /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp)
    /\ munch [(0, bv_unsigned sp)]%Z m m1 /\ cpres L (bv_unsigned sp) LB m m1
    /\ a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st
    /\ a_nres st1 = a_nres st /\ a_ptr_array st1 = a_ptr_array st /\ a_space_beg st1 = a_space_beg st
    /\ a_qglob_bytes st1 <= min_size.

Theorem aqrec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint) (LB : list ablock) (R : qrconc) (X : aconc) (st : astate) (m : amem) (lo min_size : Z) (cbs : word)
    (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  alayout_ok L -> arng L RNG st -> AREP (AHq R 0 1 (csx st R)) L st X m ->
  qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  ablocks L st X LB -> AF L LB m -> mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) ->
  ATOP <= lo -> lo <= bv_unsigned sp - AQREC_STACK -> bv_unsigned sp <= 2^47 ->
  a_qglob_bytes st < 2^56 -> 0 <= min_size < 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st1 X1 RNG1 ms', aqrec_ret L RNG LB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st R lo min_size m st1 X1 RNG1 ms' ->
     implS bsegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (recycle st min_size K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 min_size) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 aqrec_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT K Q L RNG LB R X st m lo min_size cbs ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
  intros ALO ARNG AR ET EB EP BL HF MI ST CEIL LO SP47 GB56 MIN RSTK KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. atop_facts.
  pose proof AR as AR0. destruct AR0 as (WF & _ & _ & _ & _ & HQ & HS & _). cbn [ah_quar ah_sec AHq] in HQ, HS.
  pose proof HQ as HQ0. destruct HQ0 as (QC & MX & TC & GL & TB & IA & CP & NUM & NT).
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & NDB & BS & _ & NN).
  pose proof NUM as (NB1 & NB2 & NF).
  destruct GL as [GH GA].
  set (X0 := combine (a_qglob st) (qr_glob R)).
  assert (EX1 : map fst X0 = a_qglob st) by (subst X0; apply map_fst_combine'; exact LN2).
  assert (EX2 : map snd X0 = qr_glob R) by (subst X0; apply map_snd_combine; exact LN2).
  assert (CH : chain L m X0 0) by (unfold chain; rewrite EX1, EX2; exact GA).
  pose proof (chain_bqlen L m X0 0 CH) as LOK.
  assert (SZ : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X0).
  { apply Forall_app in NF. destruct NF as [_ NFg]. rewrite <- EX1 in NFg. clear -NFg. induction X0; [constructor|]. inversion NFg; subst. constructor; [assumption| apply IHX0; assumption]. }
  (* [comment removed for export] *)
  pose proof (recycle_eq st X0 min_size K EX1 NB2 SZ LOK (proj1 MIN)) as ME.
  pose proof (qrec_fun_keeps X0 (a_qglob_bytes st) min_size LOK SZ ltac:(rewrite NB2, EX1; reflexivity)) as KP.
  destruct (qrec_fun X0 (a_qglob_bytes st) min_size) as [[rest T] bytes2] eqn:EQF.
  destruct KP as (PE & PS & LOK2 & SZ2 & EB2). rewrite ME. clear ME.
  (* [comment removed for export] *)
  assert (XB : forall x, In x X0 -> exists bb, In bb (x_busy X) /\ xb_st bb = BBatch /\ xb_class bb = K_BATCH_CLASS /\ xb_slot bb = qb_slot (snd x)).
  { intros x Hx. apply (qcoupled_rec_bslot_busy L st X R _ CP). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (GEO : Forall (bgeom L AQ_GCACHE (bv_unsigned sp - 80)) X0).
  { apply Forall_forall. intros x Hx. destruct (XB x Hx) as (bb & Hb & Sb & Cb & Kb).
    pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & _ & _ & _ & G4 & G5 & _). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
    unfold bgeom, baddr, abatch_addr, AIMG_HI, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. lia. }
  assert (SL0 : Forall (fun x => 0 <= qb_slot (snd x)) X0).
  { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) NN). unfold qr_bslots. apply in_app_iff. left. rewrite !map_app.
    apply in_app_iff. right. apply in_app_iff. left. rewrite <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
  assert (NDX : List.NoDup (bqslots X0)).
  { unfold bqslots. rewrite <- (map_map snd qb_slot), EX2. unfold qr_bslots in NDB. rewrite !map_app in NDB.
    apply NoDup_app_remove_r in NDB. apply NoDup_app_remove_l in NDB. apply NoDup_app_remove_r in NDB. exact NDB. }
  assert (LEN40 : Z.of_nat (length X0) < 2^40).
  { pose proof (nodup_range_len (qr_bslots R) (Z.to_nat 458752) NDB) as LEN.
    assert (HFB : Forall (fun k => 0 <= k < Z.of_nat (Z.to_nat 458752)) (qr_bslots R)).
    { apply Forall_forall. intros k Hk. destruct (proj1 (BS k) Hk) as (bb & Hb & Sb & Cb & Kb).
      pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & KR & G1 & G2 & (_ & G3 & _) & _). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
      unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
    specialize (LEN HFB). unfold qr_bslots in LEN. rewrite length_app, !length_map, !length_app, length_map, <- EX2, length_map in LEN. clear -LEN. lia. }
  assert (RB : Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X0).
  { apply Forall_forall. intros x Hx. destruct (XB x Hx) as (bb & Hb & Sb & Cb & Kb).
    pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & G1 & G2 & (_ & G3 & _) & _). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3.
    destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _).
    unfold baddr, abatch_addr, Q_BATCH_BYTES. eapply rng_sub; [exact RR1| clear -G1; lia| clear -G2 G3; lia]. }
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & _).
  rewrite <- EX1, <- EX2, length_map, <- tfirst_qfirst, <- tlast_qlast in GH.
  (* [comment removed for export] *)
  unfold aqrec_entry. iprefix. eapply evtF_cut.
  { eapply (QREC L RNG X0 (a_qglob_bytes st) min_size lo); try eassumption; try reflexivity;
      try lazymatch goal with
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => clear -LO; lia
      | |- rw_cells _ _ AQ_MUTEX _ => exact MX
      | |- _ = batches_bytes _ => rewrite EX1; exact NB2
      | |- _ (map _ X0) => first [exact NDX| apply (proj2 (NoDup_ListNoDup (bqslots X0))); exact NDX| apply (proj1 (NoDup_ListNoDup (bqslots X0))); exact NDX]
      end.
    all: match goal with |- ?G => idtac "REMQ" G end. all: fail. }
  cbv beta. intros ms1 PQ. unfold qrec_front_post in PQ. rewrite EQF in PQ.
  destruct PQ as (t0' & t1' & t2' & xs0 & xs1 & xs2 & xs3 & xs4 & a0' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & tbw & m2
                  & -> & MUq & WMq & MI2 & ST2 & TH2 & SAV2 & MX2 & GH2 & CHr & CHt & EB2' & BLE).
  rewrite <- EB2 in *. clear EB2'.
  (* [comment removed for export] *)
  set (R2 := mkQR (qr_loc R) (map snd rest) (qr_ia R) T [] [] (qr_qpend R)).
  set (stD := set_qglob (map fst rest) bytes2 st).
  set (Wq := ([(bv_unsigned sp - 96, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X0)%Z) in *.
  assert (DJQ : forall A n, A + n <= AIMG_HI -> (A + n <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A) -> disjoint_from Wq A n).
  { intros A n H1 H2. subst Wq. apply disjoint_from_app; [| eapply disj_objs_img; [exact GEO| exact H1]].
    cbn [disjoint_from app]. unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE in *. clear -H1 H2 CEIL LO. repeat split; lia. }
  (* [comment removed for export] *)
  assert (DJL : forall q, In q (qr_loc R) -> disjoint_from Wq (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. subst Wq. apply disjoint_from_app.
    - destruct (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) as (bb & Hb & Sb & Cb & Kb).
      pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & _ & _ & _ & G4 & G5 & _). unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5.
      cbn [disjoint_from app]. unfold abatch_addr, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES in *. clear -G4 G5 CEIL LO. repeat split; lia.
    - apply ARepQP.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
      assert (NE : qb_slot (snd x) <> qb_slot q).
      { intros E. destruct (in_split _ _ Hq) as (l1 & l2 & EL). pose proof NDB as ND0. unfold qr_bslots in ND0. rewrite EL, !map_app in ND0. cbn [map] in ND0.
        rewrite <- !app_assoc in ND0. cbn [app] in ND0.
        apply (List.NoDup_remove_2 _ _ _ ND0). apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
        rewrite <- E, <- EX2, map_map. apply in_map_iff. exists x. split; [reflexivity| exact Hx]. }
      pose proof (proj1 (Forall_forall _ _) SL0 x Hx) as S1. pose proof (proj1 (Forall_forall _ _) NN (qb_slot q) ltac:(unfold qr_bslots; apply in_app_iff; left; rewrite !map_app; apply in_app_iff; left; apply in_map; exact Hq)) as S2.
      cbn beta in S1, S2. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
      destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot q)); [left| right]; nia. }
  (* [comment removed for export] *)
  assert (HQ2 : AQdr R2 0 0 L stD X m2).
  { unfold AQdr. subst R2 stD. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob a_space_beg].
    split. { eapply cells_frame; [exact QC| exact MUq| exact WMq|]. cbn [cells_size csize Nat.add]. apply DJQ; unfold AQ_MAX, AIMG_HI, AQ_MUTEX; clear; lia. }
    split; [exact MX2|].
    split. { eapply (aqcache_frame L Wq m m2 MUq WMq); [exact TC| | exact DJL].
             pose proof (alayout_t L ALO) as (TL1 & TL2 & _ & TL4u). unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
             subst Wq. apply disjoint_from_app.
             - cbn [disjoint_from app]. unfold aq_tcache, AQ_MUTEX, AQ_GCACHE in *. clear -TL4u TL2 CEIL LO. repeat split; lia.
             - apply ARepQP.disjoint_from_Forall. apply Forall_map. apply Forall_forall. intros x Hx. cbn [fst snd].
               destruct (XB x Hx) as (bb & Hb & Sb & Cb & Kb). pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & _ & _ & _ & _ & _ & G6 & G7).
               unfold xb_alloc in G6, G7. rewrite Cb, Kb in G6. rewrite Cb, Kb, size_of_class_24 in G7.
               pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTR. unfold baddr, abatch_addr, aq_tcache, Q_BATCH_BYTES. clear -G6 G7 DTR. lia. }
    split. { split; [| exact CHr]. rewrite length_map, <- tfirst_qfirst, <- tlast_qlast. exact GH2. }
    split; [exact CHt|].
    split. { eapply (aintal_frame Wq m m2 MUq WMq); [exact IA| |]; apply DJQ; unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIMG_HI, AQ_MUTEX, AQ_GCACHE; clear; lia. }
    split. { eapply qcoupled_rec_perm; [exact CP| exact LN1| cbn [qr_glob a_qglob set_qglob]; rewrite !length_map; reflexivity| | | reflexivity].
             - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend a_qloc a_qglob set_qglob]. rewrite ET, EP. cbn [map qentries]. rewrite !List.app_nil_r.
               apply Permutation_app_head. fold (bqentries rest). fold (bqentries T). rewrite <- bqentries_app.
               eapply Permutation_trans; [exact PE|]. unfold bqentries. rewrite EX1, EX2. apply Permutation_refl.
             - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map]. rewrite !List.app_nil_r, !map_app.
               apply Permutation_app_head. rewrite !map_map. change (map (fun x : abatch * qbatchc => qb_slot (snd x)) rest ++ map (fun x => qb_slot (snd x)) T) with (bqslots rest ++ bqslots T).
               rewrite <- bqslots_app. eapply Permutation_trans; [exact PS|]. unfold bqslots. rewrite <- EX2, map_map. apply Permutation_refl. }
    split. { unfold qnumR. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_qglob]. split; [exact NB1|]. split; [first [exact EB2| reflexivity]|].
             apply Forall_app in NF. destruct NF as [NFl _]. apply Forall_app. split; [exact NFl|].
             apply Forall_app in SZ2. destruct SZ2 as [SZr _]. clear -SZr. induction rest as [|y rest' IHr]; [constructor|]. inversion SZr; subst. constructor; [assumption| apply IHr; assumption]. }
    unfold qnum_tmp. apply Forall_app in SZ2. destruct SZ2 as [_ SZt]. clear -SZt. induction T as [|y T' IHt]; [constructor|]. inversion SZt; subst. constructor; [assumption| apply IHt; assumption]. }
  (* [comment removed for export] *)
  assert (QWP : Forall (qwp L X) Wq).
  { subst Wq. apply Forall_app. split.
    - repeat (apply Forall_cons || apply Forall_nil); unfold qwp; cbn [fst snd]; intros _;
        unfold AQ_MUTEX, AQ_GCACHE; [left; clear -CEIL LO; lia| right; left; clear; lia| right; left; clear; lia].
    - apply Forall_map. apply Forall_forall. intros x Hx. unfold qwp. cbn [fst snd]. intros _. right; right.
      destruct (XB x Hx) as (bb & Hb & Sb & Cb & Kb). exists bb. split; [exact Hb|]. split; [exact Sb|].
      unfold xb_alloc, baddr, abatch_addr. rewrite Cb, Kb, size_of_class_24. unfold Q_BATCH_BYTES. clear; lia. }
  (* [comment removed for export] *)
  assert (ESX : csx st R = sec_chunks_of st ++ []).
  { unfold csx, inflight, secsT. rewrite ET, EP. reflexivity. }
  assert (PCSX : Permutation (csx st R) (csx stD R2)).
  { rewrite ESX, List.app_nil_r. unfold csx, inflight, secsT. subst R2 stD. cbn [qr_tmp qr_pend]. change (esecs []) with (@nil achunk). rewrite List.app_nil_r.
    unfold sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob set_qglob]. rewrite !flat_map_app_chunks, !filter_is_sec_app, <- !app_assoc.
    apply Permutation_app_head. apply Permutation_app_head.
    rewrite <- EX1, <- (map_fst_bqentries X0 LOK).
    pose proof LOK2 as LOK3. apply Forall_app in LOK3. destruct LOK3 as [LOKr LOKt]. rewrite <- (map_fst_bqentries rest LOKr).
    change (List.filter is_sec (map fst (bqentries X0))) with (esecs (bqentries X0)).
    change (List.filter is_sec (map fst (bqentries rest))) with (esecs (bqentries rest)).
    rewrite <- esecs_app. fold (bqentries T).   (* [comment removed for export] *)
    rewrite <- bqentries_app. apply esecs_perm. apply Permutation_sym. exact PE. }
  assert (AR2 : AREP (AHr R2 (csx stD R2)) L stD X m2).
  { unfold AHr, ARecyc1P.AHr.
    pose proof (AREP_frame_qw (AQdr R 0 1) (ASECc (csx st R)) AD AF (HLq R 0 1 (csx st R))
                  (fun L' s X' m' => AQdr R2 0 0 L' (set_qglob (map fst rest) bytes2 s) X' m') L st X m m2 Wq ALO AR MUq WMq QWP HQ2) as A1.
    subst stD. eapply AREP_qglob; [exact A1| exact HQ2| intros HS1; eapply ASECc_perm; [exact PCSX| eapply ASECc_qglob; exact HS1]]. }
  assert (ARNG2 : arng L RNG stD).
  { eapply (arng_sub L RNG st stD); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros ch Hch. assert (IN2 : In ch (csx stD R2)) by (unfold csx; apply in_app_iff; left; exact Hch).
    pose proof (Permutation_in _ (Permutation_sym PCSX) IN2) as IN1. rewrite ESX, List.app_nil_r in IN1. exact IN1. }
  assert (RS2 : RSEC (inflight R2) RNG).
  { pose proof (RSEC_arng L RNG st ARNG) as R0. rewrite <- (List.app_nil_r (sec_chunks_of st)), <- ESX in R0.
    pose proof (RSEC_perm' _ _ _ PCSX R0) as R1. unfold csx in R1. apply (proj1 (RSEC_app _ _ _)) in R1. exact (proj2 R1). }
  assert (BL2 : ablocks L stD X LB) by (eapply ablocks_same; [exact BL| reflexivity| reflexivity]).
  assert (HF2 : AF L LB m2).
  { eapply (hf_frame _ (HL R (csx st R)) L LB m m2 Wq); [exact HF| exact MUq| exact WMq|].
    subst Wq. unfold fake_untouched. apply Forall_app. split.
    - pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD. pose proof atop_range as ATR.   (* [comment removed for export] *)
      assert (SF : 2148256256 <= shad (al_fake L) /\ shad (al_fake L) + 11571200 / 8 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF in *; clear -OF ATR; Z.div_mod_to_equations; lia).
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold AQ_MUTEX, AQ_GCACHE in *; rewrite ?shlen_div; clear -CEIL LO OF OD SF ATR; repeat split; lia.
    - apply Forall_map. apply Forall_forall. intros x Hx. destruct (XB x Hx) as (bb & Hb & Sb & Cb & Kb).
      pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & G1 & G2 & (G3a & G3 & G3b) & _). unfold xb_alloc in G1, G2. rewrite Cb, Kb in G1. rewrite Cb, Kb, size_of_class_24 in G2. rewrite Cb in G3, G3a, G3b.
      eapply (wpiece_fake L ATOP ATOP); [exact ALO| apply Z.le_refl|]. unfold wpiece. right; right; right. cbn [fst snd].
      unfold baddr, abatch_addr, Q_BATCH_BYTES, K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      clear -G1 G2 G3 G3a G3b. lia. }
  pose proof (alayout_t L ALO) as (TL1 & TL2 & _).
  (* [comment removed for export] *)
  apply evtF_done.
  set (spD := Z_to_bv 64 (bv_unsigned sp - 80) : word).
  assert (USD : bv_unsigned spD = bv_unsigned sp - 80) by (subst spD; rewrite Z_to_bv_unsigned; apply Z.mod_small; unfold bv_modulus; clear -SPR CEIL LO; lia).
  eapply (adorec ASECc AD AF RSEC HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng
            L lo (bv_unsigned sp - 80) (bv_unsigned sp) LB cbs RNG m2 stD (Z_to_bv 64 aqrec_retpc) spD gp xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 F fc);
    rewrite ?USD;
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- ATOP <= _ => atop_facts; exact CEIL
    | |- lo <= _ => clear -LO; lia
    | |- _ <= 2 ^ 47 => clear -SP47 CEIL LO; lia
    | |- bv_unsigned sp - 80 <= bv_unsigned sp - 80 => apply Z.le_refl
    | |- bv_unsigned sp - 80 + 32 <= bv_unsigned sp => clear; lia
    | |- rng _ lo _ => eapply rng_sub; [exact RSTK| clear; lia| clear; lia]
    | |- rng _ (bv_unsigned sp - 80) _ => eapply rng_sub; [exact RSTK| clear -CEIL LO; lia| clear -CEIL LO; lia]
    | |- arng _ _ _ => exact ARNG2
    | |- AREP _ _ _ _ _ => exact AR2
    | |- ablocks _ _ _ _ => exact BL2
    | |- AF _ _ _ => exact HF2
    | |- RSEC _ _ => exact RS2
    | |- qr_tmp _ = _ => reflexivity
    | |- qr_pendb _ = _ => reflexivity
    | |- qr_pend _ = _ => reflexivity
    | |- mem_inv _ _ => exact MI2
    | |- stk _ _ _ _ => exact ST2
    | |- rw_cells _ _ _ (thdr _ _ _) => unfold thdr; rewrite <- tfirst_qfirst, <- tlast_qlast; exact TH2
    end.
  (* [comment removed for export] *)
  intros st3 X3 RNG3 m3 tb' t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c INV3 ST3 TH3.
  pose proof INV3 as (ARNG3 & AR3 & BL3 & HF3 & RS3 & MI3 & ST3' & FLE3 & MU3 & CP3 & SK3).
  rewrite USD in MU3. unfold thdr in TH3. cbn [length map qfirst qlast qaddrs hd List.last Z.of_nat] in TH3.
  pose proof (cells_frameD _ _ _ _ _ SAV2 MU3 ltac:(cbn [cells_size csize Nat.add disjoint_from]; clear; lia)) as SAV3.
  replace (ret_pc (Z_to_bv 64 aqrec_retpc)) with (Z_to_bv 64 aqrec_retpc : word) by (symmetry; apply ret_pc_even; [unfold aqrec_retpc; lia| reflexivity]).
  unfold aqrec_retpc. subst spD.
  assert (RSTK3 : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FLE3| exact RSTK]).
  assert (FRR : rw_cells bsegs m3 (bv_unsigned sp - 80) ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 tb'] ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact TH3|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp - 80 + Z.of_nat 32) with (bv_unsigned sp - 48) by (clear; lia). exact SAV3. }
  clear TH3 SAV3. cbn [app] in FRR.
  iprefix.
  do 6 step.                                  (* [comment removed for export] *)
  zstep.                                      (* [comment removed for export] *)
  setreg 2 sp ltac:(replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
  step.                                       (* [comment removed for export] *)
  release_frame FRR ST3 (bv_unsigned sp).
  apply evtF_done. eapply KONT. unfold aqrec_ret.
  exists t0c, t1c, t2c, a0c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, m3, (qr_done R2).
  split; [reflexivity|].
  split; [intros bb j Hb; apply FLE3, Hb|]. split; [exact ARNG3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact AR3|]. split; [exact BL3|]. split; [exact HF3|]. split; [exact MI3|]. split; [exact ST3|].
  split. { (* [comment removed for export] *)
    eapply munch_trans; [| eapply munch_weaken; [| exact MU3]; unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; split; [clear -Hx; lia| split; [clear -Hx SPR CEIL LO; lia| exact I]]].
    eapply munch_weaken; [| exact MUq]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. subst Wq.
    apply outside_of_In. intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - cbn [In] in Hiv. unfold AQ_MUTEX, AQ_GCACHE in *. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd]; clear -Hx CEIL LO SPR; lia.
    - apply in_map_iff in Hiv. destruct Hiv as (y & <- & Hy). cbn [fst snd]. pose proof (proj1 (Forall_forall _ _) GEO y Hy) as (G1 & G2 & _).
      unfold AIMG_HI, Q_BATCH_BYTES in *. clear -Hx G1 G2 CEIL LO SPR. lia. }
  split. { (* [comment removed for export] *)
    eapply cpres_trans; [| exact CP3]. eapply cpres_of_munch; [exact MUq|]. subst Wq. apply np_fp_app.
    - intros iv Hiv. cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[]]]]; cbn [fst snd].
      + eapply (np_high L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| apply Z.le_refl].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_MUTEX in *; clear -Ha; lia| unfold AQ_MUTEX; clear; lia| unfold AQ_MUTEX, AIMG_HI; clear; lia].
      + eapply (np_static L st X LB); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| intros a Ha; unfold astatic, AINSTANCE, AQ_GCACHE in *; clear -Ha; lia| unfold AQ_GCACHE; clear; lia| unfold AQ_GCACHE, AIMG_HI; clear; lia].
    - intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (y & <- & Hy). cbn [fst snd]. destruct (XB y Hy) as (bb & Hb & Sb & Cb & Kb).
      destruct (in_split _ _ Hb) as (l1 & l2 & EXB). destruct bb as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
      intros a Ha. eapply (np_slot L st X LB (bv_unsigned sp) BBatch K_BATCH_CLASS (qb_slot (snd y)) bn bb1 bctx l1 l2);
        [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO SPR; lia| exact EXB| intros p; discriminate| | | exact Ha];
        unfold baddr, abatch_addr; [apply Z.le_refl| rewrite size_of_class_24; unfold Q_BATCH_BYTES; apply Z.le_refl]. }
  destruct SK3 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). subst stD. cbn [a_live a_next a_qloc a_qloc_bytes a_nres a_ptr_array a_space_beg set_qglob] in K1, K2, K3, K4, K5, K6, K7, K8, K9.
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
  cbn [a_qglob_bytes set_qglob] in K6. rewrite K6. exact BLE.
Qed.
End QRec.
End CANSEC2.
