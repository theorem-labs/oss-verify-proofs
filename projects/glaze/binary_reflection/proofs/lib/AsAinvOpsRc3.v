(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition op_drain_top (st : ast) (c m : Z) : ast :=
  let ks := a_cache st c in let r := a_reg st c in
  let j := Z.to_nat (Z.of_nat (length ks) - m) in
  set_cache (set_reg st c (REG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r) (r_free r ++ skipn j ks) (r_uhole r) (r_fhole r))) c (firstn j ks).

Definition op_qitem (st : ast) : ast :=
  match a_gq st with
  | BATCH ba (_ :: its) :: rest => set_gq st (BATCH ba its :: rest)
  | _ => st
  end.
Definition op_recycle_prim (st : ast) (c k : Z) : ast := op_cache_push (op_qitem st) c k.
Definition op_recycle_sec (st : ast) (i : nat) : ast := op_sec_free (op_qitem st) i.
Definition op_qbatch_free (spacebeg : Z) (st : ast) (i : nat) : ast :=
  match nth_error (a_gq st) i with
  | Some b => set_cache (set_gq st (firstn i (a_gq st) ++ skipn (S i) (a_gq st))) BATCHCLASS
                        (a_cache st BATCHCLASS ++ [compact_of spacebeg BATCHCLASS (ba_addr b)])
  | None => st
  end.

(* [comment removed for export] *)
Lemma ba_bytes_ge : forall b, (forall m n, In (m, n) (ba_items b) -> 0 <= n) -> BATCHSZ <= ba_bytes b.
Proof.
  intros [a its] H. (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end). cbn [ba_items] in *. induction its as [|[m n] t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [fold_right snd] in G in change_no_check G' end); [lia|].
  pose proof (H m n (or_introl eq_refl)). assert (BATCHSZ <= BATCHSZ + fold_right (fun it acc => snd it + acc) 0 t) by (apply IH; intros m' n' Hin; apply (H m' n'); right; exact Hin). lia.
Qed.

Lemma q_bytes_ge : forall q, (forall b m n, In b q -> In (m, n) (ba_items b) -> 0 <= n) -> BATCHSZ * Z.of_nat (length q) <= q_bytes q.
Proof.
  induction q as [|b t IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right length] in G in change_no_check G' end). fold (q_bytes t).
  pose proof (ba_bytes_ge b (fun m n Hin => H b m n (or_introl eq_refl) Hin)).
  assert (BATCHSZ * Z.of_nat (length t) <= q_bytes t) by (apply IH; intros b0 m n Hb; apply (H b0 m n); right; exact Hb).
  unfold BATCHSZ in *. lia.
Qed.

(* [comment removed for export] *)
Definition part5 (CV P1 P2 P3 P4 P5 : Z -> Prop) : Prop :=
  (forall a, CV a <-> (P1 a \/ P2 a \/ P3 a \/ P4 a \/ P5 a))
  /\ (forall a, ~ (P1 a /\ P2 a)) /\ (forall a, ~ (P1 a /\ P3 a)) /\ (forall a, ~ (P1 a /\ P4 a))
  /\ (forall a, ~ (P2 a /\ P3 a)) /\ (forall a, ~ (P2 a /\ P4 a)) /\ (forall a, ~ (P3 a /\ P4 a))
  /\ (forall a, P5 a -> ~ (P1 a \/ P2 a \/ P3 a \/ P4 a)).
(* [comment removed for export] *)
Lemma part5_move : forall (CV P1 P2 P3 P4 P5 P1' P2' P3' P4' P5' : Z -> Prop) ab,
  part5 CV P1 P2 P3 P4 P5 ->
  (forall a, a <> ab -> (P1' a <-> P1 a) /\ (P2' a <-> P2 a) /\ (P3' a <-> P3 a) /\ (P4' a <-> P4 a) /\ (P5' a <-> P5 a)) ->
  CV ab -> (P1' ab \/ P2' ab \/ P3' ab \/ P4' ab \/ P5' ab) ->
  ~ (P1' ab /\ P2' ab) -> ~ (P1' ab /\ P3' ab) -> ~ (P1' ab /\ P4' ab) -> ~ (P2' ab /\ P3' ab) -> ~ (P2' ab /\ P4' ab) -> ~ (P3' ab /\ P4' ab) ->
  (P5' ab -> ~ (P1' ab \/ P2' ab \/ P3' ab \/ P4' ab)) ->
  part5 CV P1' P2' P3' P4' P5'.
Proof.
  intros CV P1 P2 P3 P4 P5 P1' P2' P3' P4' P5' ab (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) E CVab ONE N12 N13 N14 N23 N24 N34 N5.
  (lazymatch goal with |- ?G => let G' := eval unfold part5 in G in change_no_check G' end).
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [am_tauto|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2, E3, E4, E5. exact (H1 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N12|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2. exact (H2 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N13|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E3. exact (H3 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N14|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E4. exact (H4 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N23|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E2, E3. exact (H5 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N24|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E2, E4. exact (H6 a). }
  split. { intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N34|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E3, E4. exact (H7 a). }
  intros a. destruct (Z.eq_dec a ab) as [-> | NE]; [exact N5|]. destruct (E a NE) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2, E3, E4, E5. exact (H8 a).
Qed.
Lemma part5_ext : forall (CV P1 P2 P3 P4 P5 P1' P2' P3' P4' P5' : Z -> Prop),
  part5 CV P1 P2 P3 P4 P5 ->
  (forall a, (P1' a <-> P1 a) /\ (P2' a <-> P2 a) /\ (P3' a <-> P3 a) /\ (P4' a <-> P4 a) /\ (P5' a <-> P5 a)) ->
  part5 CV P1' P2' P3' P4' P5'.
Proof.
  intros CV P1 P2 P3 P4 P5 P1' P2' P3' P4' P5' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) E. (lazymatch goal with |- ?G => let G' := eval unfold part5 in G in change_no_check G' end).
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2, E3, E4, E5. exact (H1 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2. exact (H2 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E3. exact (H3 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E4. exact (H4 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E2, E3. exact (H5 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E2, E4. exact (H6 a). }
  split. { intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E3, E4. exact (H7 a). }
  intros a. destruct (E a) as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2, E3, E4, E5. exact (H8 a).
Qed.

(* [comment removed for export] *)
Lemma NoDup_fst_inj : forall (l : list (Z * Z)) a b b', List.NoDup (map fst l) -> In (a, b) l -> In (a, b') l -> b = b'.
Proof.
  intros l a b b' ND H1 H2. pose proof (AsAinvFrame3.NoDup_map_inj fst l (a, b) (a, b') ND H1 H2 eq_refl) as E. injection E as E. exact E.
Qed.
Lemma swap_remove_perm : forall {A} (l : list A) i s, nth_error l i = Some s -> Permutation (s :: swap_remove l i) l.
Proof.
  intros A l i s H. (lazymatch goal with |- ?G => let G' := eval unfold swap_remove in G in change_no_check G' end). destruct (rev l) as [|lst r'] eqn:ER.
  - assert (l = []) by (rewrite <- (rev_involutive l), ER; reflexivity). subst l. destruct i; discriminate H.
  - assert (EL : l = rev r' ++ [lst]) by (rewrite <- (rev_involutive l), ER; reflexivity).
    set (l' := rev r') in *. destruct (Nat.ltb_spec i (length l')) as [LT | GE].
    + rewrite EL in H. rewrite nth_error_app1 in H by exact LT.
      rewrite EL. rewrite <- (firstn_skipn i l') at 3.
      assert (SK : skipn i l' = s :: skipn (S i) l').
      { clear -H. revert i H. induction l' as [|x t IH]; intros i H; [destruct i; discriminate H|].
        destruct i as [|i]; [cbn in H; injection H as ->; reflexivity|]. cbn in H. (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end). exact (IH i H). }
      rewrite SK. rewrite <- app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end).
      apply Permutation_cons_app. apply Permutation_app_head. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). apply Permutation_cons_append.
    + rewrite EL in H. rewrite nth_error_app2 in H by exact GE.
      destruct (i - length l')%nat as [|k]; [| destruct k; discriminate H]. cbn in H. injection H as ->.
      rewrite EL. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RcWF.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma partition_part5 : forall st Lc c, partition_c bt st Lc c <->
    (part5 (carved bt st c) (in_live_c Lc c) (in_quar_c st c) (in_cache_c bt st c) (in_fa_c bt st c) (fun a => c = BATCHCLASS /\ in_batch st a)
     /\ List.NoDup (a_cache st c) /\ List.NoDup (r_free (a_reg st c))).
  Proof using.
    intros st Lc c. (lazymatch goal with |- ?G => let G' := eval unfold partition_c, part5 in G in change_no_check G' end). split.
    - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      split; [| exact (conj H9 H10)]. repeat (split; [assumption|]). intros a [E B]. exact (H8 a B E).
    - intros ((H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) & H9 & H10).
      repeat (split; [assumption|]). split; [| exact (conj H9 H10)]. intros a B E. exact (H8 a (conj E B)).
  Qed.

  (* [comment removed for export] *)
  Lemma cinit_of_carved : forall st Lc FF (qt qg : Z) c a, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> carved bt st c a -> a_cinit st = true.
  Proof using.
    intros st Lc FF qt qg c a W Hc (j & Hj & Hle & _). destruct (a_cinit st) eqn:E; [reflexivity | exfalso].
    pose proof W as (_ & WC & _). destruct (WC c Hc) as (_ & C2 & _). destruct (C2 E) as [_ Z0]. pose proof (csize_pos c Hc) as ((S1 & _) & _). nia.
  Qed.
  Lemma cinit_of_batch : forall st Lc FF (qt qg : Z) b, WFq bt st Lc FF qt qg -> In b (a_tq st ++ a_gq st) -> a_cinit st = true.
  Proof using.
    intros st Lc FF qt qg b W Hb. destruct (batch_facts bt st Lc FF W b Hb) as (CV & _).
    exact (cinit_of_carved st Lc FF qt qg BATCHCLASS (ba_addr b) W ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV).
  Qed.




  (* [comment removed for export] *)
  Theorem OPS_WFq_drain_top_pf : forall st Lc FF c m (qt qg : Z),
    WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> 0 <= m <= Z.of_nat (length (a_cache st c)) ->
    4 * (Z.of_nat (length (r_free (a_reg st c))) + m) <= r_mapped_fa (a_reg st c) ->
    WFq bt (op_drain_top st c m) Lc FF qt qg.
  Proof using.
    intros st Lc FF c m qt qg W Hc Hm0 Hfa.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & WMP & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    destruct (WC c Hc) as (KC1 & KC2 & KC3).
    pose proof (AsAinvOpsR3.split_keep_taken (a_cache st c) m Hm0) as SPL. cbn zeta in SPL.
    set (j := Z.to_nat (Z.of_nat (length (a_cache st c)) - m)) in *.
    set (keep := firstn j (a_cache st c)) in *. set (moved := skipn j (a_cache st c)) in *.
    destruct SPL as (EL & LK & LTk & NK & NT).
    pose proof PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    assert (ND : List.NoDup (keep ++ moved)) by (rewrite <- EL; exact P9).
    (lazymatch goal with |- ?G => let G' := eval unfold WFq, op_drain_top in G in change_no_check G' end). cbn zeta. fold j. fold keep. fold moved.
    (lazymatch goal with |- ?G => let G' := eval unfold set_cache, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    set (st' := AST (fupdZ (a_reg st) c (REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) (r_free (a_reg st c) ++ moved) (r_uhole (a_reg st c)) (r_fhole (a_reg st c))))
                    (a_cinit st) (fupdZ (a_cache st) c keep) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st)).
    assert (CVE : forall c' a, carved bt st' c' a <-> carved bt st c' a).
    { intros c' a. (lazymatch goal with |- ?G => let G' := eval unfold carved, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); am_tauto. }
    assert (WBE : forall b, wf_batch bt st b -> wf_batch bt st' b).
    { intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply CVE; exact B2|]. intros m0 n0 Hmn. destruct (B3 m0 n0 Hmn) as [N [[HP CV] | [HP RG]]].
      - split; [exact N|]. left. split; [exact HP|]. apply CVE. exact CV.
      - split; [exact N|]. right. split; [exact HP|]. exact RG. }
    assert (WQ' : wf_quarantine_q bt st' qt qg).
    { destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (a_gq st). change (quar st') with (quar st).
      split; [eapply Forall_impl; [exact WBE | exact Q1]|]. split; [eapply Forall_impl; [| exact Q2]; intros b0; apply wf_batch0_mono; [intros c0 a0; apply CVE | intros p0 n0 H0; exact H0]|].
      split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5 | exact Q6]. }
    assert (WL' : wf_live bt st' Lc).
    { destruct WL as (L1' & L2' & L3'). (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| split; [exact L2' | exact L3']].
      intros p n Hin. destruct (L1' p n Hin) as (A1 & A2 & A3 & CVL). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      intros HP. apply CVE. exact (CVL HP). }
    assert (WM' : wf_meter st').
    { (* [comment removed for export] *)
      apply (wf_meter_transfer st st' eq_refl eq_refl eq_refl); [| exact WM].
      intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; reflexivity. }
    split; [| split; [| split; [exact WQ' | split; [exact WS | split; [exact WL' | split; [exact WK | split; [exact WD | split; [exact WM' | split; [exact WMP | exact G]]]]]]]]].
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end).
      split; [| intros c' Hc'; destruct (WR2 c' Hc') as [E1 E2]; (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c' c); [lia | split; [exact E1 | exact E2]]].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
      + (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user r_mapped_fa r_free r_fhole] in G in change_no_check G' end). repeat (split; [first [assumption | lia] |]).
        split. { rewrite length_app, Nat2Z.inj_add, LTk. lia. }
        split; [assumption|].
        split. { intros k Hk. apply in_app_iff in Hk. destruct Hk as [Hk | Hk].
                 - destruct (Y9 k Hk) as [A B]. split; [exact A | apply CVE; exact B].
                 - destruct (KC3 k ltac:(rewrite EL; apply in_app_iff; right; exact Hk)) as [A B]. split; [exact A | apply CVE; exact B]. }
        split; [| exact FHK].
        unfold partition_c in *. unfold in_cache_c, in_fa_c, in_batch, carved in *. cbn [a_cache a_reg a_tq a_gq r_alloc_user r_free] in *.
        (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). rewrite Z.eqb_refl. (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user r_free] in G in change_no_check G' end).
        assert (SPLIT : forall a, (exists k, In k (a_cache st c) /\ a = chunk_of_compact SBEG c k) <->
                                  ((exists k, In k keep /\ a = chunk_of_compact SBEG c k) \/ (exists k, In k moved /\ a = chunk_of_compact SBEG c k))).
        { intros a. rewrite EL. split.
          - intros (k & Hk & E). apply in_app_iff in Hk. destruct Hk as [Hk|Hk]; [left | right]; exists k; split; assumption.
          - intros [(k & Hk & E) | (k & Hk & E)]; exists k; (split; [apply in_app_iff | exact E]); [left | right]; exact Hk. }
        assert (FAPP : forall a, (exists k, In k (r_free (a_reg st c) ++ moved) /\ a = chunk_of_compact SBEG c k) <->
                                 ((exists k, In k (r_free (a_reg st c)) /\ a = chunk_of_compact SBEG c k) \/ (exists k, In k moved /\ a = chunk_of_compact SBEG c k))).
        { intros a. split.
          - intros (k & Hk & E). apply in_app_iff in Hk. destruct Hk as [Hk|Hk]; [left | right]; exists k; split; assumption.
          - intros [(k & Hk & E) | (k & Hk & E)]; exists k; (split; [apply in_app_iff | exact E]); [left | right]; exact Hk. }
        split. { intros a. rewrite (P1 a), (SPLIT a), (FAPP a). am_tauto. }
        split; [exact P2|].
        split. { intros a [X Y]. apply (P3 a). split; [exact X|]. apply SPLIT. left. exact Y. }
        split. { intros a [X Y]. apply FAPP in Y. destruct Y as [Y | Y]; [exact (P4 a (conj X Y)) | apply (P3 a); split; [exact X | apply SPLIT; right; exact Y]]. }
        split. { intros a [X Y]. apply (P5 a). split; [exact X|]. apply SPLIT. left. exact Y. }
        split. { intros a [X Y]. apply FAPP in Y. destruct Y as [Y | Y]; [exact (P6 a (conj X Y)) | apply (P5 a); split; [exact X | apply SPLIT; right; exact Y]]. }
        split. { intros a [X Y]. apply FAPP in Y. destruct Y as [Y | Y].
                 - apply (P7 a). split; [apply SPLIT; left; exact X | exact Y].
                 - destruct X as (k & Hk & E). destruct Y as (k' & Hk' & E'). rewrite E in E'. apply (f_equal (compact_of SBEG c)) in E'.
                   rewrite !compact_roundtrip_k in E'. subst k'. exact (AsAinvOpsR3.nodup_split_disj keep moved _ ND Hk Hk'). }
        split. { intros a Hb Hc24 X. apply (P8 a Hb Hc24). destruct X as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | |].
                 - right; right; left. apply SPLIT. left. exact X.
                 - apply FAPP in X. destruct X as [X | X]; [right; right; right; exact X | right; right; left; apply SPLIT; right; exact X]. }
        split; [exact (NoDup_app_remove_r _ _ ND)|].
        apply NoDup_app; [exact P10 | exact (NoDup_app_remove_l _ _ ND) |].
        intros k Hk Hk'. apply (P7 (chunk_of_compact SBEG c k)). split; [exists k; split; [rewrite EL; apply in_app_iff; right; exact Hk' | reflexivity] | exists k; split; [exact Hk | reflexivity]].
      + repeat (split; [assumption|]).
        split. { intros k Hk. destruct (Z9 k Hk) as [A B]. split; [exact A | apply CVE; exact B]. }
        split; [| exact FHK'].
        apply (AsAinvOpsR3.partition_keep bt st st' Lc c'); [exact (CVE c') | reflexivity | reflexivity | | | exact PART'].
        * (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end). apply fupdZ_other. exact NE.
        * (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). rewrite fupdZ_other by exact NE. reflexivity.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end).
      intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_cinit a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
      + split; [rewrite LK; lia|]. split; [intros F; destruct (KC2 F) as [F1 F2]; split; [(lazymatch goal with |- ?G => let G' := eval unfold keep in G in change_no_check G' end); rewrite F1; apply firstn_nil | (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); exact F2]|].
        intros k Hk. destruct (KC3 k ltac:(rewrite EL; apply in_app_iff; left; exact Hk)) as [A B]. split; [exact A | apply CVE; exact B].
      + destruct (WC c' Hc') as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
        intros k Hk. destruct (C3 k Hk) as [A B]. split; [exact A | apply CVE; exact B].
  Qed.

  (* [comment removed for export] *)
  Lemma op_qitem_eq : forall st ba it its rest, a_gq st = BATCH ba (it :: its) :: rest -> op_qitem st = set_gq st (BATCH ba its :: rest).
  Proof using. intros st ba it its rest E. (lazymatch goal with |- ?G => let G' := eval unfold op_qitem in G in change_no_check G' end). rewrite E. reflexivity. Qed.
  Lemma quar_gq_head : forall st ba it its rest, a_gq st = BATCH ba (it :: its) :: rest ->
    quar st = flat_map ba_items (a_tq st) ++ it :: (its ++ flat_map ba_items rest)
    /\ quar (set_gq st (BATCH ba its :: rest)) = flat_map ba_items (a_tq st) ++ (its ++ flat_map ba_items rest).
  Proof using.
    intros st ba it its rest E. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq] in G in change_no_check G' end). rewrite E, !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items] in G in change_no_check G' end). split; reflexivity.
  Qed.
  Lemma in_batch_gq_head : forall st ba it its rest a, a_gq st = BATCH ba (it :: its) :: rest ->
    in_batch (set_gq st (BATCH ba its :: rest)) a <-> in_batch st a.
  Proof using.
    intros st ba it its rest a E. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq] in G in change_no_check G' end). rewrite E. split; intros (b & Hb & Eb);
      apply in_app_iff in Hb; destruct Hb as [Hb | [<- | Hb]].
    - exists b. split; [apply in_app_iff; left; exact Hb | exact Eb].
    - exists (BATCH ba (it :: its)). split; [apply in_app_iff; right; left; reflexivity | exact Eb].
    - exists b. split; [apply in_app_iff; right; right; exact Hb | exact Eb].
    - exists b. split; [apply in_app_iff; left; exact Hb | exact Eb].
    - exists (BATCH ba its). split; [apply in_app_iff; right; left; reflexivity | exact Eb].
    - exists b. split; [apply in_app_iff; right; right; exact Hb | exact Eb].
  Qed.

  Lemma compact_carved_range : forall st Lc FF c a {qt qg : Z}, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> carved bt st c a ->
    0 <= compact_of SBEG c a < 2 ^ 32.
  Proof using.
    intros st Lc FF c a qt qg W Hc CV. destruct (carved_range bt st Lc FF W c a Hc CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof W as ((WR & _) & _). destruct (WR c Hc) as (R1 & _ & R3 & _). pose proof (csize_pos c Hc) as ((S1 & S2) & S3).
    (lazymatch goal with |- ?G => let G' := eval unfold compact_of in G in change_no_check G' end). unfold KREGION_EXHAUST, KUSERMAP in *.
    assert (0 <= (a - region_beg SBEG c) / 16) by (apply Z.div_pos; lia).
    assert ((a - region_beg SBEG c) / 16 < 2 ^ 32) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.

  Theorem OPS_WFq_recycle_prim_pf : forall st Lc FF ba m n its rest c k (qt qg : Z),
    WFq bt st Lc FF qt qg -> a_gq st = BATCH ba ((m, n) :: its) :: rest -> is_primary n = true ->
    c = blk_class n -> k = compact_of SBEG c (prim_alloc_beg (m + 16) n) ->
    Z.of_nat (length (a_cache st c)) < cache_max c ->
    WFq bt (op_recycle_prim st c k) Lc FF qt qg.
  Proof using.
    intros st Lc FF ba m n its rest c k qt qg W Hgq HP Hc Hk HLEN.
    assert (HCI : a_cinit st = true) by (apply (cinit_of_batch st Lc FF qt qg (BATCH ba ((m, n) :: its)) W); apply in_app_iff; right; rewrite Hgq; left; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim in G in change_no_check G' end). rewrite (op_qitem_eq st ba (m, n) its rest Hgq).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & WL & WK & WD & WM & WMP & G).
    destruct (quar_gq_head st ba (m, n) its rest Hgq) as [EQ0 EQ1].
    set (QA := flat_map ba_items (a_tq st)) in *. set (QB := its ++ flat_map ba_items rest) in *.
    assert (Hq : In (m, n) (quar st)) by (rewrite EQ0; apply in_app_iff; right; left; reflexivity).
    pose proof (quar_chunk bt st Lc FF W m n Hq HP) as Gv. cbn zeta in Gv. rewrite <- Hc in Gv. set (ab := prim_alloc_beg (m + 16) n) in *.
    destruct Gv as (Hc30 & CVab & QCab & G4 & G5 & G6).
    assert (N1 : 1 <= n) by (destruct (quar_item bt st Lc FF W m n Hq) as (N & _); lia).
    assert (NDQ : List.NoDup (QA ++ (m, n) :: QB)) by (rewrite <- EQ0; exact (NoDup_map_inv _ _ Q6)).
    set (st1 := set_gq st (BATCH ba its :: rest)) in *.
    assert (INQ : forall x, In x (quar st1) <-> In x (quar st) /\ x <> (m, n)) by (intros x; rewrite EQ0, EQ1; apply in_remove_mid; exact NDQ).
    assert (NM : forall n', ~ In (m, n') (quar st1)).
    { intros n' Hin. apply INQ in Hin. destruct Hin as [Hin NE]. apply NE. f_equal. exact (NoDup_fst_inj (quar st) m n' n Q6 Hin Hq). }
    assert (RT : chunk_of_compact SBEG c k = ab) by (rewrite Hk; exact (carved_roundtrip bt st Lc FF c ab W Hc30 CVab)).
    assert (KR : 0 <= k < 2 ^ 32) by (rewrite Hk; exact (compact_carved_range st Lc FF c ab W Hc30 CVab)).
    pose proof (proj1 (partition_part5 st Lc c) ltac:(destruct (WR1 c Hc30) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & _); exact PART)) as ((P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) & P9 & P10).
    assert (NKC : ~ In k (a_cache st c)).
    { intros Hin. apply (P5 ab). split; [exact QCab | exists k; split; [exact Hin | symmetry; exact RT]]. }
    set (st' := op_cache_push st1 c k).
    assert (HB : forall a, in_batch st' a <-> in_batch st a) by (intros a; exact (in_batch_gq_head st ba (m, n) its rest a Hgq)).
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split; [| split; [| split; [| split; [| split; [exact WL | split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G]]]]]]]]].
    - (* [comment removed for export] *)
      split; [| intros c' Hc'; destruct (WR2 c' Hc') as [E1 E2]; split; [exact E1|]; (lazymatch goal with |- ?G => let G' := eval unfold st', op_cache_push in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c' c); [lia | exact E2]].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c') with (a_reg st c'). do 8 (split; [assumption|]). split; [exact Z9|]. split; [| exact FHK'].
      apply partition_part5. apply partition_part5 in PART'. destruct PART' as (PP & PN1 & PN2).
      change (r_free (a_reg st' c')) with (r_free (a_reg st c')).
      destruct (Z.eq_dec c' c) as [-> | NE].
      + split; [| split; [| exact PN2]].
        * apply (part5_move (carved bt st c) (in_live_c Lc c) (in_quar_c st c) (in_cache_c bt st c) (in_fa_c bt st c) (fun a => c = BATCHCLASS /\ in_batch st a)
                            (in_live_c Lc c) (in_quar_c st' c) (in_cache_c bt st' c) (in_fa_c bt st' c) (fun a => c = BATCHCLASS /\ in_batch st' a) ab PP).
          -- intros a NEa. split; [am_tauto|]. split; [| split; [| split; [am_tauto|]]].
             ++ (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). change (quar st') with (quar st1). split.
                ** intros (m' & n' & Hin & X). exists m', n'. split; [exact (proj1 (proj1 (INQ _) Hin)) | exact X].
                ** intros (m' & n' & Hin & X). exists m', n'. split; [| exact X]. apply INQ. split; [exact Hin|].
                   intros E. injection E as -> ->. apply NEa. destruct X as (_ & _ & X). symmetry. exact X.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, st', op_cache_push in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. change (a_cache st1 c) with (a_cache st c). split.
                ** intros (k' & Hk' & E). apply in_app_iff in Hk'. destruct Hk' as [Hk' | [<- | []]]; [exists k'; split; assumption|].
                   exfalso. apply NEa. rewrite E. exact RT.
                ** intros (k' & Hk' & E). exists k'. split; [apply in_app_iff; left; exact Hk' | exact E].
             ++ rewrite (HB a). am_tauto.
          -- exact CVab.
          -- right; right; left. (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, st', op_cache_push in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. exists k. split; [apply in_app_iff; right; left; reflexivity | symmetry; exact RT].
          -- intros [X _]. exact (P2 ab (conj X QCab)).
          -- intros [X _]. exact (P2 ab (conj X QCab)).
          -- intros [X _]. exact (P2 ab (conj X QCab)).
          -- intros [(m' & n' & Hin & HP' & HC' & HA') _]. change (quar st') with (quar st1) in Hin.
             assert (N1' : 1 <= n') by (destruct (quar_item bt st Lc FF W m' n' (proj1 (proj1 (INQ _) Hin))) as (N & _); lia).
             pose proof (rz_unif n n' N1 N1' HP HP' ltac:(rewrite HC'; symmetry; exact Hc)) as ER.
             assert (m' = m) by (unfold ab, prim_alloc_beg in HA'; clear -HA' ER; lia). subst m'. exact (NM n' Hin).
          -- intros [(m' & n' & Hin & HP' & HC' & HA') _]. change (quar st') with (quar st1) in Hin.
             assert (N1' : 1 <= n') by (destruct (quar_item bt st Lc FF W m' n' (proj1 (proj1 (INQ _) Hin))) as (N & _); lia).
             pose proof (rz_unif n n' N1 N1' HP HP' ltac:(rewrite HC'; symmetry; exact Hc)) as ER.
             assert (m' = m) by (unfold ab, prim_alloc_beg in HA'; clear -HA' ER; lia). subst m'. exact (NM n' Hin).
          -- intros [_ X]. exact (P6 ab (conj QCab X)).
          -- intros [E X]. apply HB in X. exfalso. apply (P8 ab (conj E X)). right; left. exact QCab.
        * (lazymatch goal with |- ?G => let G' := eval unfold st', op_cache_push in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. change (a_cache st1 c) with (a_cache st c).
          apply NoDup_app; [exact P9 | constructor; [intros [] | constructor] |]. intros x Hx [<- | []]. exact (NKC Hx).
      + assert (EC : a_cache st' c' = a_cache st c') by ((lazymatch goal with |- ?G => let G' := eval unfold st', op_cache_push in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end); apply fupdZ_other; exact NE).
        split; [| split; [rewrite EC; exact PN1 | exact PN2]].
        apply (part5_ext _ _ _ _ _ _ _ _ _ _ _ PP). intros a. split; [am_tauto|]. split; [| split; [| split; [am_tauto|]]].
        * (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). change (quar st') with (quar st1). split.
          -- intros (m' & n' & Hin & X). exists m', n'. split; [exact (proj1 (proj1 (INQ _) Hin)) | exact X].
          -- intros (m' & n' & Hin & X). exists m', n'. split; [| exact X]. apply INQ. split; [exact Hin|].
             intros E. injection E as -> ->. apply NE. destruct X as (_ & X & _). rewrite Hc. symmetry. exact X.
        * (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c in G in change_no_check G' end). rewrite EC. am_tauto.
        * rewrite (HB a). am_tauto.
    - (* [comment removed for export] *)
      intros c' Hc'. destruct (WC c' Hc') as (C1 & C2 & C3). (lazymatch goal with |- ?G => let G' := eval unfold st', op_cache_push in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache a_cinit] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
      destruct (Z.eqb_spec c' c) as [-> | NE]; [| exact (conj C1 (conj C2 C3))].
      change (a_cache st1 c) with (a_cache st c). change (a_cinit st1) with (a_cinit st).
      split; [rewrite length_app, Nat2Z.inj_add; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia|]. split; [intros F; rewrite HCI in F; discriminate F|].
      intros k' Hk'. apply in_app_iff in Hk'. destruct Hk' as [Hk' | [<- | []]]; [exact (C3 k' Hk')|]. split; [exact KR|]. rewrite RT. exact CVab.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (BATCH ba its :: rest). change (quar st') with (quar st1).
      rewrite Hgq in Q2, Q4, Q5. inversion Q2 as [| b0 l0 WB0 WBR]; subst.
      split; [exact Q1|].
      split. { constructor; [| exact WBR]. destruct WB0 as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold wf_batch0 in G in change_no_check G' end). cbn [ba_items ba_addr] in B1, B2, B3 |- *. cbn [length] in B1. split; [clear -B1; lia|]. split; [exact B2|].
               intros m' n' Hin. exact (B3 m' n' (or_intror Hin)). }
      split; [exact Q3|].
      split. { cbn [q_bytes fold_right] in Q4 |- *. unfold ba_bytes in *. cbn [ba_items fold_right snd] in *. lia. }
      split; [rewrite map_app in Q5 |- *; exact Q5|].
      rewrite EQ1. rewrite EQ0 in Q6. rewrite map_app in Q6 |- *. cbn [map fst] in Q6. exact (NoDup_remove_1 _ _ _ Q6).
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (a_nres st') with (a_nres st). change (quar st') with (quar st1).
      repeat (split; [assumption|]).
      split. { intros s0 Hs. rewrite (S6 s0 Hs). destruct (S4 s0 Hs) as (N64 & _). split.
               - intros X Y. exact (X (proj1 (proj1 (INQ _) Y))).
               - intros X Y. apply X. apply INQ. split; [exact Y|]. intros E. injection E as E1 E2.
                 apply (is_primary_iff n N1) in HP. lia. }
      split; [exact S7|]. intros m' n' Hin HP'. exact (S8 m' n' (proj1 (proj1 (INQ _) Hin)) HP').
  Qed.

  (* [comment removed for export] *)
  Lemma nth_error_split_fs : forall {A} (l : list A) i x, nth_error l i = Some x ->
    l = firstn i l ++ x :: skipn (S i) l.
  Proof using.
    intros A l. induction l as [|y t IH]; intros i x H; [destruct i; discriminate H|].
    destruct i as [|i]; [cbn in H; injection H as ->; reflexivity|]. cbn in H. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn app] in G in change_no_check G' end). f_equal. exact (IH i x H).
  Qed.

  Theorem OPS_WFq_qbatch_free_pf : forall st Lc FF i ba (qt qg : Z),
    WFq bt st Lc FF qt qg -> nth_error (a_gq st) i = Some (BATCH ba []) ->
    Z.of_nat (length (a_cache st BATCHCLASS)) < cache_max BATCHCLASS ->
    WFq bt (op_qbatch_free SBEG st i) Lc FF qt qg.
  Proof using.
    intros st Lc FF i ba qt qg W Hnth HLEN.
    assert (HCI : a_cinit st = true) by (apply (cinit_of_batch st Lc FF qt qg (BATCH ba []) W); apply in_app_iff; right; exact (nth_error_In _ _ Hnth)).
    (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). rewrite Hnth. (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end).
    pose proof (nth_error_split_fs (a_gq st) i _ Hnth) as Hgq.
    set (G1 := firstn i (a_gq st)) in *. set (G2 := skipn (S i) (a_gq st)) in *.
    set (k := compact_of SBEG BATCHCLASS ba). set (c := BATCHCLASS) in *.
    assert (Hc30 : 1 <= c <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold c, BATCHCLASS in G in change_no_check G' end); lia).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & WL & WK & WD & WM & WMP & G).
    assert (Hb : In (BATCH ba []) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; apply in_app_iff; right; left; reflexivity).
    destruct (batch_facts bt st Lc FF W _ Hb) as (CVab & _). cbn [ba_addr] in CVab. fold c in CVab.
    set (st1 := set_gq st (G1 ++ G2)).
    assert (EQ : quar st1 = quar st).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar, st1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq] in G in change_no_check G' end). rewrite Hgq, !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items app] in G in change_no_check G' end). reflexivity. }
    assert (RT : chunk_of_compact SBEG c k = ba) by (exact (carved_roundtrip bt st Lc FF c ba W Hc30 CVab)).
    assert (KR : 0 <= k < 2 ^ 32) by (exact (compact_carved_range st Lc FF c ba W Hc30 CVab)).
    pose proof (proj1 (partition_part5 st Lc c) ltac:(destruct (WR1 c Hc30) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & _); exact PART)) as ((P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) & P9 & P10).
    assert (INB : in_batch st ba) by (exists (BATCH ba []); split; [exact Hb | reflexivity]).
    pose proof (P8 ba (conj eq_refl INB)) as NONE.
    assert (NKC : ~ In k (a_cache st c)).
    { intros Hin. apply NONE. right; right; left. exists k. split; [exact Hin | symmetry; exact RT]. }
    assert (NDB : List.NoDup (map ba_addr (a_tq st) ++ map ba_addr G1 ++ ba :: map ba_addr G2)).
    { rewrite Hgq, !map_app in Q5. cbn [map ba_addr] in Q5. exact Q5. }
    set (st' := set_cache st1 c (a_cache st c ++ [k])).
    assert (HB : forall a, in_batch st' a <-> in_batch st a /\ a <> ba).
    { intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). change (a_tq st' ++ a_gq st') with (a_tq st ++ G1 ++ G2). rewrite Hgq. rewrite !app_assoc in NDB.
      pose proof (NoDup_remove_2 _ _ _ NDB) as NI. rewrite <- !map_app in NI. split.
      - intros (b & Hin & Eb). split.
        + exists b. split; [| exact Eb]. rewrite !in_app_iff in Hin |- *. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). am_tauto.
        + intros ->. apply NI. rewrite <- Eb. apply in_map. rewrite <- app_assoc. exact Hin.
      - intros [(b & Hin & Eb) NE]. exists b. split; [| exact Eb]. rewrite !in_app_iff in Hin |- *. cbn [In] in Hin.
        destruct Hin as [Hin | [Hin | [<- | Hin]]]; [am_tauto | am_tauto | | am_tauto]. exfalso. apply NE. symmetry. exact Eb. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split; [| split; [| split; [| split; [| split; [exact WL | split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G]]]]]]]]].
    - (* [comment removed for export] *)
      split; [| intros c' Hc'; destruct (WR2 c' Hc') as [E1 E2]; split; [exact E1|]; (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c' c); [lia | exact E2]].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c') with (a_reg st c'). do 8 (split; [assumption|]). split; [exact Z9|]. split; [| exact FHK'].
      apply partition_part5. apply partition_part5 in PART'. destruct PART' as (PP & PN1 & PN2).
      change (r_free (a_reg st' c')) with (r_free (a_reg st c')).
      assert (HQ : forall a, in_quar_c st' c' a <-> in_quar_c st c' a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end); change (quar st') with (quar st1); rewrite EQ; am_tauto).
      destruct (Z.eq_dec c' c) as [-> | NE].
      + split; [| split; [| exact PN2]].
        * apply (part5_move (carved bt st c) (in_live_c Lc c) (in_quar_c st c) (in_cache_c bt st c) (in_fa_c bt st c) (fun a => c = BATCHCLASS /\ in_batch st a)
                            (in_live_c Lc c) (in_quar_c st' c) (in_cache_c bt st' c) (in_fa_c bt st' c) (fun a => c = BATCHCLASS /\ in_batch st' a) ba PP).
          -- intros a NEa. split; [am_tauto|]. split; [exact (HQ a)|]. split; [| split; [am_tauto|]].
             ++ (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. split.
                ** intros (k' & Hk' & E). apply in_app_iff in Hk'. destruct Hk' as [Hk' | [<- | []]]; [exists k'; split; assumption|].
                   exfalso. apply NEa. rewrite E. exact RT.
                ** intros (k' & Hk' & E). exists k'. split; [apply in_app_iff; left; exact Hk' | exact E].
             ++ rewrite (HB a). am_tauto.
          -- exact CVab.
          -- right; right; left. (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. exists k. split; [apply in_app_iff; right; left; reflexivity | symmetry; exact RT].
          -- intros [X _]. apply NONE. left. exact X.
          -- intros [X _]. apply NONE. left. exact X.
          -- intros [X _]. apply NONE. left. exact X.
          -- intros [X _]. apply NONE. right; left. apply HQ. exact X.
          -- intros [X _]. apply NONE. right; left. apply HQ. exact X.
          -- intros [_ X]. apply NONE. right; right; right. exact X.
          -- intros [_ X]. apply HB in X. exfalso. exact (proj2 X eq_refl).
        * (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same.
          apply NoDup_app; [exact P9 | constructor; [intros [] | constructor] |]. intros x Hx [<- | []]. exact (NKC Hx).
      + assert (EC : a_cache st' c' = a_cache st c') by ((lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end); apply fupdZ_other; exact NE).
        split; [| split; [rewrite EC; exact PN1 | exact PN2]].
        apply (part5_ext _ _ _ _ _ _ _ _ _ _ _ PP). intros a. split; [am_tauto|]. split; [exact (HQ a)|]. split; [| split; [am_tauto|]].
        * (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c in G in change_no_check G' end). rewrite EC. am_tauto.
        * split; intros [E _]; exfalso; exact (NE E).
    - (* [comment removed for export] *)
      intros c' Hc'. destruct (WC c' Hc') as (C1 & C2 & C3). (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache a_cinit] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
      destruct (Z.eqb_spec c' c) as [-> | NE]; [| exact (conj C1 (conj C2 C3))].
      change (a_cinit st1) with (a_cinit st).
      split; [rewrite length_app, Nat2Z.inj_add; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia|]. split; [intros F; rewrite HCI in F; discriminate F|].
      intros k' Hk'. apply in_app_iff in Hk'. destruct Hk' as [Hk' | [<- | []]]; [exact (C3 k' Hk')|]. split; [exact KR|]. rewrite RT. exact CVab.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (G1 ++ G2). change (quar st') with (quar st1).
      rewrite Hgq in Q2, Q4. rewrite Forall_app in Q2. destruct Q2 as [Q2a Q2b]. inversion Q2b as [| b0 l0 WB0 WBR]; subst b0 l0.
      split; [exact Q1|].
      split; [rewrite Forall_app; exact (conj Q2a WBR)|].
      split; [exact Q3|].
      split. { rewrite q_bytes_app in Q4 |- *. cbn [q_bytes fold_right] in Q4. fold (q_bytes G2) in Q4. unfold ba_bytes in Q4 at 1. cbn [ba_items fold_right] in Q4. unfold BATCHSZ in Q4. lia. }
      split. { rewrite !map_app. rewrite !app_assoc in NDB |- *. exact (NoDup_remove_1 _ _ _ NDB). }
      rewrite EQ. exact Q6.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (a_nres st') with (a_nres st). change (quar st') with (quar st1). rewrite EQ.
      exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj S7 S8))))))).
  Qed.

  (* [comment removed for export] *)
  Lemma seps_perm : forall x l l', Permutation l l' -> seps x l -> seps x l'.
  Proof using.
    intros x l l' PM Hs. apply seps_of_forall. intros y Hy. apply (AsAinvOpsS3.seps_In x l y Hs). exact (Permutation_in y (Permutation_sym PM) Hy).
  Qed.
  Lemma PW_perm : forall l l', Permutation l l' -> PW l -> PW l'.
  Proof using.
    intros l l' PM. induction PM as [| x l l' PM IH | x y l | l l' l'' PM1 IH1 PM2 IH2]; intros HP.
    - exact I.
    - destruct HP as [Hs Ht]. split; [exact (seps_perm x l l' PM Hs) | exact (IH Ht)].
    - destruct HP as [[Hyx Hy] [Hx Ht]]. (lazymatch goal with |- ?G => let G' := eval cbn [PW seps] in G in change_no_check G' end). split; [split; [lia | exact Hx] | split; [exact Hy | exact Ht]].
    - exact (IH2 (IH1 HP)).
  Qed.

  Lemma sec_user_inj : forall st Lc FF {qt qg : Z} s s', WFq bt st Lc FF qt qg -> In s (a_sec st) -> In s' (a_sec st) -> sc_user s = sc_user s' -> s = s'.
  Proof using.
    intros st Lc FF qt qg s s' W Hs Hs' E. destruct (sec_cases bt st Lc FF W s s' Hs Hs') as [X | X]; [exact X|]. exfalso.
    destruct (sec_facts bt st Lc FF W s Hs) as (_ & _ & _ & _ & A5 & A6 & A7 & _). destruct (sec_facts bt st Lc FF W s' Hs') as (_ & _ & _ & _ & B5 & B6 & B7 & _).
    unfold PG in *. lia.
  Qed.


  Theorem OPS_WFq_recycle_sec_pf : forall st Lc FF ba m n its rest i s (qt qg : Z),
    WFq bt st Lc FF qt qg -> a_gq st = BATCH ba ((m, n) :: its) :: rest -> is_primary n = false ->
    nth_error (a_sec st) i = Some s -> sc_user s = m + 16 ->
    WFq bt (op_recycle_sec st i) Lc FF qt qg.
  Proof using.
    intros st Lc FF ba m n its rest i s qt qg W Hgq HP Hnth Hus.
    (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec in G in change_no_check G' end). rewrite (op_qitem_eq st ba (m, n) its rest Hgq).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & WL & WK & WD & WM & WMP & G).
    destruct (quar_gq_head st ba (m, n) its rest Hgq) as [EQ0 EQ1].
    set (QA := flat_map ba_items (a_tq st)) in *. set (QB := its ++ flat_map ba_items rest) in *.
    assert (Hq : In (m, n) (quar st)) by (rewrite EQ0; apply in_app_iff; right; left; reflexivity).
    assert (N1 : 1 <= n) by (destruct (quar_item bt st Lc FF W m n Hq) as (N & _); lia).
    assert (NDQ : List.NoDup (QA ++ (m, n) :: QB)) by (rewrite <- EQ0; exact (NoDup_map_inv _ _ Q6)).
    set (st1 := set_gq st (BATCH ba its :: rest)) in *.
    assert (INQ : forall x, In x (quar st1) <-> In x (quar st) /\ x <> (m, n)) by (intros x; rewrite EQ0, EQ1; apply in_remove_mid; exact NDQ).
    assert (NM : forall n', ~ In (m, n') (quar st1)).
    { intros n' Hin. apply INQ in Hin. destruct Hin as [Hin NE]. apply NE. f_equal. exact (NoDup_fst_inj (quar st) m n' n Q6 Hin Hq). }
    assert (Hs : In s (a_sec st)) by (exact (nth_error_In _ _ Hnth)).
    assert (Hsn : sc_n s = n).
    { destruct (quar_sec bt st Lc FF W m n Hq HP) as (sc & Hsc & Eu & En). rewrite <- (sec_user_inj st Lc FF sc s W Hsc Hs ltac:(lia)). exact En. }
    set (SR := swap_remove (a_sec st) i).
    pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    assert (NDS : List.NoDup (s :: SR)) by (exact (Permutation_NoDup (Permutation_sym PERM) (NoDup_map_inv _ _ S5))).
    assert (INS : forall x, In x SR <-> In x (a_sec st) /\ x <> s).
    { intros x. split.
      - intros Hx. split; [exact (Permutation_in x PERM (or_intror Hx))|]. intros ->. inversion NDS as [| ? ? NI _]; subst. exact (NI Hx).
      - intros [Hx NE]. destruct (Permutation_in x (Permutation_sym PERM) Hx) as [E | Hx']; [exfalso; exact (NE (eq_sym E)) | exact Hx']. }
    set (st' := op_sec_free st1 i).
    assert (ESEC : a_sec st' = SR) by reflexivity.
    assert (REGT : forall m' n', In (m', n') (quar st1) -> registered st (m' + 16) n' -> registered st' (m' + 16) n').
    { intros m' n' Hin (s0 & Hs0 & Eu0 & En0). exists s0. split; [| exact (conj Eu0 En0)]. rewrite ESEC. apply INS. split; [exact Hs0|].
      intros ->. assert (m' = m) by lia. subst m'. exact (NM n' Hin). }
    assert (HB : forall a, in_batch st' a <-> in_batch st a) by (intros a; exact (in_batch_gq_head st ba (m, n) its rest a Hgq)).
    assert (WM' : wf_meter st').
    { (* [comment removed for export] *)
      destruct WM as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end).
      change (a_kact st') with (a_kact st). change (a_shsec st') with (a_shsec st + 2 * PG). rewrite ESEC. change (a_reg st') with (a_reg st).
      change (sum_mu st') with (sum_mu st).
      pose proof (Permutation_length PERM) as LEN. cbn [length] in LEN.
      split; [exact M1|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear -M2; lia|]. split; [rewrite <- LEN in M3; rewrite Nat2Z.inj_succ in M3; clear -M3; lia|]. split; [exact M4 | exact M5]. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split; [| split; [exact WC | split; [| split; [| split; [exact WL | split; [exact WK | split; [exact WD | split; [exact WM' | split; [| exact G]]]]]]]]].
    - (* [comment removed for export] *)
      split; [| exact WR2].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c') with (a_reg st c'). do 8 (split; [assumption|]). split; [exact Z9|]. split; [| exact FHK'].
      apply partition_part5. apply partition_part5 in PART'. destruct PART' as (PP & PN1 & PN2).
      split; [| exact (conj PN1 PN2)].
      apply (part5_ext _ _ _ _ _ _ _ _ _ _ _ PP). intros a. split; [am_tauto|]. split; [| split; [am_tauto | split; [am_tauto|]]].
      + (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). change (quar st') with (quar st1). split.
        * intros (m' & n' & Hin & X). exists m', n'. split; [exact (proj1 (proj1 (INQ _) Hin)) | exact X].
        * intros (m' & n' & Hin & X). exists m', n'. split; [| exact X]. apply INQ. split; [exact Hin|].
          intros E. injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
      + rewrite (HB a). am_tauto.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (BATCH ba its :: rest). change (quar st') with (quar st1).
      rewrite Hgq in Q2, Q4, Q5. inversion Q2 as [| b0 l0 WB0 WBR]; subst.
      split. { rewrite Forall_forall in Q1 |- *. intros b Hb. destruct (Q1 b Hb) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
               intros m' n' Hin. destruct (B3 m' n' Hin) as (N & [X | [X RG]]); (split; [exact N|]); [left; exact X | right; split; [exact X|]].
               apply REGT; [| exact RG]. rewrite EQ1. apply in_app_iff. left. (lazymatch goal with |- ?G => let G' := eval unfold QA in G in change_no_check G' end). apply in_flat_map. exists b. exact (conj Hb Hin). }
      split. { constructor.
               - destruct WB0 as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold wf_batch0 in G in change_no_check G' end). cbn [ba_items ba_addr] in B1, B2, B3 |- *. cbn [length] in B1. split; [clear -B1; lia|]. split; [exact B2|].
                 intros m' n' Hin. destruct (B3 m' n' (or_intror Hin)) as (N & [X | [X RG]]); (split; [exact N|]); [left; exact X | right; split; [exact X|]].
                 apply REGT; [| exact RG]. rewrite EQ1. apply in_app_iff. right. (lazymatch goal with |- ?G => let G' := eval unfold QB in G in change_no_check G' end). apply in_app_iff. left. exact Hin.
               - rewrite Forall_forall in WBR |- *. intros b Hb. destruct (WBR b Hb) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
                 intros m' n' Hin. destruct (B3 m' n' Hin) as (N & [X | [X RG]]); (split; [exact N|]); [left; exact X | right; split; [exact X|]].
                 apply REGT; [| exact RG]. rewrite EQ1. apply in_app_iff. right. (lazymatch goal with |- ?G => let G' := eval unfold QB in G in change_no_check G' end). apply in_app_iff. right. apply in_flat_map. exists b. exact (conj Hb Hin). }
      split; [exact Q3|].
      split. { cbn [q_bytes fold_right] in Q4 |- *. unfold ba_bytes in *. cbn [ba_items fold_right snd] in *. lia. }
      split; [rewrite map_app in Q5 |- *; exact Q5|].
      rewrite EQ1. rewrite EQ0 in Q6. rewrite map_app in Q6 |- *. cbn [map fst] in Q6. exact (NoDup_remove_1 _ _ _ Q6).
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). rewrite ESEC. change (a_nres st') with (a_nres st). change (quar st') with (quar st1).
      split. { pose proof (Permutation_length PERM) as PL. cbn [length] in PL. lia. }
      split; [exact S2|]. split; [exact S3|].
      split. { intros s0 Hs0. exact (S4 s0 (proj1 (proj1 (INS s0) Hs0))). }
      split. { pose proof (Permutation_NoDup (Permutation_sym (Permutation_map sc_map PERM)) S5) as X. cbn [map] in X. inversion X; assumption. }
      split. { intros s0 Hs0. apply INS in Hs0. destruct Hs0 as [Hs0 NEs]. rewrite (S6 s0 Hs0). split.
               - intros X Y. exact (X (proj1 (proj1 (INQ _) Y))).
               - intros X Y. apply X. apply INQ. split; [exact Y|]. intros E. injection E as E1 E2.
                 apply NEs. apply (sec_user_inj st Lc FF s0 s W Hs0 Hs). lia. }
      split. { intros p n' Hin HP'. destruct (S7 p n' Hin HP') as (s0 & Hs0 & Eu0 & En0). exists s0. split; [| exact (conj Eu0 En0)]. rewrite ESEC. apply INS. split; [exact Hs0|].
               intros ->. apply (proj1 (S6 s Hs)); [rewrite Eu0, En0; exact Hin|]. rewrite Hus, Hsn. replace (m + 16 - 16) with m by lia. exact Hq. }
      intros m' n' Hin HP'. exact (REGT m' n' Hin (S8 m' n' (proj1 (proj1 (INQ _) Hin)) HP')).
    - (* [comment removed for export] *)
      destruct WMP as (M1 & M2 & MREST).
      assert (PMR : Permutation ((sc_map s, sc_map s + sc_mapsz s) :: all_ranges bt st') (all_ranges bt st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite ESEC. change (a_dep st') with (a_dep st).
        set (f := fun s0 : schunk => (sc_map s0, sc_map s0 + sc_mapsz s0)).
        set (DD := map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
        transitivity (bt_fixed bt ++ f s :: map f SR ++ DD); [apply Permutation_middle|].
        apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
        apply Permutation_app_tail. exact (Permutation_map f PERM). }
      split. { intros lo hi Hin. apply (M1 lo hi). exact (Permutation_in _ PMR (or_intror Hin)). }
      destruct MREST as (K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20).
      split; [| do 17 (split; [assumption|]); intros b0 n0 lo hi Hb0 Hin; apply (K20 b0 n0 lo hi Hb0);
                assert (HA : In (lo, hi) (all_ranges bt st)) by (apply (Permutation_in _ PMR); right; (lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); apply in_app_iff; right; exact Hin);
                unfold dyn_ranges in Hin |- *; rewrite ESEC in Hin; change (a_dep st') with (a_dep st) in Hin; rewrite !in_app_iff in Hin |- *;
                destruct Hin as [Hin | Hin]; [left | right; exact Hin];
                apply in_map_iff in Hin; destruct Hin as (s0 & E0 & Hs0); apply in_map_iff; exists s0; split; [exact E0 | exact (proj1 (proj1 (INS s0) Hs0))]].
      apply AsAinvOpsS3.splits_of_PW.
      assert (PWA : PW (all_ranges bt st)).
      { apply PW_of_splits. intros l1 [xlo xhi] l2 [ylo yhi] E Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (M2 l1 l2 xlo xhi ylo yhi E Hy). }
      exact (proj2 (PW_perm _ _ (Permutation_sym PMR) PWA)).
  Qed.

End RcWF.
