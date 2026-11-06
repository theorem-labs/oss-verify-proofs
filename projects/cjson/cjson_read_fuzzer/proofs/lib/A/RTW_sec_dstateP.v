(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_trans.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ck_eqb_eq : forall u v, ck_eqb u v = true <-> u = v.
Proof.
  intros [a b] [c d]. unfold ck_eqb. cbn. rewrite andb_true_iff, !Z.eqb_eq. split; [intros [-> ->]; reflexivity| intros E; injection E as -> ->; auto].
Qed.
Lemma remove_first_In : forall {A} (eqb : A -> A -> bool) x l y, In y (remove_first eqb x l) -> In y l.
Proof.
  induction l as [|z l IH]; intros y H; [exact H|]. cbn in H. destruct (eqb x z); [right; exact H|].
  destruct H as [<-|H]; [left; reflexivity| right; apply IH; exact H].
Qed.
(* [comment removed for export] *)
Lemma remove_first_perm : forall x l, In x l -> Permutation l (x :: remove_first ck_eqb x l).
Proof.
  intros x l. induction l as [|z l IH]; intros H; [destruct H|]. cbn.
  destruct (ck_eqb x z) eqn:E.
  - apply ck_eqb_eq in E. subst z. apply Permutation_refl.
  - destruct H as [->|H]; [exfalso; pose proof (proj2 (ck_eqb_eq x x) eq_refl); congruence|].
    apply Permutation_trans with (z :: x :: remove_first ck_eqb x l); [apply perm_skip; apply IH; exact H| apply perm_swap].
Qed.
Lemma remove_first_filter_true : forall (f : Z * Z -> bool) x l, f x = true ->
  Permutation (List.filter f l) (List.filter f (x :: remove_first ck_eqb x l)) \/ ~ In x l.
Proof.
  intros f x l Hf. destruct (in_dec (fun u v => ltac:(destruct (ck_eqb u v) eqn:E; [left; apply ck_eqb_eq; exact E| right; intros C; apply ck_eqb_eq in C; congruence])) x l) as [I|N].
  - left. apply Permutation_filter'. apply remove_first_perm. exact I.
  - right. exact N.
Qed.
Lemma filter_remove_first_false : forall (f : Z * Z -> bool) x l, f x = false ->
  List.filter f (remove_first ck_eqb x l) = List.filter f l.
Proof.
  intros f x l Hf. induction l as [|z l IH]; [reflexivity|]. cbn. destruct (ck_eqb x z) eqn:E.
  - apply ck_eqb_eq in E. subst z. rewrite Hf. reflexivity.
  - cbn. destruct (f z); [rewrite IH; reflexivity| exact IH].
Qed.
Lemma NoDup_remove_first : forall x (l : list (Z * Z)), List.NoDup l -> List.NoDup (remove_first ck_eqb x l).
Proof.
  intros x l ND. induction l as [|z l IH]; [constructor|]. inversion ND as [|z' l' Hni ND']; subst. cbn. destruct (ck_eqb x z).
  - exact ND'.
  - constructor; [| apply IH; exact ND']. intros C. apply Hni. eapply remove_first_In. exact C.
Qed.

Lemma remove_first_nodup_notin : forall x (l : list (Z * Z)), List.NoDup l -> ~ In x (remove_first ck_eqb x l).
Proof.
  intros x l ND. induction l as [|z l IH]; intros HIn; [exact HIn|]. inversion ND as [|z' l' Hni ND']; subst. cbn in HIn.
  destruct (ck_eqb x z) eqn:EQ.
  - apply ck_eqb_eq in EQ. subst z. exact (Hni HIn).
  - destruct HIn as [->|HIn]; [pose proof (proj2 (ck_eqb_eq x x) eq_refl); congruence| exact (IH ND' HIn)].
Qed.

Lemma perm_move_front : forall (x : Z) L L' Q R T, Permutation L (x :: L') ->
  Permutation (L ++ Q ++ R ++ T) (L' ++ Q ++ (x :: R) ++ T).
Proof.
  intros x L L' Q R T P. apply Permutation_trans with ((x :: L') ++ Q ++ R ++ T); [apply Permutation_app_tail; exact P|].
  change ((x :: L') ++ Q ++ R ++ T) with (x :: (L' ++ Q ++ R ++ T)).
  rewrite (app_assoc L' Q (R ++ T)). change (L' ++ Q ++ (x :: R) ++ T) with (L' ++ Q ++ x :: (R ++ T)). rewrite (app_assoc L' Q (x :: R ++ T)).
  apply Permutation_middle.
Qed.

Lemma zsum_map_perm : forall (f : Z * Z -> Z) l l', Permutation l l' -> zsum (map f l) = zsum (map f l').
Proof. intros f l l' H. apply zsum_perm. apply Permutation_map. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TR.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.

(* [comment removed for export] *)
Section LIVEP.
Variables (c k A n : Z).
Let stL := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 ((A, n) :: LB) (remove_first ck_eqb (c, k) AP) SP QP b4 b5.
Hypothesis HP : bprim n = true.
Hypothesis HC : c = pclass n.
Hypothesis HIN : In (c, k) AP.
Hypothesis HA : A = cptr_addr st c k + rz_size n.
Hypothesis HN : 0 <= n < 2^40.
Hypothesis HNA : forall A' n', In (A', n') (all_blocks st) -> A' <> A.

Lemma liveP_c_range : 1 <= c <= 30.
Proof. rewrite HC. exact (proj1 (prim_facts n HP)). Qed.
Lemma liveP_bcptr : b_cptr stL A n = k.
Proof.
  unfold b_cptr, b_alloc_beg. rewrite HA, <- HC. unfold cptr_addr, rbeg. cbn [st_spacebeg st stL].
  replace (region_beg a3 c + 16 * k + rz_size n - rz_size n - region_beg a3 c) with (k * 16) by lia. apply Z.div_mul. lia.
Qed.
Lemma liveP_all_blocks : all_blocks stL = (A, n) :: all_blocks st. Proof. reflexivity. Qed.
Lemma liveP_qelems : qelems stL = qelems st. Proof. reflexivity. Qed.
Lemma liveP_qall : qall stL = qall st. Proof. reflexivity. Qed.
Lemma liveP_rg : forall c', rg stL c' = rg st c'. Proof. reflexivity. Qed.
Lemma liveP_cch : forall c', cch stL c' = cch st c'. Proof. reflexivity. Qed.
Lemma liveP_avail : forall c', avail_cptrs stL c' = avail_cptrs st c'. Proof. reflexivity. Qed.
Lemma liveP_navail : forall c', navail stL c' = navail st c'. Proof. reflexivity. Qed.
Lemma liveP_ncarved : forall c', ncarved stL c' = ncarved st c'. Proof. reflexivity. Qed.
Lemma liveP_quar : forall c', quar_cptrs stL c' = quar_cptrs st c'. Proof. reflexivity. Qed.
Lemma liveP_qpend : forall c', qpend_cptrs stL c' = qpend_cptrs st c'. Proof. reflexivity. Qed.
Lemma liveP_batch : forall c', batch_cptrs stL c' = batch_cptrs st c'. Proof. reflexivity. Qed.
Lemma liveP_cptr_addr : forall c' j, cptr_addr stL c' j = cptr_addr st c' j. Proof. reflexivity. Qed.
Lemma liveP_live_same : live_cptrs stL c = k :: live_cptrs st c.
Proof.
  unfold live_cptrs, lb_prim. cbn [st_lb stL st]. cbn [List.filter snd]. rewrite HP, <- HC, Z.eqb_refl. cbn [andb map fst snd].
  rewrite liveP_bcptr. f_equal.
Qed.
Lemma liveP_live_other : forall c', c' <> c -> live_cptrs stL c' = live_cptrs st c'.
Proof.
  intros c' Hc'. unfold live_cptrs, lb_prim. cbn [st_lb stL st]. cbn [List.filter snd]. rewrite HP. cbn [andb].
  destruct (Z.eqb_spec (pclass n) c'); [exfalso; subst; lia| reflexivity].
Qed.
Lemma liveP_apend_same : Permutation (apend_cptrs st c) (k :: apend_cptrs stL c).
Proof.
  unfold apend_cptrs. cbn [st_apend st stL].
  destruct (remove_first_filter_true (fun ck => fst ck =? c) (c, k) AP ltac:(cbn; apply Z.eqb_refl)) as [P|N]; [| exfalso; exact (N HIN)].
  cbn [List.filter fst] in P. rewrite Z.eqb_refl in P. cbn [map snd] in P.
  exact (Permutation_map snd P).
Qed.
Lemma liveP_apend_other : forall c', c' <> c -> apend_cptrs stL c' = apend_cptrs st c'.
Proof.
  intros c' Hc'. unfold apend_cptrs. cbn [st_apend st stL]. rewrite filter_remove_first_false; [reflexivity|]. cbn. apply Z.eqb_neq. lia.
Qed.
Lemma liveP_used_same : Permutation (used_cptrs stL c) (used_cptrs st c).
Proof.
  unfold used_cptrs. rewrite liveP_avail, liveP_live_same, liveP_quar, liveP_qpend, liveP_batch.
  set (AV := avail_cptrs st c). set (L := live_cptrs st c). set (Q := quar_cptrs st c). set (QP' := qpend_cptrs st c). set (BT := batch_cptrs st c).
  apply Permutation_trans with (AV ++ (k :: L) ++ Q ++ QP' ++ BT ++ apend_cptrs stL c); [apply Permutation_refl|].
  apply Permutation_trans with (AV ++ L ++ Q ++ QP' ++ BT ++ k :: apend_cptrs stL c).
  - apply Permutation_app_head. change ((k :: L) ++ Q ++ QP' ++ BT ++ apend_cptrs stL c) with (k :: (L ++ Q ++ QP' ++ BT) ++ apend_cptrs stL c) || idtac.
    rewrite !app_assoc. rewrite <- (app_assoc ((L ++ Q) ++ QP') BT). rewrite <- !app_assoc.
    (* [comment removed for export] *)
    replace ((k :: L) ++ Q ++ QP' ++ BT ++ apend_cptrs stL c) with (k :: (L ++ Q ++ QP' ++ BT) ++ apend_cptrs stL c) by (cbn; rewrite <- !app_assoc; reflexivity).
    replace (L ++ Q ++ QP' ++ BT ++ k :: apend_cptrs stL c) with ((L ++ Q ++ QP' ++ BT) ++ k :: apend_cptrs stL c) by (rewrite <- !app_assoc; reflexivity).
    apply Permutation_middle.
  - repeat apply Permutation_app_head. apply Permutation_sym. exact liveP_apend_same.
Qed.
Lemma liveP_used_other : forall c', c' <> c -> used_cptrs stL c' = used_cptrs st c'.
Proof.
  intros c' Hc'. unfold used_cptrs. rewrite liveP_avail, liveP_live_other, liveP_quar, liveP_qpend, liveP_batch, liveP_apend_other by exact Hc'. reflexivity.
Qed.
Lemma liveP_k_carved : carved_cptr st c k /\ 0 <= k.
Proof.
  pose proof liveP_c_range as CR.
  pose proof (wf_class_ok st WF c ltac:(unfold KNUMCLASSES; lia)) as WC.
  assert (IN : In k (used_cptrs st c)).
  { unfold used_cptrs. rewrite !in_app_iff. do 5 right. unfold apend_cptrs. cbn [st_apend st]. apply in_map_iff. exists (c, k). split; [reflexivity|].
    apply filter_In. split; [exact HIN| cbn; apply Z.eqb_refl]. }
  pose proof (wc_used_carved st c WC k IN) as CV. split; [exact CV|].
  destruct CV as (j & Hj & ->). unfold chunk_cptr. apply Z.div_pos; [| lia]. pose proof (csize_pos c ltac:(lia)). nia.
Qed.

Lemma RTWF_liveP : RTWF stL.
Proof.
  pose proof liveP_c_range as CR. pose proof liveP_k_carved as [CV K0].
  constructor.
  - destruct (wf_base_ok st WF); constructor; assumption.
  - intros c' Hc'. pose proof (wf_class_ok st WF c' Hc') as WC. destruct (Z.eq_dec c' c) as [->|NE].
    + destruct WC; constructor; rewrite ?liveP_rg, ?liveP_ncarved, ?liveP_cch; try assumption.
      * intros j Hj. apply wc_used_carved. eapply Permutation_in; [exact liveP_used_same| exact Hj].
      * eapply Permutation_NoDup; [apply Permutation_sym; exact liveP_used_same| exact wc_used_nodup].
      * unfold zlen in *. rewrite (Permutation_length liveP_used_same). exact wc_used_all.
    + destruct WC; constructor; rewrite ?liveP_rg, ?liveP_ncarved, ?liveP_cch, ?liveP_used_other by exact NE; try assumption.
  - (* [comment removed for export] *) pose proof (wf_blocks_ok st WF) as WK. constructor.
    + intros b Hb. rewrite liveP_all_blocks in Hb. destruct Hb as [<-|Hb].
      * unfold wf_block. cbn [fst snd]. split; [exact HN|]. split.
        { rewrite HA. pose proof (rz_size_range n) as [_ RZ].
          destruct (carved_chunk st WF c k ltac:(unfold KNUMCLASSES; lia) ltac:(lia) CV) as (_ & _ & C3).
          destruct (region_range st WF c ltac:(unfold KNUMCLASSES; lia)) as (_ & _ & _ & R4 & _).
          pose proof (csize_mod32 c ltac:(lia)) as M32. pose proof (csize_pos c ltac:(lia)) as CP.
          apply mod0_add; [lia| | exact RZ].
          apply (mod0_of_sub _ (rbeg st c) 16 ltac:(lia)).
          - apply (mod0_trans _ 16 (csize c)); [lia| lia| apply (mod0_trans _ 16 32); [lia|lia|reflexivity|exact M32]| exact C3].
          - apply (mod0_trans _ 16 4096); [lia| lia| reflexivity| exact R4]. }
        split; [| intros HF; rewrite HP in HF; discriminate].
        intros _. cbn zeta. rewrite <- HC, liveP_bcptr. split; [exact CR|]. split; [exact K0|].
        unfold b_alloc_beg. rewrite liveP_cptr_addr, HA. lia.
      * exact (wk_block st WK b Hb).
    + rewrite liveP_all_blocks. cbn [map fst]. constructor; [| exact (wk_nodup st WK)].
      intros C. apply in_map_iff in C as ([A' n'] & E & Hin). cbn in E. exact (HNA A' n' Hin E).
  - (* [comment removed for export] *) pose proof (wf_sec_ok st WF) as WS. destruct WS; constructor; try assumption.
    + intros e He. destruct (ws_entry e He) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      rewrite liveP_all_blocks. destruct E4 as [E4|E4]; [left; right; exact E4| right; exact E4].
    + intros e He. destruct (ws_spend e He) as [S1 S2]. split; [exact S1|]. rewrite liveP_all_blocks. intros [E|C]; [| exact (S2 C)].
      (* [comment removed for export] *)
      injection E as E1 E2. pose proof (ws_entry e S1) as (EB & EN & _ & _). pose proof (sec_facts (snd e) EB) as (_ & _ & _ & SM & _).
      pose proof (prim_vs_tail st WF (fst e, fst e + smapsize (snd e))
                    ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists e; split; [reflexivity| exact S1])) as D.
      cbn [fst snd] in D. destruct (carved_chunk st WF c k ltac:(unfold KNUMCLASSES; lia) ltac:(lia) CV) as (C1 & C2 & _).
      destruct (region_range st WF c ltac:(unfold KNUMCLASSES; lia)) as (R1 & R2 & R3 & _). pose proof (S_range st WF) as (S1' & S2' & _).
      pose proof (wc_alloc_mapped st c (wf_class_ok st WF c ltac:(unfold KNUMCLASSES; lia))).
      pose proof (rz_size_range n) as [RZ _]. pose proof (csize_pos c ltac:(lia)) as CP.
      unfold usz, sec_user, SEC_HDR, SEC_RZ, KSPACESIZE, PRIM_RES_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *.
      clear - HA E1 D C1 C2 R1 R2 R3 S1' S2' H RZ SM CP CR. lia.
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    + cbn [st_apend st_qpend stL]. cbn [st_apend st_qpend st] in wq_inflight.
      pose proof (Permutation_length (remove_first_perm (c, k) AP HIN)) as L. cbn [length] in L. unfold zlen in *. lia.
    + intros ck Hck. apply wq_apend. eapply remove_first_In. exact Hck.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma rt_prov_liveP : rt_prov stL = rt_prov st + fp n + (if pclass n =? 24 then CL24_TAX else 0).
Proof.
  assert (E10 : prov_emb stL = prov_emb st) by reflexivity.
  assert (E9 : prov_l24 stL = prov_l24 st + (if pclass n =? 24 then CL24_TAX else 0)).
  { unfold prov_l24, lb_prim. cbn [st_lb stL st List.filter snd]. rewrite HP. cbn [andb].
    destruct (pclass n =? 24); [rewrite zlen_cons|]; lia. }
  assert (E1 : prov_classes stL = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stL = prov_nb st) by reflexivity.
  assert (E3 : prov_q stL = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stL = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stL = prov_live st + fp n).
  { unfold prov_live. cbn [st_lb stL st map]. rewrite RTW_m_pop.zsum_cons. cbn [snd]. unfold rp. rewrite HP. lia. }
  assert (E6 : prov_quar stL = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stL = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stL = prov_slots st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. lia.
Qed.
Lemma RTMODEL_liveP : forall mo, RTMODEL st mo -> RTMODEL stL mo. Proof. intros mo H. exact H. Qed.
Lemma GWIN_liveP : forall m mo g, GWIN st m mo g -> GWIN stL m mo g. Proof. intros m mo g H. exact H. Qed.
End LIVEP.

(* [comment removed for export] *)
Section LIVES.
Variables (mb n : Z).
Let A := sec_user mb.
Let stL := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 ((A, n) :: LB) AP (remove_first ck_eqb (mb, n) SP) QP b4 b5.
Hypothesis HP : bprim n = false.
Hypothesis HIN : In (mb, n) SP.

Lemma liveS_entry : In (mb, n) (st_sec st) /\ ~ In (A, n) (all_blocks st) /\ 0 <= n < 2^40 /\ mb mod 4096 = 0.
Proof.
  destruct (ws_spend st (wf_sec_ok st WF) (mb, n) HIN) as [S1 S2]. destruct (ws_entry st (wf_sec_ok st WF) (mb, n) S1) as (E1 & E2 & E3 & E4).
  cbn [fst snd] in *. repeat split; try assumption; lia.
Qed.
Lemma liveS_all_blocks : all_blocks stL = (A, n) :: all_blocks st. Proof. reflexivity. Qed.
Lemma liveS_lb_prim : forall c', lb_prim stL c' = lb_prim st c'.
Proof. intros c'. unfold lb_prim. cbn [st_lb stL st List.filter snd]. rewrite HP. reflexivity. Qed.
Lemma liveS_used : forall c', used_cptrs stL c' = used_cptrs st c'.
Proof. intros c'. unfold used_cptrs, live_cptrs. rewrite liveS_lb_prim. reflexivity. Qed.
(* [comment removed for export] *)
Lemma liveS_fresh : forall A' n', In (A', n') (all_blocks st) -> A' <> A.
Proof.
  intros A' n' Hin E. destruct liveS_entry as (S1 & S2 & S3 & S4).
  pose proof (spend_blockfree st WF (mb, n) HIN A' n' Hin) as D. cbn [fst snd] in D.
  pose proof (block_geom st WF A' n' Hin) as (_ & _ & _ & X & Y & _). unfold usz in Y.
  pose proof (sec_facts n HP) as (_ & _ & _ & SM & _). unfold usz in SM.
  subst A'. unfold A, sec_user, SEC_HDR, SEC_RZ in *. clear - D X Y SM. lia.
Qed.

Lemma RTWF_liveS : RTWF stL.
Proof.
  destruct liveS_entry as (S1 & S2 & S3 & S4).
  constructor.
  - destruct (wf_base_ok st WF); constructor; assumption.
  - intros c' Hc'. destruct (wf_class_ok st WF c' Hc'); constructor; rewrite ?liveS_used; try assumption.
  - pose proof (wf_blocks_ok st WF) as WK. constructor.
    + intros b Hb. rewrite liveS_all_blocks in Hb. destruct Hb as [<-|Hb]; [| exact (wk_block st WK b Hb)].
      unfold wf_block. cbn [fst snd]. split; [exact S3|]. split; [unfold A, sec_user, SEC_HDR, SEC_RZ; apply mod0_add; [lia| apply mod0_add; [lia| apply (mod0_trans _ 16 4096); [lia|lia|reflexivity|exact S4]| reflexivity]| reflexivity]|].
      split; [intros HT; rewrite HP in HT; discriminate|]. intros _. cbn [st_sec stL]. unfold A, b_map_beg, sec_user.
      replace (mb + SEC_HDR + SEC_RZ - SEC_RZ - SEC_HDR) with mb by lia. exact S1.
    + rewrite liveS_all_blocks. cbn [map fst]. constructor; [| exact (wk_nodup st WK)].
      intros C. apply in_map_iff in C as ([A' n'] & E & Hin). cbn in E. exact (liveS_fresh A' n' Hin E).
  - pose proof (wf_sec_ok st WF) as WS. destruct WS; constructor; try assumption.
    + intros e He. destruct (ws_entry e He) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      rewrite liveS_all_blocks. cbn [st_spend stL].
      destruct E4 as [E4|E4]; [left; right; exact E4|].
      destruct (ck_eqb (mb, n) e) eqn:EQ.
      * apply ck_eqb_eq in EQ. subst e. left. left. reflexivity.
      * right. (* [comment removed for export] *)
        clear - E4 EQ. induction SP as [|z l IH]; [destruct E4|]. cbn. destruct E4 as [<-|E4].
        { rewrite EQ. left. reflexivity. } destruct (ck_eqb (mb, n) z); [exact E4| right; apply IH; exact E4].
    + intros e He. cbn [st_spend stL] in He. pose proof (remove_first_In _ _ _ _ He) as He0. destruct (ws_spend e He0) as [T1 T2]. split; [exact T1|].
      rewrite liveS_all_blocks. intros [E|C]; [| exact (T2 C)].
      (* [comment removed for export] *)
      destruct e as [mb' n']. cbn [fst snd] in *. injection E as E1 E2. unfold A, sec_user in E1. assert (mb' = mb) by lia. subst mb' n'.
      pose proof ws_spend_nodup as ND. cbn [st_spend st] in ND.
      exact (remove_first_nodup_notin _ _ ND He).
    + cbn [st_spend stL]. apply NoDup_remove_first. exact ws_spend_nodup.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma rt_prov_liveS : rt_prov stL = rt_prov st + fp n + rp n.
Proof.
  assert (E10 : prov_emb stL = prov_emb st) by reflexivity.
  assert (E9 : prov_l24 stL = prov_l24 st).
  { unfold prov_l24, lb_prim. cbn [st_lb stL st List.filter snd]. rewrite HP. reflexivity. }
  assert (E1 : prov_classes stL = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stL = prov_nb st) by reflexivity.
  assert (E3 : prov_q stL = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stL = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stL = prov_live st + fp n + rp n).
  { unfold prov_live. cbn [st_lb stL st map]. rewrite RTW_m_pop.zsum_cons. cbn [snd]. lia. }
  assert (E6 : prov_quar stL = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stL = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stL = prov_slots st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. lia.
Qed.
Lemma RTMODEL_liveS : forall mo, RTMODEL st mo -> RTMODEL stL mo. Proof. intros mo H. exact H. Qed.
Lemma GWIN_liveS : forall m mo g, GWIN st m mo g -> GWIN stL m mo g. Proof. intros m mo g H. exact H. Qed.
End LIVES.

(* [comment removed for export] *)
Section FREE.
Variables (A n : Z).
Let stF := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 (remove_first ck_eqb (A, n) LB) AP SP ((A, n) :: QP) b4 b5.
Hypothesis HIN : In (A, n) LB.
Hypothesis HQP : QP = [].    (* [comment removed for export] *)

Lemma free_all_blocks : Permutation (all_blocks st) (all_blocks stF).
Proof.
  unfold all_blocks. cbn [st_lb st_qpend st stF]. change (qelems stF) with (qelems st).
  apply Permutation_trans with (((A, n) :: remove_first ck_eqb (A, n) LB) ++ qelems st ++ QP).
  - apply Permutation_app_tail. apply remove_first_perm. exact HIN.
  - cbn [app]. rewrite (app_assoc (remove_first ck_eqb (A, n) LB) (qelems st) QP), (app_assoc (remove_first ck_eqb (A, n) LB) (qelems st) ((A, n) :: QP)).
    apply Permutation_middle.
Qed.
Lemma free_used : forall c', Permutation (used_cptrs st c') (used_cptrs stF c').
Proof.
  intros c'. unfold used_cptrs. change (avail_cptrs stF c') with (avail_cptrs st c'). change (quar_cptrs stF c') with (quar_cptrs st c').
  change (batch_cptrs stF c') with (batch_cptrs st c'). change (apend_cptrs stF c') with (apend_cptrs st c').
  apply Permutation_app_head.
  unfold live_cptrs, qpend_cptrs, lb_prim, qp_prim. cbn [st_lb st_qpend st stF].
  set (f := fun b : Z * Z => bprim (snd b) && (pclass (snd b) =? c')). set (g := fun b : Z * Z => b_cptr st (fst b) (snd b)).
  change (fun b : Z * Z => b_cptr stF (fst b) (snd b)) with g.
  destruct (f (A, n)) eqn:EF.
  - destruct (remove_first_filter_true f (A, n) LB EF) as [P|N]; [| exfalso; exact (N HIN)].
    cbn [List.filter] in P |- *. rewrite EF in P |- *. cbn [map].
    (* [comment removed for export] *)
    apply perm_move_front. rewrite <- map_cons. apply Permutation_map. exact P.
  - rewrite (filter_remove_first_false f (A, n) LB EF). cbn [List.filter]. rewrite EF. apply Permutation_refl.
Qed.

Lemma RTWF_free : RTWF stF.
Proof.
  constructor.
  - destruct (wf_base_ok st WF); constructor; assumption.
  - intros c' Hc'. destruct (wf_class_ok st WF c' Hc'); constructor; try assumption.
    + intros j Hj. apply wc_used_carved. eapply Permutation_in; [apply Permutation_sym; apply free_used| exact Hj].
    + eapply Permutation_NoDup; [apply free_used| exact wc_used_nodup].
    + unfold zlen in *. rewrite <- (Permutation_length (free_used c')). exact wc_used_all.
  - pose proof (wf_blocks_ok st WF) as WK. constructor.
    + intros b Hb. apply (wk_block st WK). eapply Permutation_in; [apply Permutation_sym; apply free_all_blocks| exact Hb].
    + eapply Permutation_NoDup; [apply Permutation_map; apply free_all_blocks| exact (wk_nodup st WK)].
  - destruct (wf_sec_ok st WF); constructor; try assumption.
    + intros e He. destruct (ws_entry e He) as (E1 & E2 & E3 & E4). repeat (split; [assumption|]).
      destruct E4 as [E4|E4]; [left; eapply Permutation_in; [apply free_all_blocks| exact E4]| right; exact E4].
    + intros e He. destruct (ws_spend e He) as [T1 T2]. split; [exact T1|]. intros C. apply T2. eapply Permutation_in; [apply Permutation_sym; apply free_all_blocks| exact C].
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    cbn [st_apend st_qpend stF]. cbn [st_apend st_qpend st] in wq_inflight. rewrite HQP. unfold zlen in *. cbn [length]. lia.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma rt_prov_free : rt_prov stF = rt_prov st - fp n - (if is_cl24 n then CL24_TAX else 0).
Proof.
  assert (E10 : prov_emb stF = prov_emb st) by reflexivity.
  assert (E9 : prov_l24 st = prov_l24 stF + (if is_cl24 n then CL24_TAX else 0)).
  { unfold prov_l24, lb_prim, is_cl24, bprim. cbn [st_lb stF st]. unfold zlen.
    rewrite (Permutation_length (Permutation_filter' (fun b : Z * Z => is_primary (snd b) && (pclass (snd b) =? 24)) _ _ (remove_first_perm (A, n) LB HIN))).
    cbn [List.filter snd]. destruct (is_primary n && (pclass n =? 24)); cbn [length]; lia. }
  assert (E1 : prov_classes stF = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stF = prov_nb st) by reflexivity.
  assert (E3 : prov_q stF = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stF = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st = prov_live stF + fp n + rp n).
  { unfold prov_live. cbn [st_lb stF st].
    rewrite (zsum_map_perm (fun b : Z * Z => fp (snd b) + rp (snd b)) LB _ (remove_first_perm (A, n) LB HIN)). cbn [map]. rewrite RTW_m_pop.zsum_cons. cbn [snd]. lia. }
  assert (E6 : prov_quar stF = prov_quar st + rp n).
  { unfold prov_quar. cbn [st_qpend stF st]. change (qelems stF) with (qelems st). rewrite !map_app, !zsum_app. cbn [map]. rewrite RTW_m_pop.zsum_cons. cbn [snd]. lia. }
  assert (E7 : prov_depot stF = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stF = prov_slots st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E6, E7, E8. lia.
Qed.
Lemma RTMODEL_free : forall mo, RTMODEL st mo -> RTMODEL stF mo. Proof. intros mo H. exact H. Qed.
Lemma GWIN_free : forall m mo g, GWIN st m mo g -> GWIN stF m mo g. Proof. intros m mo g H. exact H. Qed.
End FREE.
End TR.


End CeilWrap.
End RT_trans.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_m_live.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition st_liveP (st : rtstate) (c k A n : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 ((A, n) :: LB) (remove_first ck_eqb (c, k) AP) SP QP b4 b5
  end.

(* [comment removed for export] *)
Lemma st_liveP_same : forall st c k A n,
  st_sp0 (st_liveP st c k A n) = st_sp0 st /\ st_lb (st_liveP st c k A n) = (A, n) :: st_lb st /\ st_lf (st_liveP st c k A n) = st_lf st
  /\ st_trs (st_liveP st c k A n) = st_trs st /\ st_apend (st_liveP st c k A n) = remove_first ck_eqb (c, k) (st_apend st)
  /\ st_spend (st_liveP st c k A n) = st_spend st /\ st_sec (st_liveP st c k A n) = st_sec st
  /\ st_qpend (st_liveP st c k A n) = st_qpend st /\ st_qtmp (st_liveP st c k A n) = st_qtmp st /\ st_qcur (st_liveP st c k A n) = st_qcur st
  /\ st_qthread (st_liveP st c k A n) = st_qthread st /\ st_qglobal (st_liveP st c k A n) = st_qglobal st /\ st_depot (st_liveP st c k A n) = st_depot st
  /\ st_fs (st_liveP st c k A n) = st_fs st /\ st_t (st_liveP st c k A n) = st_t st /\ st_spacebeg (st_liveP st c k A n) = st_spacebeg st
  /\ st_pbase (st_liveP st c k A n) = st_pbase st /\ st_pa (st_liveP st c k A n) = st_pa st
  /\ st_ctx (st_liveP st c k A n) = st_ctx st /\ st_tls (st_liveP st c k A n) = st_tls st /\ st_cache_inited (st_liveP st c k A n) = st_cache_inited st
  /\ st_regions (st_liveP st c k A n) = st_regions st /\ st_nreserved (st_liveP st c k A n) = st_nreserved st
  /\ st_trs0 (st_liveP st c k A n) = st_trs0 st /\ st_hints (st_liveP st c k A n) = st_hints st /\ st_loose0 (st_liveP st c k A n) = st_loose0 st
  /\ st_ia_inited (st_liveP st c k A n) = st_ia_inited st /\ st_cache (st_liveP st c k A n) = st_cache st.
Proof. intros st c k A n. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

(* [comment removed for export] *)
Lemma liveP_fresh : forall st c k n, RTWF st -> In (c, k) (st_apend st) -> c = pclass n -> bprim n = true ->
  forall A' n', In (A', n') (all_blocks st) -> A' <> cptr_addr st c k + rz_size n.
Proof.
  intros st c k n WF HIN HC HP A' n' HB.
  pose proof (prim_facts n HP) as (P1 & P2 & P3 & P4 & P5). unfold pslot in *. rewrite <- HC in *.
  pose proof (rz_size_range n) as [R1 _]. unfold usz in P2.
  pose proof (block_geom st WF A' n' HB) as (_ & _ & _ & G1 & G2 & _). unfold usz in G2.
  destruct (apend_vs_block st WF c k HIN A' n' HB); lia.
Qed.

(* [comment removed for export] *)
Lemma RTWF_liveP' : forall st c k A n, RTWF st -> bprim n = true -> c = pclass n -> In (c, k) (st_apend st) ->
  A = cptr_addr st c k + rz_size n -> 0 <= n < 2^40 -> RTWF (st_liveP st c k A n).
Proof.
  intros st c k A n WF HP HC HIN HA HN. pose proof (liveP_fresh st c k n WF HIN HC HP) as FR. rewrite <- HA in FR.
  destruct st. eapply RTWF_liveP; eauto.
Qed.
Lemma rt_prov_liveP' : forall st c k A n, bprim n = true -> rt_prov (st_liveP st c k A n) = rt_prov st + fp n + (if pclass n =? 24 then CL24_TAX else 0).
Proof. intros st c k A n HP. destruct st. eapply rt_prov_liveP; eauto. Qed.
Lemma RTMODEL_liveP' : forall st c k A n mo, RTMODEL st mo -> RTMODEL (st_liveP st c k A n) mo.
Proof. intros st c k A n mo H. destruct st. exact H. Qed.
Lemma SWIN_liveP' : forall st c k A n g, SWIN st g -> SWIN (st_liveP st c k A n) g.
Proof. intros st c k A n g H. destruct st. exact H. Qed.
Lemma GWIN_liveP' : forall st c k A n m mo g, GWIN st m mo g -> GWIN (st_liveP st c k A n) m mo g.
Proof. intros st c k A n m mo g H. destruct st. exact H. Qed.

Lemma liveP_avail' : forall st c k A n c', avail_cptrs (st_liveP st c k A n) c' = avail_cptrs st c'.
Proof. intros. destruct st. reflexivity. Qed.
Lemma liveP_cptr_addr' : forall st c k A n c' j, cptr_addr (st_liveP st c k A n) c' j = cptr_addr st c' j.
Proof. intros. destruct st. reflexivity. Qed.
Lemma liveP_apend_in' : forall st c k A n c' k', In k' (apend_cptrs (st_liveP st c k A n) c') -> In k' (apend_cptrs st c').
Proof.
  intros st c k A n c' k' H. unfold apend_cptrs in *. apply in_map_iff in H as ([c'' k''] & E & Hf). cbn [snd] in E. subst k''.
  apply filter_In in Hf as [Hin Hb]. apply in_map_iff. exists (c'', k'). split; [reflexivity|]. apply filter_In. split; [| exact Hb].
  destruct st. cbn in Hin |- *. eapply remove_first_In. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma liveP_apend_notk' : forall st c k A n, RTWF st -> In (c, k) (st_apend st) -> 1 <= c <= 30 ->
  ~ In k (avail_cptrs st c ++ apend_cptrs (st_liveP st c k A n) c).
Proof.
  intros st c k A n WF HIN Hc Hin.
  pose proof (wc_used_nodup st c (wf_class_ok st WF c ltac:(unfold KNUMCLASSES; lia))) as ND. rewrite used_cptrs_split in ND.
  assert (PA : Permutation (apend_cptrs st c) (k :: apend_cptrs (st_liveP st c k A n) c)).
  { destruct st. apply liveP_apend_same. exact HIN. }
  apply in_app_iff in Hin as [Hin|Hin].
  - eapply (nodup_app_disj _ _ k ND Hin). apply in_or_app. right. apply in_or_app. right. exact (apend_in_cptrs st c k HIN).
  - do 3 apply NoDup_app_remove_l in ND.
    pose proof (Permutation_NoDup PA ND) as ND3. inversion ND3; subst. contradiction.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LIVEM.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Variables (c k n : Z).
Hypothesis HIN : In (c, k) (st_apend st).
Hypothesis HP : bprim n = true.
Hypothesis HC : c = pclass n.
Let A := cptr_addr st c k + rz_size n.
Let stL := st_liveP st c k A n.

Lemma liveM_c_range : 1 <= c <= 30.
Proof. rewrite HC. exact (proj1 (prim_facts n HP)). Qed.

(* [comment removed for export] *)
Lemma R_block_liveP : forall m md A' n', R_block st m md A' n' -> R_block stL m md A' n'.
Proof. intros m md A' n' H. unfold stL, st_liveP. destruct st. exact H. Qed.

Theorem RTREP_liveP' : forall W m m',
  Forall (apz_ok st c k) W -> munch W m m' -> wmono asegs m m' -> RTREP st m ->
  R_block st m' BLive A n ->
  RTREP stL m'.
Proof.
  intros W m m' HW MU WM HR HB. pose proof liveM_c_range as CR. unfold stL.
  destruct (apz_others st WF HX c k HIN W HW m m' MU WM HR)
    as (X1 & X2 & X3 & X4 & X5 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & XA).
  assert (RA : R_avail stL m').
  { unfold stL. intros c' k' Hc' Hin. rewrite liveP_cptr_addr'. apply XA; [exact Hc'| |].
    - rewrite liveP_avail' in Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right; eapply liveP_apend_in'; exact Hin].
    - intros E. injection E as E1 E2. subst c' k'. exact (liveP_apend_notk' st c k A n WF HIN CR ltac:(rewrite liveP_avail' in Hin; exact Hin)). }
  assert (RL : R_live stL m').
  { unfold stL. intros A' n' Hin. destruct (st_liveP_same st c k A n) as (_ & E & _). rewrite E in Hin.
    destruct Hin as [E'|Hin].
    - injection E' as E1 E2. subst A' n'. apply R_block_liveP. exact HB.
    - apply R_block_liveP. exact (X9 A' n' Hin). }
  unfold st_liveP in *. destruct st. constructor; assumption.
Qed.
End LIVEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apzc_ok (st : rtstate) (c k SP : Z) (iv : Z * Z) : Prop :=
     (cptr_addr st c k <= fst iv /\ snd iv <= cptr_addr st c k + csize c)
  \/ (SH (cptr_addr st c k) <= fst iv /\ snd iv <= SH (cptr_addr st c k + csize c))
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (CEIL <= fst iv /\ snd iv <= SP).

Lemma apzc_apz : forall st c k SP W, Forall (apzc_ok st c k SP) W -> Forall (apz_ok st c k) W.
Proof.
  intros st c k SP W H. eapply Forall_impl; [| exact H]. intros [lo hi] A1. unfold apzc_ok, apz_ok in *. cbn [fst snd] in *. tauto.
Qed.

Section CLIA.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (c k : Z).
Hypothesis HIN : In (c, k) (st_apend st).
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.
Local Abbreviation CH := (cptr_addr st c k).
Local Abbreviation CS := (csize c).

Lemma chunk_not_client : forall a, CH <= a < CH + CS -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (geomA st WF c k HIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (shA st WF c k HIN) as (S1 & S2 & S3 & S4).
  unfold KREGIONSIZE, KFREEARRAY_OFF in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, KHIGHMEM_BEG in *. lia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (apend_vs_block st WF c k HIN A n HB) as D.
    pose proof (block_geom st WF A n HB) as (_ & _ & _ & X & Y & _). unfold usz in Y. lia.
  - pose proof (frame_range st WF F j Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    pose proof (loose_vs_chunk st WF c k HIN _ _ (wb_fs_loose st (wf_base_ok st WF))) as D.
    change FS_FRAMES_OFF with 36864 in X.
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz j) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as B. rewrite (rt_SH_aligned_add F (fsz j) AL) in B. unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
Qed.

Lemma chunk_shadow_not_client : forall a, SH CH <= a < SH (CH + CS) -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (geomA st WF c k HIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (shA st WF c k HIN) as (S1 & S2 & S3 & S4). rewrite SH_CEIL in *. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  unfold KREGIONSIZE, KFREEARRAY_OFF in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, KHIGHMEM_BEG in *. lia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n HB) as (_ & _ & X0 & X & Y & _). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F j Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    pose proof (loose_vs_chunk st WF c k HIN _ _ (wb_fs_loose st (wf_base_ok st WF))) as D.
    change FS_FRAMES_OFF with 36864 in X.
    destruct Hr as [Hr|Hr]; [unfold KHIGHMEM_BEG, AIMG_HI in *; blia|].
    rewrite <- (rt_SH_aligned_add F (fsz j) AL) in Hr.
    destruct D as [D|D].
    + pose proof (rt_SH_mono (F + fsz j) CH ltac:(lia)). lia.
    + pose proof (rt_SH_mono (CH + CS) F ltac:(lia)). lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

(* [comment removed for export] *)
Lemma cli_pres_apz : forall W m m',
  munch W m m' -> wmono asegs m m' -> Forall (apzc_ok st c k SP) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold apzc_ok in A1. cbn [fst snd] in A1. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|[A1|[A1|A1]]].
  - apply (chunk_not_client a); [lia| exact HC].
  - apply (chunk_shadow_not_client a); [lia| exact HC].
  - apply (tpage_not_client st WF SP HSP a); [unfold T_STATS, T_UNWINDING, T_ACACHE in *; lia| exact HC].
  - apply (below_sp_not_client st WF SP a); [lia| exact HC].
Qed.
End CLIA.

(* [comment removed for export] *)
Lemma tpx_ok_of_RTWF : forall st, RTWF st -> tpx_ok st.
Proof. intros st WF. split; [exact (wb_ctx_t st (wf_base_ok st WF))| exact (wb_dtls_t st (wf_base_ok st WF))]. Qed.


End CeilWrap.
End RTW_m_live.

(* [comment removed for export] *)
Module RTW_q_trans.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface RT_trans.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition q_set (st : rtstate) (qt qg : list qbatch) (ap qp : list (Z * Z)) (tmp : list qbatch) (cur : list (qbatch * Z)) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 _ _ a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB _ SP _ _ _ =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 qt qg a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB ap SP qp tmp cur
  end.

Lemma q_set_fields : forall st qt qg ap qp tmp cur,
  st_qthread (q_set st qt qg ap qp tmp cur) = qt /\ st_qglobal (q_set st qt qg ap qp tmp cur) = qg
  /\ st_apend (q_set st qt qg ap qp tmp cur) = ap /\ st_qpend (q_set st qt qg ap qp tmp cur) = qp
  /\ st_qtmp (q_set st qt qg ap qp tmp cur) = tmp /\ st_qcur (q_set st qt qg ap qp tmp cur) = cur.
Proof. intros. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

(* [comment removed for export] *)
Lemma q_set_same : forall st qt qg ap qp tmp cur, let st' := q_set st qt qg ap qp tmp cur in
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st /\ st_regions st' = st_regions st
  /\ st_cache_inited st' = st_cache_inited st /\ st_cache st' = st_cache st /\ st_pa st' = st_pa st /\ st_nreserved st' = st_nreserved st
  /\ st_sec st' = st_sec st /\ st_depot st' = st_depot st /\ st_trs st' = st_trs st /\ st_trs0 st' = st_trs0 st
  /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st /\ st_lf st' = st_lf st /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st
  /\ st_tls st' = st_tls st /\ st_loose0 st' = st_loose0 st /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_spend st' = st_spend st.
Proof. intros. subst st'. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

(* [comment removed for export] *)
Lemma q_set_rg : forall st qt qg ap qp tmp cur c, rg (q_set st qt qg ap qp tmp cur) c = rg st c.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_cch : forall st qt qg ap qp tmp cur c, cch (q_set st qt qg ap qp tmp cur) c = cch st c.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_cptr_addr : forall st qt qg ap qp tmp cur c k, cptr_addr (q_set st qt qg ap qp tmp cur) c k = cptr_addr st c k.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_avail : forall st qt qg ap qp tmp cur c, avail_cptrs (q_set st qt qg ap qp tmp cur) c = avail_cptrs st c.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_live : forall st qt qg ap qp tmp cur c, live_cptrs (q_set st qt qg ap qp tmp cur) c = live_cptrs st c.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_qcache_t : forall st qt qg ap qp tmp cur, qcache_t (q_set st qt qg ap qp tmp cur) = qcache_t st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_acache : forall st qt qg ap qp tmp cur, acache (q_set st qt qg ap qp tmp cur) = acache st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_rt_ranges : forall st qt qg ap qp tmp cur, rt_ranges (q_set st qt qg ap qp tmp cur) = rt_ranges st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_fresh : forall st qt qg ap qp tmp cur c, fresh_cls st c -> fresh_cls (q_set st qt qg ap qp tmp cur) c.
Proof. intros st qt qg ap qp tmp cur c H. unfold fresh_cls in *. rewrite q_set_rg, q_set_cch. exact H. Qed.
Lemma RTMODEL_q_set : forall st qt qg ap qp tmp cur mo, RTMODEL st mo -> RTMODEL (q_set st qt qg ap qp tmp cur) mo.
Proof. intros. destruct st. exact H. Qed.
Lemma GWIN_q_set : forall st qt qg ap qp tmp cur m mo g, GWIN st m mo g -> GWIN (q_set st qt qg ap qp tmp cur) m mo g.
Proof. intros. destruct st. exact H. Qed.
Lemma SWIN_q_set : forall st qt qg ap qp tmp cur g, SWIN st g -> SWIN (q_set st qt qg ap qp tmp cur) g.
Proof. intros. destruct st. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qb_push (b : qbatch) (e : Z * Z) : qbatch := mkQB (qb_addr b) (qb_elems b ++ [e]).
(* [comment removed for export] *)
Definition upd_last (q : list qbatch) (f : qbatch -> qbatch) : list qbatch :=
  match rev q with [] => [] | b :: r => rev r ++ [f b] end.

(* [comment removed for export] *)
Definition st_enq_last (st : rtstate) (A n : Z) : rtstate :=
  q_set st (upd_last (st_qthread st) (fun b => qb_push b (A, n))) (st_qglobal st)
        (st_apend st) (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st).

(* [comment removed for export] *)
Definition st_enq_new (st : rtstate) (k A n : Z) : rtstate :=
  q_set st (st_qthread st ++ [mkQB (cptr_addr st 24 k) [(A, n)]]) (st_qglobal st)
        (remove_first ck_eqb (24, k) (st_apend st)) (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st).

(* [comment removed for export] *)
Definition st_drain (st : rtstate) : rtstate :=
  q_set st [] (st_qglobal st ++ st_qthread st) (st_apend st) (st_qpend st) (st_qtmp st) (st_qcur st).

(* [comment removed for export] *)
Definition qb_absorb (cur nxt : qbatch) : qbatch := mkQB (qb_addr cur) (qb_elems cur ++ qb_elems nxt).
Definition st_merge (st : rtstate) (pre : list qbatch) (cur nxt : qbatch) (post : list qbatch) : rtstate :=
  q_set st (st_qthread st) (pre ++ qb_absorb cur nxt :: post) (st_apend st) (st_qpend st)
        (st_qtmp st ++ [mkQB (qb_addr nxt) []]) (st_qcur st).

(* [comment removed for export] *)
Definition st_qpop (st : rtstate) : rtstate :=
  match st_qglobal st with
  | [] => st
  | b :: r => q_set st (st_qthread st) r (st_apend st) (st_qpend st) (st_qtmp st ++ [b]) (st_qcur st)
  end.

(* [comment removed for export] *)
Definition st_qstart (st : rtstate) : rtstate :=
  match st_qtmp st with
  | [] => st
  | b :: r => q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]
  end.

(* [comment removed for export] *)
Definition st_qchunk (st : rtstate) (c k : Z) : rtstate :=
  match st_qcur st with
  | [(b, d)] => q_set st (st_qthread st) (st_qglobal st) ((c, k) :: st_apend st) (st_qpend st) (st_qtmp st) [(b, d + 1)]
  | _ => st
  end.

(* [comment removed for export] *)
Definition st_qbatch (st : rtstate) (kb : Z) : rtstate :=
  q_set st (st_qthread st) (st_qglobal st) ((24, kb) :: st_apend st) (st_qpend st) (st_qtmp st) [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_last_snoc : forall q b f, upd_last (q ++ [b]) f = q ++ [f b].
Proof. intros. unfold upd_last. rewrite rev_app_distr. cbn. rewrite rev_involutive. reflexivity. Qed.
Lemma upd_last_nil : forall f, upd_last [] f = []. Proof. reflexivity. Qed.

Lemma qb_count_push : forall b e, qb_count (qb_push b e) = qb_count b + 1.
Proof. intros. unfold qb_count, qb_push. cbn. rewrite length_app. cbn. lia. Qed.
Lemma qb_size_push : forall b A n, qb_size (qb_push b (A, n)) = qb_size b + Z.max n 1.
Proof.
  intros. unfold qb_size, qb_push. cbn [qb_elems].
  induction (qb_elems b) as [|e l IH]; cbn; [lia|]. cbn in IH. lia.
Qed.
Lemma qb_size_one : forall a A n, qb_size (mkQB a [(A, n)]) = QBATCH_SIZE + Z.max n 1.
Proof. intros. unfold qb_size. cbn. lia. Qed.
Lemma qc_bytes_app : forall p q, qc_bytes (p ++ q) = qc_bytes p + qc_bytes q.
Proof. intros. unfold qc_bytes. induction p as [|b p IH]; cbn; [lia|]. cbn in IH. lia. Qed.
Lemma qc_bytes_cons : forall b q, qc_bytes (b :: q) = qb_size b + qc_bytes q.
Proof. intros. reflexivity. Qed.
Lemma qc_bytes_nil : qc_bytes [] = 0. Proof. reflexivity. Qed.
Lemma qb_count_absorb : forall cur nxt, qb_count (qb_absorb cur nxt) = qb_count cur + qb_count nxt.
Proof. intros. unfold qb_count, qb_absorb. cbn. rewrite length_app. lia. Qed.
Lemma qb_size_absorb : forall cur nxt, qb_size (qb_absorb cur nxt) = qb_size cur + qb_size nxt - QBATCH_SIZE.
Proof.
  intros. unfold qb_size, qb_absorb. cbn [qb_elems].
  induction (qb_elems cur) as [|e l IH]; cbn; [lia|]. cbn in IH. lia.
Qed.


End CeilWrap.
End RTW_q_trans.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_secz RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_artR.
Import RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section TRDP.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HP : bprim n = false.
Hypothesis PEND : In (sec_user mb, n) QP.

Let A := sec_user mb.
Definition didx : Z := index_of a9 mb.
Let idx := didx.
Let secD := sec_remove a9 idx.
Let QP' := remove_first ck_eqb (sec_user mb, n) QP.
Let stD := mkRT a1 a2 a3 a4 a5 a6 a7 a8 secD a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP' b4 b5.

(* [comment removed for export] *)
Lemma qelems_stD : qelems stD = qelems st.
Proof. reflexivity. Qed.
Lemma A_in_blocks : In (A, n) (all_blocks st).
Proof. unfold all_blocks. cbn [st_lb st_qpend st]. apply in_or_app. right. apply in_or_app. right. exact PEND. Qed.
Lemma all_blocks_perm : Permutation (all_blocks st) ((A, n) :: all_blocks stD).
Proof.
  unfold all_blocks. rewrite qelems_stD. cbn [st_lb st_qpend st stD].
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_head; exact (remove_first_perm (A, n) QP PEND)|].
  change (remove_first ck_eqb (A, n) QP) with QP'. apply Permutation_sym. rewrite (app_assoc LB (qelems st) ((A, n) :: QP')), (app_assoc LB (qelems st) QP'). apply Permutation_middle.
Qed.
Lemma blocksD_sub : forall x, In x (all_blocks stD) -> In x (all_blocks st).
Proof. intros x Hx. apply (Permutation_in x (Permutation_sym all_blocks_perm)). right. exact Hx. Qed.
Lemma A_notin_blocksD : ~ In (A, n) (all_blocks stD) /\ forall n', ~ In (A, n') (all_blocks stD).
Proof.
  pose proof (Permutation_NoDup (Permutation_map fst all_blocks_perm) (wk_nodup st (wf_blocks_ok st WF))) as ND. cbn [map fst] in ND.
  inversion ND as [|x l Hn Hl]; subst.
  split; [intros C; apply Hn; apply in_map_iff; exists (A, n); auto|].
  intros n' C. apply Hn. apply in_map_iff. exists (A, n'). auto.
Qed.

Lemma mbn_in_sec : In (mb, n) a9.
Proof.
  pose proof (wk_block st (wf_blocks_ok st WF) _ A_in_blocks) as (_ & _ & _ & HS). cbn [fst snd] in HS.
  specialize (HS HP). replace (b_map_beg A) with mb in HS; [exact HS|]. unfold A, b_map_beg, sec_user. lia.
Qed.
Lemma mb_in_fst : In mb (map fst a9).
Proof. apply in_map_iff. exists (mb, n). split; [reflexivity| exact mbn_in_sec]. Qed.
Lemma idx_facts : 0 <= idx < nsec st /\ nthz a9 idx (0,0) = (mb, n).
Proof.
  pose proof (ws_nodup st (wf_sec_ok st WF)) as ND. cbn [st_sec st] in ND.
  destruct (index_of_In_bound a9 mb mb_in_fst) as [B E]. unfold idx, didx, nsec. cbn [st_sec st]. split; [exact B|].
  (* [comment removed for export] *)
  destruct (nthz a9 (index_of a9 mb) (0,0)) as [mb' n'] eqn:En. cbn [fst] in E. subst mb'.
  assert (Hin : In (mb, n') a9). { rewrite <- En. unfold nthz. destruct (Z.ltb_spec0 (index_of a9 mb) 0); [lia|]. apply nth_In. unfold zlen in B. lia. }
  f_equal. exact (NoDup_map_fst_unique a9 mb n' n ND Hin mbn_in_sec).
Qed.

(* [comment removed for export] *)
Lemma dereg_qall : qall stD = qall st.
Proof. reflexivity. Qed.
Lemma dereg_q_prim : forall c, q_prim stD c = q_prim st c.
Proof. reflexivity. Qed.
Lemma dereg_qp_prim : forall c, qp_prim stD c = qp_prim st c.
Proof.
  intros c. unfold qp_prim. cbn [st_qpend stD st]. unfold QP'. apply filter_remove_first_false. cbn [snd]. rewrite HP. reflexivity.
Qed.
Lemma dereg_used : forall c, used_cptrs stD c = used_cptrs st c.
Proof.
  intros c. unfold used_cptrs, avail_cptrs, live_cptrs, quar_cptrs, qpend_cptrs, batch_cptrs, apend_cptrs, qbatch_addrs, lb_prim.
  rewrite dereg_q_prim, dereg_qall, dereg_qp_prim. reflexivity.
Qed.
Lemma dereg_nsec : nsec stD = nsec st - 1.
Proof. unfold nsec. cbn [st_sec stD st]. unfold secD. apply (sec_remove_zlen a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF))); [exact (proj1 idx_facts)| exact (proj2 idx_facts)]. Qed.

(* [comment removed for export] *)
Let RSEC (l : list (Z * Z)) := map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) l.
Lemma rt_ranges_of : forall s9 qp qc, rt_ranges (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP qp b4 qc) =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21) ++ RSEC s9
  ++ (map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof. intros. unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot]. cbn [app]. rewrite <- ?app_assoc. reflexivity. Qed.
Lemma rt_ranges_perm : Permutation (rt_ranges st) ((mb, mb + smapsize n) :: rt_ranges stD).
Proof.
  unfold st, stD. rewrite !rt_ranges_of.
  pose proof (Permutation_map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts))) as PM.
  cbn [map fst snd] in PM. fold (RSEC a9) in PM. fold (RSEC secD) in PM. unfold secD in PM |- *. fold idx.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact PM|].
  apply Permutation_sym. apply Permutation_middle with (l1 := (a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21).
Qed.
Lemma dereg_In_ranges : forall r, In r (rt_ranges stD) -> In r (rt_ranges st).
Proof. intros r Hr. apply (Permutation_in r (Permutation_sym rt_ranges_perm)). right. exact Hr. Qed.
Lemma mb_fresh : forall r, In r (rt_ranges stD) -> mb + smapsize n <= fst r \/ snd r <= mb.
Proof.
  intros r Hr. pose proof (pwdj_perm _ _ rt_ranges_perm (wb_pwdj st (wf_base_ok st WF))) as PW. cbn in PW. destruct PW as [HF _].
  rewrite Forall_forall in HF. specialize (HF r Hr). cbn [fst snd] in HF. lia.
Qed.

(* [comment removed for export] *)
Lemma RTWF_dereg : RTWF stD.
Proof.
  pose proof idx_facts as [HI HN]. pose proof (wf_base_ok st WF) as WB. pose proof (wf_sec_ok st WF) as WS.
  pose proof A_notin_blocksD as [NA NA'].
  constructor.
  - (* [comment removed for export] *) destruct WB; constructor; try assumption.
    + intros r Hr. exact (wb_ranges r (dereg_In_ranges r Hr)).
    + pose proof (pwdj_perm _ _ rt_ranges_perm wb_pwdj) as PW. cbn in PW. exact (proj2 PW).
  - (* [comment removed for export] *) intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; try assumption; rewrite ?dereg_used; assumption.
  - (* [comment removed for export] *) pose proof (wf_blocks_ok st WF) as WK. constructor.
    + intros bk Hb. pose proof (wk_block st WK bk (blocksD_sub bk Hb)) as (K1 & K2 & K3 & K4). unfold wf_block. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      intros HF. cbn [st_sec stD]. specialize (K4 HF). cbn [st_sec st] in K4.
      apply (sec_remove_In_iff a9 idx (mb, n) (ws_nodup st WS) HI HN) in K4 as [E|K4]; [| exact K4].
      exfalso. injection E as E1 E2. apply (NA' (snd bk)). replace A with (fst bk); [rewrite <- surjective_pairing; exact Hb|].
      unfold A, sec_user. unfold b_map_beg in E1. lia.
    + pose proof (Permutation_NoDup (Permutation_map fst all_blocks_perm) (wk_nodup st WK)) as ND. cbn [map] in ND. inversion ND; assumption.
  - (* [comment removed for export] *) destruct WS; constructor.
    + cbn [st_sec stD]. exact (proj1 (sec_remove_nodup_fst a9 idx (mb, n) ws_nodup HI HN)).
    + rewrite dereg_nsec. cbn [st_nreserved stD]. cbn [st_nreserved st] in ws_nres. lia.
    + intros e He. cbn [st_sec st_spend stD] in He |- *. pose proof (sec_remove_In a9 idx (mb, n) ws_nodup HI HN e He) as He0.
      destruct (ws_entry e He0) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      destruct E4 as [E4|E4]; [| right; exact E4]. left.
      apply (Permutation_in _ all_blocks_perm) in E4. destruct E4 as [E4|E4]; [| exact E4].
      exfalso. injection E4 as E5 E6. assert (fst e = mb) by (unfold A, sec_user in E5; lia).
      assert (e = (mb, n)).
      { rewrite (surjective_pairing e). f_equal; [lia|]. apply (NoDup_map_fst_unique a9 mb); [exact ws_nodup| rewrite <- H, <- surjective_pairing; exact He0| exact mbn_in_sec]. }
      subst e. exact (sec_remove_notin a9 idx (mb, n) ws_nodup HI HN He).
    + intros e He. cbn [st_sec st_spend stD] in He |- *. destruct (ws_spend e He) as [T1 T2]. cbn [st_sec st] in T1. split.
      * apply (sec_remove_In_iff a9 idx (mb, n) ws_nodup HI HN) in T1 as [->|T1]; [| exact T1]. exfalso. apply T2. exact A_in_blocks.
      * intros C. apply T2. exact (blocksD_sub _ C).
    + exact ws_spend_nodup.
  - (* [comment removed for export] *) destruct (wf_quar_ok st WF); constructor; try assumption.
    + (* [comment removed for export] *) cbn [st_apend st_qpend stD]. cbn [st_apend st_qpend st] in wq_inflight.
      pose proof (Permutation_length (remove_first_perm (A, n) QP PEND)) as L. cbn [length] in L. unfold QP'. unfold A in L. unfold zlen in *. lia.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma dereg_same : same_but_secondary_p st stD.
Proof. unfold same_but_secondary_p. repeat split; reflexivity. Qed.
Lemma dereg_rel : sec_dealloc_pend_rel st stD A n mb.
Proof.
  split; [exact dereg_same|]. split; [reflexivity|].
  cbn [st_sec st stD]. exact (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts)).
Qed.

(* [comment removed for export] *)
Lemma rt_prov_dereg : rt_prov stD + SEC_SLOT_TAX + 2 * smapsize n <= rt_prov st.
Proof.
  assert (E1 : prov_classes stD = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stD = prov_nb st) by reflexivity.
  assert (E3 : prov_q stD = prov_q st) by reflexivity.
  assert (E5 : prov_live stD = prov_live st) by reflexivity.
  assert (E7 : prov_depot stD = prov_depot st) by reflexivity.
  assert (E9 : prov_l24 stD = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stD = prov_emb st) by reflexivity.   (* [comment removed for export] *)
  assert (E8 : prov_slots stD = prov_slots st - SEC_SLOT_TAX) by (unfold prov_slots; rewrite dereg_nsec; lia).
  assert (E4 : prov_ptr stD <= prov_ptr st).
  { unfold prov_ptr. cbn [st_nreserved stD st]. rewrite dereg_nsec. lia. }
  assert (E6 : prov_quar stD + 2 * smapsize n = prov_quar st).
  { unfold prov_quar. rewrite qelems_stD. cbn [st_qpend st stD].
    rewrite (zsum_perm _ _ (Permutation_map (fun b0 : Z * Z => rp (snd b0)) (Permutation_app_head (qelems st) (remove_first_perm (A, n) QP PEND)))).
    fold QP'. rewrite !map_app. cbn [map snd]. rewrite !zsum_app. cbn [zsum fold_right].
    replace (rp n) with (2 * smapsize n) by (unfold rp; rewrite HP; reflexivity). change (remove_first ck_eqb (A, n) QP) with QP'. unfold zsum. lia. }
  unfold rt_prov. rewrite E1, E2, E3, E5, E7, E8, E9. lia.
Qed.

(* [comment removed for export] *)
Let lst := last a9 (0,0).
Lemma dereg_index : forall x, In x (map fst secD) ->
  sec_index stD x = (if x =? fst lst then (if idx <? nsec st - 1 then idx else sec_index st x) else sec_index st x)
  /\ 0 <= sec_index stD x < nsec st - 1 /\ nthz secD (sec_index stD x) (0,0) = nthz a9 (sec_index st x) (0,0).
Proof.
  intros x Hx. pose proof idx_facts as [HI HN]. pose proof (ws_nodup st (wf_sec_ok st WF)) as ND. cbn [st_sec st] in ND.
  pose proof (sec_remove_nodup_fst a9 idx (mb, n) ND HI HN) as [NDD NIN]. fold secD in NDD, NIN.
  pose proof (sec_remove_zlen a9 idx (mb, n) ND HI HN) as ZL. fold secD in ZL. unfold nsec. cbn [st_sec st].
  destruct (index_of_In_bound secD x Hx) as [B E]. unfold sec_index. cbn [st_sec stD st]. fold secD. rewrite ZL in B.
  (* [comment removed for export] *)
  assert (HxO : In x (map fst a9)).
  { apply in_map_iff in Hx as (ex & Ex & Hex). apply in_map_iff. exists ex. split; [exact Ex| exact (sec_remove_In a9 idx (mb, n) ND HI HN ex Hex)]. }
  destruct (index_of_In_bound a9 x HxO) as [BO EO].
  pose proof (sec_remove_nth a9 idx (mb, n) ND HI HN (index_of secD x) B) as NT. fold secD lst in NT.
  assert (KEY : forall i j, 0 <= i < zlen a9 -> 0 <= j < zlen a9 -> fst (nthz a9 i (0,0)) = fst (nthz a9 j (0,0)) -> i = j).
  { intros i j Hi Hj Hij. rewrite <- (index_of_nthz a9 i (0,0) ND Hi), <- (index_of_nthz a9 j (0,0) ND Hj). rewrite Hij. reflexivity. }
  pose proof (lst_nth a9 idx (mb, n) ND HI HN) as LN. fold lst in LN.
  destruct (Z.eqb_spec (index_of secD x) idx) as [EI|NI].
  - (* [comment removed for export] *)
    rewrite EI in NT, E |- *. rewrite NT in E.
    assert (IL : idx < zlen a9 - 1) by lia.
    split; [| split; [lia| rewrite NT, <- LN; f_equal; symmetry; apply KEY; [lia| lia| rewrite LN, EO; symmetry; exact E]]].
    rewrite <- E, Z.eqb_refl. destruct (Z.ltb_spec0 idx (zlen a9 - 1)); [reflexivity| lia].
  - rewrite NT in E.
    assert (EQ : index_of a9 x = index_of secD x) by (apply KEY; [lia| lia| rewrite EO, E; reflexivity]).
    split; [| split; [lia| rewrite NT, EQ; reflexivity]].
    destruct (Z.eqb_spec x (fst lst)) as [EX|NX]; [| symmetry; exact EQ].
    destruct (Z.ltb_spec0 idx (zlen a9 - 1)) as [IL|IL]; [| symmetry; exact EQ].
    exfalso. enough (index_of secD x = zlen a9 - 1) by lia. apply KEY; [lia| lia|]. rewrite E, LN. exact EX.
Qed.

(* [comment removed for export] *)
Lemma rt_loose_of : forall s9 qp qc, rt_loose (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP qp b4 qc) =
  a21 ++ map (fun e => (fst e, smapsize (snd e))) s9 ++ map (fun b => (b, NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, STOREBLOCK_SIZE)) (d_sblocks a12).
Proof. intros. reflexivity. Qed.
Lemma rt_loose_perm : Permutation (rt_loose st) ((mb, smapsize n) :: rt_loose stD).
Proof.
  unfold st, stD. rewrite !rt_loose_of.
  pose proof (Permutation_map (fun e : Z * Z => (fst e, smapsize (snd e))) (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts))) as PM.
  cbn [map fst snd] in PM. unfold secD. fold idx.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact PM|].
  apply Permutation_sym. apply (Permutation_middle a21).
Qed.
Lemma rt_loose_ranges : forall s9 qp qc e, In e (rt_loose (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP qp b4 qc)) ->
  In (fst e, fst e + snd e) (rt_ranges (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP qp b4 qc)).
Proof.
  intros s9 qp qc e He. rewrite rt_loose_of in He. rewrite rt_ranges_of. rewrite !in_app_iff in He. rewrite !in_app_iff. cbn [In].
  destruct He as [He|[He|[He|He]]].
  - left. right. right. apply in_map_iff. exists e. split; [reflexivity| exact He].
  - right. left. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
  - right. right. left. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
  - right. right. right. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
Qed.

Lemma RTMODEL_dereg : forall moX, LOK asegs moX -> RTMODEL st moX -> RTMODEL stD (mm_unmap (wz mb) (wz (smapsize n)) moX).
Proof.
  intros moX HO (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof (ws_entry st (wf_sec_ok st WF) (mb, n) mbn_in_sec) as (_ & Hn40 & MAL & _). cbn [fst snd] in Hn40, MAL.
  pose proof (wb_ranges st (wf_base_ok st WF) (mb, mb + smapsize n)) as RG. cbn [fst snd] in RG.
  specialize (RG ltac:(unfold st; rewrite rt_ranges_of; rewrite !in_app_iff; right; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact mbn_in_sec])).
  pose proof (smapsize_pos n ltac:(lia)) as [SP0 _]. unfold KHIGHMEM_BEG, AIMG_HI in RG.
  pose proof (P_range st WF) as (P1 & P2 & P3). pose proof (pa_range st WF) as (Q1 & Q2 & _). cbn [st_pbase st_pa st] in P1, P2, P3, Q1, Q2. unfold KHIGHMEM_BEG, AIMG_HI in P1, Q1.
  assert (U1 : bv_unsigned (wz mb) = mb) by (unfold wz; apply unsigned_lit; blia).
  assert (U2 : bv_unsigned (wz (smapsize n)) = smapsize n) by (unfold wz; apply unsigned_lit; blia).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  (* [comment removed for export] *)
  pose proof mb_fresh as MF.
  assert (NB : forall lo2 sz2, In (lo2, lo2 + sz2) (rt_ranges stD) -> wz lo2 <> wz mb).
  { intros lo2 sz2 Hin E. pose proof (MF _ Hin) as D. cbn [fst snd] in D.
    pose proof (wb_ranges st (wf_base_ok st WF) _ (dereg_In_ranges _ Hin)) as (R1 & R2 & R3 & _). cbn [fst snd] in R1, R2, R3. unfold KHIGHMEM_BEG, AIMG_HI in R1.
    apply wz_inj in E; blia. }
  unfold RTMODEL. rewrite mm_unmap_maps. cbn [vm_limit st_pbase st_pa stD st].
  assert (ZR : forall lo2 sz2, In (lo2, lo2 + sz2) (rt_ranges stD) -> zin lo2 sz2 (vm_maps (m_vmmaps moX)) -> zin lo2 sz2 (map_remove (vm_maps (m_vmmaps moX)) (wz mb))).
  { intros lo2 sz2 Hin HZ. unfold zin in *. apply In_map_remove. split; [exact HZ| cbn [fst]; exact (NB lo2 sz2 Hin)]. }
  split; [apply ZR; [unfold stD; rewrite rt_ranges_of; left; reflexivity| exact M1]|].
  split; [apply ZR; [unfold stD; rewrite rt_ranges_of; right; left; reflexivity| exact M2]|].
  split. { unfold zin in *. apply In_map_remove. split; [exact M3|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KHIGHSHADOW_BEG; lia| blia]. unfold KHIGHSHADOW_BEG in E. blia. }
  split. { unfold zin in *. apply In_map_remove. split; [exact M4|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KLOWSHADOW_BEG; lia| blia]. unfold KLOWSHADOW_BEG in E. blia. }
  split; [| split; [| split; [| split]]].
  - intros e He. apply (ZR (fst e) (snd e)); [exact (rt_loose_ranges _ _ _ e He)|]. apply M5.
    apply (Permutation_in e (Permutation_sym rt_loose_perm)). right. exact He.
  - (* [comment removed for export] *)
    unfold zin in *. apply In_map_remove. split; [exact M6|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KLOWSHADOW_END; lia| blia]. unfold KLOWSHADOW_END in E. blia.
  - intros x Hx. specialize (M7 x Hx). unfold lzf in *. rewrite mm_unmap_lazy, mm_unmap_na, U1, U2.
    rewrite !inzr_maps_subtract by (first [exact Hlz| exact Hna| lia]).
    apply andb_true_iff in M7 as [L1 L2]. rewrite L1. apply negb_true_iff in L2. rewrite L2.
    unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI in Hx.
    destruct (Z.leb_spec0 mb (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (mb + smapsize n)); cbn; try reflexivity; exfalso; blia.
  - exact M8.
  - intros e He. apply (sec_plain_unmap moX _ _ _ _ HO). apply M9. cbn [st_sec st]. cbn [st_sec stD] in He.
    exact (sec_remove_In a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts) e He).
Qed.

(* [comment removed for export] *)
Lemma SWIN_dereg : forall g, SWIN st g -> SWIN stD g.
Proof.
  intros g HS e He. apply HS. cbn [st_sec st]. cbn [st_sec stD] in He.
  exact (sec_remove_In a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts) e He).
Qed.

Lemma GWIN_dereg : forall m mo g, GWIN st m mo g -> GWIN stD m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma qelems_sub : forall x, In x (qelems stD) -> In x (qelems st).
Proof. intros x Hx. exact Hx. Qed.
Lemma qpend_sub : forall x, In x (st_qpend stD) -> In x (st_qpend st).
Proof. intros x Hx. cbn [st_qpend stD st] in *. exact (remove_first_In ck_eqb _ _ _ Hx). Qed.
End TRDP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_secderegP (st : rtstate) (mb n : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 (sec_remove a9 (index_of a9 mb)) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP
         (remove_first ck_eqb (sec_user mb, n) QP) b4 b5
  end.

Section W2P.
  Variables (st : rtstate) (mb n : Z).
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis PEND : In (sec_user mb, n) (st_qpend st).
  Let stD := st_secderegP st mb n.
  Let idx := sec_index st mb.

  Lemma st_secdereg_fields :
    st_sec stD = sec_remove (st_sec st) idx /\ st_qcur stD = st_qcur st /\ st_spend stD = st_spend st /\ st_nreserved stD = st_nreserved st
    /\ st_pa stD = st_pa st /\ st_t stD = st_t st /\ st_sp0 stD = st_sp0 st /\ st_lb stD = st_lb st /\ st_lf stD = st_lf st /\ st_trs stD = st_trs st
    /\ st_depot stD = st_depot st /\ st_ctx stD = st_ctx st /\ st_qpend stD = remove_first ck_eqb (sec_user mb, n) (st_qpend st) /\ st_pbase stD = st_pbase st.
  Proof using WF HP PEND. unfold stD, idx, sec_index. destruct st. cbn -[remove_first]. repeat (split; [reflexivity|]). reflexivity. Qed.

  Lemma idx_facts' : 0 <= idx < nsec st /\ nthz (st_sec st) idx (0,0) = (mb, n).
  Proof using WF HP PEND. unfold idx, sec_index. destruct st. eapply idx_facts; eauto. Qed.
  Lemma mbn_in_sec' : In (mb, n) (st_sec st).
  Proof using WF HP PEND. destruct st. eapply mbn_in_sec; eauto. Qed.
  Lemma A_in_blocks' : In (sec_user mb, n) (all_blocks st).
  Proof using WF HP PEND. destruct st. eapply A_in_blocks; eauto. Qed.
  Lemma dereg_nsec' : nsec stD = nsec st - 1.
  Proof using WF HP PEND. unfold stD. destruct st. eapply dereg_nsec; eauto. Qed.
  Lemma RTWF_dereg' : RTWF stD.
  Proof using WF HP PEND. unfold stD. destruct st. eapply RTWF_dereg; eauto. Qed.
  Lemma dereg_rel' : sec_dealloc_pend_rel st stD (sec_user mb) n mb.
  Proof using WF HP PEND. unfold stD. destruct st. eapply dereg_rel; eauto. Qed.
  Lemma rt_prov_dereg' : rt_prov stD + SEC_SLOT_TAX + 2 * smapsize n <= rt_prov st.
  Proof using WF HP PEND. unfold stD. destruct st. eapply rt_prov_dereg; eauto. Qed.
  Lemma RTMODEL_dereg' : forall moX, LOK asegs moX -> RTMODEL st moX -> RTMODEL stD (mm_unmap (wz mb) (wz (smapsize n)) moX).
  Proof using WF HP PEND. unfold stD. destruct st. intros. eapply RTMODEL_dereg; eauto. Qed.
  Lemma GWIN_dereg' : forall m mo g, GWIN st m mo g -> GWIN stD m mo g.
  Proof using WF HP PEND. unfold stD. destruct st. intros m mo g H. exact H. Qed.
  Lemma SWIN_dereg' : forall g, SWIN st g -> SWIN stD g.
  Proof using WF HP PEND. unfold stD. destruct st. eapply SWIN_dereg; eauto. Qed.
  Lemma RTSH_dereg' : forall x, RTSH stD x <-> RTSH st x.
  Proof using WF HP PEND. unfold stD. destruct st. intros x. unfold RTSH. cbn. tauto. Qed.
  Lemma mb_fresh' : forall r, In r (rt_ranges stD) -> mb + smapsize n <= fst r \/ snd r <= mb.
  Proof using WF HP PEND. unfold stD. destruct st. eapply mb_fresh; eauto. Qed.
  Lemma dereg_In_ranges' : forall r, In r (rt_ranges stD) -> In r (rt_ranges st).
  Proof using WF HP PEND. unfold stD. destruct st. eapply dereg_In_ranges; eauto. Qed.
  Lemma all_blocks_perm' : Permutation (all_blocks st) ((sec_user mb, n) :: all_blocks stD).
  Proof using WF HP PEND. unfold stD. destruct st. eapply all_blocks_perm; eauto. Qed.
  Lemma blocksD_sub' : forall x, In x (all_blocks stD) -> In x (all_blocks st).
  Proof using WF HP PEND. unfold stD. destruct st. eapply blocksD_sub; eauto. Qed.
  Lemma A_notin_blocksD' : forall n', ~ In (sec_user mb, n') (all_blocks stD).
  Proof using WF HP PEND. unfold stD. destruct st. eapply A_notin_blocksD; eauto. Qed.
  Lemma qelems_stD' : forall x, In x (qelems stD) -> In x (qelems st).
  Proof using WF HP PEND. unfold stD. destruct st. eapply qelems_sub; eauto. Qed.
  Lemma qpend_stD' : forall x, In x (st_qpend stD) -> In x (st_qpend st).
  Proof using WF HP PEND. unfold stD. destruct st. eapply qpend_sub; eauto. Qed.
  Lemma dereg_index' : forall x, In x (map fst (st_sec stD)) ->
    sec_index stD x = (if x =? fst (last (st_sec st) (0,0)) then (if idx <? nsec st - 1 then idx else sec_index st x) else sec_index st x)
    /\ 0 <= sec_index stD x < nsec st - 1 /\ nthz (st_sec stD) (sec_index stD x) (0,0) = nthz (st_sec st) (sec_index st x) (0,0).
  Proof using WF HP PEND. unfold stD, idx, sec_index. destruct st. cbn. intros x Hx. eapply dereg_index; eauto. Qed.
  Lemma secD_In' : forall e, In e (st_sec stD) -> In e (st_sec st) /\ e <> (mb, n).
  Proof using WF HP PEND.
    intros e He. pose proof st_secdereg_fields as (E1 & _). rewrite E1 in He. pose proof idx_facts' as [HI HN].
    split; [exact (sec_remove_In _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN e He)|].
    intros ->. exact (sec_remove_notin _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN He).
  Qed.
  Lemma secD_nth' : forall i, 0 <= i < nsec st - 1 ->
    nthz (st_sec stD) i (0,0) = if i =? idx then last (st_sec st) (0,0) else nthz (st_sec st) i (0,0).
  Proof using WF HP PEND.
    intros i Hi. pose proof st_secdereg_fields as (E1 & _). rewrite E1. pose proof idx_facts' as [HI HN].
    apply (sec_remove_nth _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN). unfold nsec in Hi. lia.
  Qed.
End W2P.


End CeilWrap.
