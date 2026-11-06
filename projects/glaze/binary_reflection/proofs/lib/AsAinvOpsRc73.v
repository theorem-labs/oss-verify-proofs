(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsD3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section D.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WFx (st : ast) (Lc FF : list (Z * Z)) : Prop := exists qt qg, WFq bt st Lc FF qt qg.








  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma existsb_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
  Proof.
    intros A f l l' P. destruct (existsb f l) eqn:E1; destruct (existsb f l') eqn:E2; try reflexivity.
    - apply existsb_exists in E1. destruct E1 as (x & Hx & Fx).
      assert (E3 : existsb f l' = true) by (apply existsb_exists; exists x; split; [eapply Permutation_in; [exact P | exact Hx] | exact Fx]). congruence.
    - apply existsb_exists in E2. destruct E2 as (x & Hx & Fx).
      assert (E3 : existsb f l = true) by (apply existsb_exists; exists x; split; [eapply Permutation_in; [apply Permutation_sym; exact P | exact Hx] | exact Fx]). congruence.
  Qed.

  Lemma drain_perm : forall st1, Permutation (a_tq (op_drain st1) ++ a_gq (op_drain st1)) (a_tq st1 ++ a_gq st1).
  Proof. intros st1. (lazymatch goal with |- ?G => let G' := eval unfold op_drain in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq set_tq app] in G in change_no_check G' end). apply Permutation_app_comm. Qed.
  Lemma drain_quar_perm : forall st1, Permutation (quar (op_drain st1)) (quar st1).
  Proof. intros st1. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply Permutation_flat_map. apply drain_perm. Qed.
  Lemma drain_in_batch : forall st1 a, in_batch (op_drain st1) a <-> in_batch st1 a.
  Proof.
    intros st1 a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). split; intros (b0 & Hb0 & E0); exists b0; split; try exact E0.
    - eapply Permutation_in; [exact (drain_perm st1) | exact Hb0].
    - eapply Permutation_in; [apply Permutation_sym; exact (drain_perm st1) | exact Hb0].
  Qed.
  Lemma drain_in_quar : forall st1 x, In x (quar (op_drain st1)) <-> In x (quar st1).
  Proof.
    intros st1 x. split; intros H.
    - eapply Permutation_in; [exact (drain_quar_perm st1) | exact H].
    - eapply Permutation_in; [apply Permutation_sym; exact (drain_quar_perm st1) | exact H].
  Qed.
  (* [comment removed for export] *)
  Theorem OPS_WFq_drain_pf : forall st1 Lc FF qt qg, WFq bt st1 Lc FF qt qg ->
    WFq bt (op_drain st1) Lc FF 0 (q_bytes (a_gq st1) + q_bytes (a_tq st1)).
  Proof.
    intros st1 Lc FF qt qg W.
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & _ & _ & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & LV & WK & WD & WM & WMP & G).
    set (st2 := op_drain st1).
    pose proof (drain_in_batch st1) as HBt. pose proof (drain_in_quar st1) as HQt. fold st2 in HBt, HQt.
    assert (HQc : forall c a, in_quar_c st2 c a <-> in_quar_c st1 c a).
    { intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split; intros (m & n' & Hq & X); exists m, n'; split; try exact X; apply HQt; exact Hq. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end). split; [| split; [exact WC | split; [| split; [| split; [exact LV | split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G]]]]]]]]].
    - (* [comment removed for export] *) split; [| exact WR2]. intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st2 c) with (a_reg st1 c). repeat (split; [assumption|]). split; [| exact FHK].
      apply (partition_ext bt st1 st2 Lc Lc c); [intros a; tauto | exact (HQc c) | exact HBt | reflexivity | reflexivity | exact PART].
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st2) with (@nil batch). change (a_gq st2) with (a_gq st1 ++ a_tq st1).
      change (wf_batch0 bt st2) with (wf_batch0 bt st1).
      split; [constructor|]. split; [rewrite Forall_app; split; [exact Q2 | eapply Forall_impl; [| exact Q1]; intros b0; apply wf_batch_0]|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [rewrite q_bytes_app; lia|].
      split. { (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). eapply Permutation_NoDup; [| exact Q5]. apply Permutation_map. apply Permutation_app_comm. }
      eapply Permutation_NoDup; [| exact Q6]. apply Permutation_map. apply Permutation_sym. exact (drain_quar_perm st1).
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st2) with (a_sec st1). change (a_nres st2) with (a_nres st1).
      change (registered st2) with (registered st1). repeat (split; [assumption|]).
      split. { intros s0 Hs. rewrite (HQt (sc_user s0 - 16, sc_n s0)). exact (S6 s0 Hs). }
      split; [exact S7|]. intros m n' Hq HP'. apply HQt in Hq. exact (S8 m n' Hq HP').
  Qed.



  Definition OPS_WF_drain : Prop := forall st1 Lc FF,
    WFx st1 Lc FF -> q_bytes (a_gq st1) + q_bytes (a_tq st1) <= 2 ^ 28 -> WF bt (op_drain st1) Lc FF.
  Theorem OPS_WF_drain_pf : OPS_WF_drain.
  Proof.
    intros st1 Lc FF (qt & qg & W) HB. apply (WFq_mono bt _ _ _ _ _ _ _ (OPS_WFq_drain_pf st1 Lc FF qt qg W)); lia.
  Qed.
End D.
End AsAinvOpsD3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsD23.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b AsAinvOpsD3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section D2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition foot_drain (gq : list batch) (a : Z) : Prop :=
    (T + T_QC <= a < T + T_QC + 32) \/ (IB bt + 880 <= a < IB bt + 888) \/ (IB bt + 888 <= a < IB bt + 920)
    \/ (match rev gq with [] => False | b :: _ => ba_addr b <= a < ba_addr b + 8 end) \/ (T + 2768 <= a < T + 3168) \/ CEIL <= a.

  (* [comment removed for export] *)
  Definition zl_lo (gq : list batch) : Z := match rev gq with [] => 0 | b :: _ => ba_addr b end.
  Definition zl_hi (gq : list batch) : Z := match rev gq with [] => 0 | b :: _ => ba_addr b + 8 end.
  Lemma zl_iff : forall gq a,
    (match rev gq with [] => False | b :: _ => ba_addr b <= a < ba_addr b + 8 end) <-> zl_lo gq <= a < zl_hi gq.
  Proof. intros gq a. (lazymatch goal with |- ?G => let G' := eval unfold zl_lo, zl_hi in G in change_no_check G' end). destruct (rev gq) as [|b r]; [split; [intros F; destruct F | lia] | tauto]. Qed.
  Lemma zl_last : forall gq a, zl_lo gq <= a < zl_hi gq -> exists g1 bl, gq = g1 ++ [bl] /\ ba_addr bl <= a < ba_addr bl + 8.
  Proof.
    intros gq a H. unfold zl_lo, zl_hi in H. destruct (rev gq) as [|bl rl] eqn:ER; [lia|].
    exists (rev rl), bl. split; [| exact H]. rewrite <- (rev_involutive gq), ER. (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). reflexivity.
  Qed.


  Definition OPS_REP_drain : Prop := forall st1 Lc FF M M' mdl mdl' tq1,
    WFx bt st1 Lc FF -> Rep bt st1 Lc FF M mdl -> a_tq st1 = tq1 -> tq1 <> [] ->
    agrees_off (foot_drain (a_gq st1)) M M' ->
    cellZ SG M' (T + T_QC) 8 0 -> cellZ SG M' (T + T_QC + 8) 8 0 -> cellZ SG M' (T + T_QC + 16) 8 0 -> cellZ SG M' (T + T_QC + 24) 8 0 ->
    byteZ SG M' (IB bt + 880) 0 -> byteZ SG M' (IB bt + 881) 0 ->
    cellZ SG M' (IB bt + 888) 8 (Z.of_nat (length (a_gq st1)) + Z.of_nat (length tq1)) ->
    (forall b0 q0, a_gq st1 ++ tq1 = b0 :: q0 -> cellZ SG M' (IB bt + 896) 8 (ba_addr b0)) ->
    (forall q1 bl, tq1 = q1 ++ [bl] -> cellZ SG M' (IB bt + 904) 8 (ba_addr bl)) ->
    cellZ SG M' (IB bt + 912) 8 (q_bytes (a_gq st1) + q_bytes tq1) ->
    (forall g1 bl b0 q0, a_gq st1 = g1 ++ [bl] -> tq1 = b0 :: q0 -> cellZ SG M' (ba_addr bl) 8 (ba_addr b0)) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st1) mdl' ->
    (* [comment removed for export] *)
    (a_gq st1 = [] -> forall a : word, IB bt + 896 <= bv_unsigned a < IB bt + 904 -> M' a <> None) ->
    Rep bt (op_drain st1) Lc FF M' mdl'.

  Theorem OPS_REP_drain_pf : OPS_REP_drain.
  Proof.
    intros st Lc FF M M' mdl mdl' tq1 (qt & qg & W) R Etq NE AGR CL0 CL8 CL16 CL24 B880 B881 CG0 CG8 CG16 CG24 CNX SBM MI FDEF.
    subst tq1.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _). box J1. box J2. box J3. box J4. box J5. box J6. box J7. box TPI. box TPB. box TPG.
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & DT & DR & _).
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    assert (ZLfacts : forall i, zl_lo (a_gq st) <= i < zl_hi (a_gq st) -> exists bl, In bl (a_tq st ++ a_gq st) /\ carved bt st BATCHCLASS (ba_addr bl)
                        /\ SBEG <= ba_addr bl /\ ba_addr bl + BATCHSZ <= SBEG + KSPACE /\ ba_addr bl <= i < ba_addr bl + 8
                        /\ (exists g1, a_gq st = g1 ++ [bl])).
    { intros i Zi. destruct (zl_last _ _ Zi) as (g1 & bl & Egq & Hi2).
      assert (Hbl2 : In bl (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Egq; apply in_app_iff; right; left; reflexivity).
      destruct (batch_facts bt st Lc FF W bl Hbl2) as (CVl & _ & Bl1 & Bl2). exists bl. repeat (split; [assumption|]). exists g1. exact Egq. }
    assert (ZLspace : forall i, zl_lo (a_gq st) <= i < zl_hi (a_gq st) -> SBEG <= i < SBEG + KSPACE).
    { intros i Zi. destruct (ZLfacts i Zi) as (bl & _ & _ & Bl1 & Bl2 & Hi2 & _). unfold BATCHSZ in Bl2. lia. }
    (* [comment removed for export] *)
    set (PIN := fun i : Z => (T + T_QC <= i < T + T_QC + 32) \/ (IB bt + 880 <= i < IB bt + 882) \/ (IB bt + 888 <= i < IB bt + 920)
                             \/ (zl_lo (a_gq st) <= i < zl_hi (a_gq st))).
    set (Mmid := fun a : word => if decide (PIN (u a)) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NEa. unfold Mmid in NEa |- *.
      destruct (decide (PIN (u a))) as [IN|NI]; [exfalso; exact (NEa eq_refl)|].
      destruct (AGR a NEa) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_drain in Hf. unfold PIN in NI.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]].
      - apply NI. left. exact Hf.
      - destruct (Z.lt_ge_cases (u a) (IB bt + 882)) as [LT|GE]; [apply NI; right; left; lia|].
        exact (instpad_not_cells bt st Lc FF W (u a) ltac:((lazymatch goal with |- ?G => let G' := eval unfold instpad in G in change_no_check G' end); lia) HC).
      - apply NI. right; right; left. exact Hf.
      - apply NI. right; right; right. apply zl_iff. exact Hf.
      - exact (stats_not_cells bt st Lc FF W (u a) Hf HC).
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    (* [comment removed for export] *)
    assert (AG : forall i, ~ PIN i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (decide (PIN i)) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (decide (PIN (u a))) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    (* [comment removed for export] *)
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    (* [comment removed for export] *)
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> ~ (IB bt + 880 <= i < IB bt + 920) -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn. apply AG; [| clear -Hi I1 I2; ulia]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|X]]].
      - clear -X Hi TPI. Zlia.
      - apply Hn. lia.
      - apply Hn. lia.
      - pose proof (ZLspace i X) as ZS. clear -ZS Hi I2 SBH. ulia. }
    assert (TPR : forall i, T <= i < T + PG -> ~ (T + T_QC <= i < T + T_QC + 32) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|X]]].
      - exact (Hn X).
      - clear -X Hi TPI INI. Zlia.
      - clear -X Hi TPI INI. Zlia.
      - pose proof (ZLspace i X) as ZS. clear -ZS Hi TPG. Zlia. }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG ->
                   forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin Hlen Hpg i Hi Hr. apply AG; [| exact Hr].
      destruct (fixed_range bt st Lc FF W lo hi Hin) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen) as [SP|SP]; (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|X]]].
      1,5: clear -X Hi D; unfold T_QC in X; ulia.
      1,2,4,5: clear -X Hi D4 INI; ulia.
      1,2: pose proof (ZLspace i X) as ZS; clear -ZS Hi SP; ulia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi Hr. apply AG; [| exact Hr].
      destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hin) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hin) as [SP|SP]; (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|X]]].
      1,5: clear -X Hi D; unfold T_QC in X; ulia.
      1,2,4,5: clear -X Hi D4 INI; ulia.
      1,2: pose proof (ZLspace i X) as ZS; clear -ZS Hi SP; ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE + PG -> ~ (zl_lo (a_gq st) <= i < zl_hi (a_gq st)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|X]]].
      - clear -X Hi TPG. Zlia.
      - clear -X Hi SBH INI I2. ulia.
      - clear -X Hi SBH INI I2. ulia.
      - exact (Hn X). }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|X]]].
      - clear -X Hi TPB. Zlia.
      - clear -X Hi INI I2. ulia.
      - clear -X Hi INI I2. ulia.
      - pose proof (ZLspace i X) as ZS. clear -ZS Hi SBH. ulia. }
    (* [comment removed for export] *)
    assert (CH24vsFA : forall a c0 i, carved bt st BATCHCLASS a -> 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> ~ (a <= i < a + 8192)).
    { intros a c0 i CVa Hc0 Hi Hin2. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      destruct (carved_range bt st Lc FF W BATCHCLASS a HC24 CVa) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2.
      pose proof (region_facts bt st Lc FF W BATCHCLASS HC24) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 BATCHCLASS) as [LT|[->|GT]]; [| ulia |].
      * assert (c0 * 2 ^ 32 + 2 ^ 32 <= BATCHCLASS * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia.
      * assert (BATCHCLASS * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (BATCHCLASS * 2 ^ 32 + 2 ^ 32) with ((BATCHCLASS + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia. }
    (* [comment removed for export] *)
    destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). pose proof PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
    (* [comment removed for export] *)
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> ba_addr b0 <= i < ba_addr b0 + BATCHSZ ->
                 (forall g1 bl, a_gq st = g1 ++ [bl] -> b0 = bl -> ba_addr bl + 8 <= i) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi ZOK Hr. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3).
      apply SPCR; [clear -Hi BL2 BL3; ulia | | exact Hr]. intros Zi.
      destruct (ZLfacts i Zi) as (bl & Hbl2 & CVl & Bl1 & Bl2 & Hi2 & (g1 & Egq)).
      destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr b0) BATCHCLASS (ba_addr bl) HC24 HC24 CVb CVl) as [[_ EA] | D].
      - pose proof (NoDup_map_inj ba_addr (a_tq st ++ a_gq st) b0 bl WQ5 Hb0 Hbl2 EA) as Eb. pose proof (ZOK g1 bl Egq Eb). lia.
      - change (csize BATCHCLASS) with 8192 in D. unfold BATCHSZ in *. lia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    (* [comment removed for export] *)
    assert (HDRR : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply SPCR; [clear -W1 W2 W3 W4 N1'; ulia | | exact Hr]. intros Zi.
        destruct (ZLfacts i Zi) as (bl & Hbl2 & CVl & Bl1 & Bl2 & Hi2 & _).
        destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg p' n') BATCHCLASS (ba_addr bl) HC' HC24 CV' CVl) as [[EC EA] | D].
        + apply (NBL (ba_addr bl) ltac:(exists bl; split; [exact Hbl2 | reflexivity]) eq_refl). rewrite <- EC, <- EA.
          destruct Hown as [Hown|Hown].
          * left. pose proof (live_chunk bt st Lc FF W p' n' Hown HP') as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & G3 & _). exact G3.
          * right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' Hown HP') as Gv. cbn zeta in Gv. replace (p' - 16 + 16) with p' in Gv by lia.
            destruct Gv as (_ & _ & G3 & _). exact G3.
        + change (csize BATCHCLASS) with 8192 in D. clear -D W1 W2 W3 W4 Hi2 N1' RZ'. unfold prim_alloc_beg in *. lia.
      - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
    (* [comment removed for export] *)
    clear WR2 WC WQ1 WQ2 WQ3 WQ4 WQ6 S2 S4 S5 S6 S7 S8 LV1 LV3 WK WD WM' RNG PW' R6a R6b IN6 G PARTB NBL.
    set (st' := op_drain st).
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in DC.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _].
             apply (IMGR i LT). intros X. apply (DC c0 Hc0 i Hi). (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). unfold IB in X.
             destruct (Z.lt_ge_cases i (ia_instance IA + 888)); [right; left; lia | right; right; left; lia]. }
    (* [comment removed for export] *)
    split. { destruct P2 as (I1' & I2' & I3 & I4 & I5 & I6 & IL & IP & IW). (lazymatch goal with |- ?G => let G' := eval unfold rep_instance in G in change_no_check G' end).
             change (a_nres st') with (a_nres st). change (a_sec st') with (a_sec st). change (a_gq st') with (a_gq st ++ a_tq st).
             assert (AGI : forall i, ((IB bt + 112 <= i < IB bt + 880) \/ (IB bt + 920 <= i < IB bt + 985)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply IMGR; clear -Hi INI; lia. }
             split; [frZ AGI I1'|]. split; [frZ AGI I2'|]. split; [frB AGI I3|]. split; [exact B880|]. split; [exact B881|]. split; [frB AGI I6|].
             split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). rewrite length_app, Nat2Z.inj_add.
                      replace (IB bt + 888 + 8) with (IB bt + 896) by lia. replace (IB bt + 888 + 16) with (IB bt + 904) by lia. replace (IB bt + 888 + 24) with (IB bt + 912) by lia.
                      split; [exact CG0|].
                      split. { destruct (a_gq st ++ a_tq st) as [|b0 q0] eqn:E0; [exfalso; apply NE; destruct (a_tq st); [reflexivity | destruct (a_gq st); discriminate E0]|].
                               exact (CG8 b0 q0 eq_refl). }
                      split. { rewrite rev_app_distr. destruct (rev (a_tq st)) as [|bl rl] eqn:ER; [exfalso; apply NE; rewrite <- (rev_involutive (a_tq st)), ER; reflexivity|].
                               (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). apply (CG16 (rev rl) bl). rewrite <- (rev_involutive (a_tq st)), ER. reflexivity. }
                      rewrite q_bytes_app. exact CG24. }
             split. { intros i s Hs. pose proof (nth_error_lt _ _ _ Hs) as Hl. pose proof (IP i s Hs) as C.
                      eapply (cellZ_frame _ _ _ _ _ _ C); [lia | lia |]. intros j Hj. apply (FIXR _ _ IN8); [ulia | ulia | clear -Hj Hl S1 S3; lia | lia]. }
             frW DEF IW. }
    (* [comment removed for export] *)
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (@nil batch). change (a_cinit st') with (a_cinit st). change (a_cache st') with (a_cache st).
             assert (AGT : forall i, (T <= i < T + T_QC \/ T + T_QC + 32 <= i < T + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply TPR; [clear -Hi; unfold T_QC, PG in *; lia | clear -Hi; lia | exact Hr]. }
             assert (AGC : forall i, bt_tctx bt <= i < bt_tctx bt + 160 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply (FIXR _ _ INC); [ulia | ulia | clear -Hi; lia | exact Hr]. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length rev q_bytes fold_right Z.of_nat] in G in change_no_check G' end). split; [exact CL0|]. split; [exact CL8|]. split; [exact CL16 | exact CL24]. }
             split. { intros c' Hc'. pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                      eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                      unfold T_PC, PC_SZ in *. intros i Hi Hr. apply AGT; [| exact Hr]. right. clear -Hi Hc'. nia. }
             split; [frW DEF TW|]. split; [frZ AGC TC1|]. split; [frZ AGC TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi].
             - apply SPCR; [clear -Hi E9 E10; ulia | intros Zi; pose proof (ZLspace i Zi) as ZS; clear -ZS Hi E9; ulia | exact Hr].
             - apply SPCR; [clear -Hi E1 E2 E5 E6 E7 E8; ulia | | exact Hr]. intros Zi.
               destruct (ZLfacts i Zi) as (bl & Hbl2 & CVl & Bl1 & Bl2 & Hi2 & _).
               exact (CH24vsFA (ba_addr bl) c0 i CVl Hc0 ltac:(clear -Hi E6 E7; lia) ltac:(clear -Hi2; lia)). }
    (* [comment removed for export] *)
    split. { change (a_tq st') with (@nil batch). intros i b Hb. destruct i; discriminate Hb. }
    (* [comment removed for export] *)
    split. { change (a_gq st') with (a_gq st ++ a_tq st). intros i b0 Hb0.
             destruct (Nat.lt_ge_cases i (length (a_gq st))) as [LT | GE].
             - rewrite nth_error_app1 in Hb0 by exact LT.
               assert (Hin0 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; exact (nth_error_In _ _ Hb0)).
               destruct (BR b0 Hin0) as (Q1 & Q2 & Q3). destruct (P6 i b0 Hb0) as (C1 & C2 & C3 & C4 & CW). unfold BATCHSZ, BATCHCAP in Q2, Q3.
               assert (AGb : forall j, ba_addr b0 + 8 <= j < ba_addr b0 + 24 + 8 * Z.of_nat (length (ba_items b0)) -> 0 <= j < 2 ^ 64 -> M' (Z_to_bv 64 j) = Mmid (Z_to_bv 64 j)).
               { intros j Hj Hrj. apply (BA b0 j Hin0); [(lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia | intros g1 bl _ E; rewrite <- E; lia | exact Hrj]. }
               split. { destruct (Nat.eq_dec (S i) (length (a_gq st))) as [EL | NEL].
                        - (* [comment removed for export] *)
                          rewrite nth_error_app2, EL, Nat.sub_diag by lia.
                          assert (Egq : a_gq st = firstn i (a_gq st) ++ [b0]).
                          { rewrite <- (firstn_skipn i (a_gq st)) at 1. f_equal.
                            destruct (skipn i (a_gq st)) as [|x r] eqn:ES.
                            + exfalso. pose proof (f_equal (@length batch) ES) as LL. rewrite length_skipn in LL. cbn in LL. lia.
                            + pose proof (f_equal (@length batch) ES) as LL. rewrite length_skipn in LL. cbn in LL.
                              assert (r = []) by (destruct r; [reflexivity | cbn in LL; lia]). subst r. f_equal.
                              pose proof (nth_error_skipn i (a_gq st) 0%nat) as NS. rewrite ES, Nat.add_0_r in NS. cbn in NS. congruence. }
                          destruct (a_tq st) as [|t0 q0] eqn:ET; [exfalso; exact (NE eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [nth_error] in G in change_no_check G' end).
                          exact (CNX _ _ t0 q0 Egq eq_refl).
                        - rewrite nth_error_app1 by lia.
                          eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | lia |]. intros j Hj. apply (BA b0 j Hin0); [(lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia | | lia].
                          intros g1 bl Egq Ebl. exfalso. subst b0. apply NEL.
                          pose proof (f_equal (@length batch) Egq) as LL. rewrite length_app in LL. cbn in LL.
                          assert (NDg : List.NoDup (a_gq st)).
                          { apply (NoDup_map_inv ba_addr). rewrite map_app in WQ5. exact (NoDup_app_remove_l _ _ WQ5). }
                          rewrite Egq in Hb0.
                          destruct (Nat.lt_ge_cases i (length g1)) as [LT2 | GE2].
                          + exfalso. rewrite nth_error_app1 in Hb0 by exact LT2. rewrite Egq in NDg.
                            apply (NoDup_remove_2 g1 [] bl); [exact NDg | rewrite app_nil_r; exact (nth_error_In _ _ Hb0)].
                          + lia. }
               split; [frZ AGb C2|]. split; [frZ AGb C3|]. split; [| frW DEF CW].
               intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (C4 j mn Hj) as CC4. frZ AGb CC4.
             - (* [comment removed for export] *)
               rewrite nth_error_app2 in Hb0 by exact GE.
               assert (Hin0 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact (nth_error_In _ _ Hb0)).
               destruct (BR b0 Hin0) as (Q1 & Q2 & Q3). destruct (P5 _ b0 Hb0) as (C1 & C2 & C3 & C4 & CW). unfold BATCHSZ, BATCHCAP in Q2, Q3.
               assert (AGb : forall j, ba_addr b0 <= j < ba_addr b0 + 24 + 8 * Z.of_nat (length (ba_items b0)) -> 0 <= j < 2 ^ 64 -> M' (Z_to_bv 64 j) = Mmid (Z_to_bv 64 j)).
               { intros j Hj Hrj. apply (BA b0 j Hin0); [(lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia | | exact Hrj].
                 intros g1 bl Egq ->. exfalso. rewrite Egq, map_app, map_app in WQ5. cbn [map] in WQ5.
                 rewrite app_assoc in WQ5. apply (NoDup_remove_2 _ _ _ WQ5). rewrite app_nil_r. apply in_app_iff. left. apply in_map. exact (nth_error_In _ _ Hb0). }
               split. { rewrite nth_error_app2 by lia. replace (S i - length (a_gq st))%nat with (S (i - length (a_gq st))) by lia. frZ AGb C1. }
               split; [frZ AGb C2|]. split; [frZ AGb C3|]. split; [| frW DEF CW].
               intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (C4 j mn Hj) as CC4. frZ AGb CC4. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRR p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq'. pose proof (proj1 (drain_in_quar st (m0, n')) Hq') as Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRR (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. apply (IMGR i LT).
               unfold foot_depot_static in Hi. unfold DEPOT_NIDS, DEPOT_MAP1 in Hi. unfold IB, DEPOT_TAB, SSOBJ in *. clear -Hi J1 J2. Zlia.
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | clear -Hi; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. apply (IMGR i LT). unfold IB in *. clear -Hi J5. Zlia.
               + (* [comment removed for export] *)
                 destruct (dtls_cell_facts bt st Lc FF W i Hi) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7).
                 apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|X]]].
                 * apply DF5. clear -X. unfold T_QC, PG in *. lia.
                 * apply DF3. clear -X INI. lia.
                 * apply DF3. clear -X INI. lia.
                 * pose proof (ZLspace i X) as ZS. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6' & R6a' & R6b' & _) & _).
                   apply (DF6 _ _ IN6'); [clear -R6a' R6b'; unfold KSPACE, PG in *; lia | clear -ZS R6a' R6b'; unfold KSPACE, PG in *; lia].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. apply (IMGR i LT).
             unfold ialloc_cells in Hi. unfold IB, IA_FLAG, IA_INST, IASZ in *. clear -Hi J3 J4. Zlia. }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st).
             assert (EXQ : forall g, existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st')
                               = existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st)).
             { intros g. apply existsb_perm. exact (drain_quar_perm st). }
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. rewrite EXQ. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs HQ' HU. pose proof (proj1 (drain_in_quar st _) HQ') as HQ.
                      pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM P13). }
    (* [comment removed for export] *)
    split. { destruct P14 as (BU1 & BU2 & BU3 & BU4 & BU5 & BU6 & BU7 & BU8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st).
             change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact BU1|]. split; [exact MI|]. split; [exact BU3|]. split; [exact BU4|]. split; [exact BU5|]. split; [exact BU6|]. split; [exact BU7|].
             rewrite E3. change (prim_charge st') with (prim_charge st). change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st). exact BU8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    assert (RTC : forall i, ia_rtc_sb IA <= i < ia_rtc_sb IA + 8 \/ ia_rtc_uar IA <= i < ia_rtc_uar IA + 4 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. destruct (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); exact Hi)) as [LT _]. apply (IMGR i LT).
      unfold IB in *. clear -Hi J6 J7. Zlia. }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; apply RTC; left; cbn in Hi; lia] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; apply RTC; right; cbn in Hi; lia] |].
    split; [intros z Hz; exact (def_keep Mmid M' _ DEF (proj1 P19 z Hz))|].
    intros _ a Ha. assert (C : a_gq st = [] \/ a_gq st <> []) by (destruct (a_gq st); [left; reflexivity | right; discriminate]).
    destruct C as [E0 | NE0]; [exact (FDEF E0 a Ha) | apply (def_keep Mmid M' a DEF); exact (proj2 P19 NE0 a Ha)].
  Qed.
End D2.
End AsAinvOpsD23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvRepX3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Xdec (X : Z -> Prop) : Type := forall z : Z, {X z} + {~ X z}.
Lemma Xdec_iv : forall lo hi, Xdec (fun z => lo <= z < hi).
Proof. intros lo hi z. destruct (Z_le_dec lo z); [destruct (Z_lt_dec z hi); [left; lia | right; lia] | right; lia]. Defined.
Lemma Xdec_or : forall X Y, Xdec X -> Xdec Y -> Xdec (fun z => X z \/ Y z).
Proof. intros X Y DX DY z. destruct (DX z); [left; left; assumption|]. destruct (DY z); [left; right; assumption | right; tauto]. Defined.
Lemma Xdec_and : forall X Y, Xdec X -> Xdec Y -> Xdec (fun z => X z /\ Y z).
Proof. intros X Y DX DY z. destruct (DX z); [| right; tauto]. destruct (DY z); [left; tauto | right; tauto]. Defined.

Lemma Xdec_false : Xdec (fun _ => False).
Proof. intros z. right. tauto. Defined.
Lemma Xdec_ex_list : forall {A} (l : list A) (P : A -> Z -> Prop), (forall x, Xdec (P x)) -> Xdec (fun z => exists x, In x l /\ P x z).
Proof.
  intros A l P DP z. induction l as [|x t IH].
  - right. intros (y & [] & _).
  - destruct (DP x z) as [Hx | Nx]; [left; exists x; split; [left; reflexivity | exact Hx]|].
    destruct IH as [E | N]; [left; destruct E as (y & Hy & Py); exists y; split; [right; exact Hy | exact Py]|].
    right. intros (y & [<- | Hy] & Py); [exact (Nx Py) | apply N; exists y; exact (conj Hy Py)].
Defined.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put8 (M : mem) (a v : Z) : mem := wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition put4 (M : mem) (a v : Z) : mem := wbytes M (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 v)).

Section Put.
  Variable SEGS : list Segment.
  Lemma put8_hit : forall M a v, 0 <= a -> a + 8 <= 2 ^ 64 -> cellZ SEGS (put8 M a v) a 8 v.
  Proof. intros M a v H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, put8 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
  Lemma put4_hit : forall M a v, 0 <= a -> a + 4 <= 2 ^ 64 -> cellZ SEGS (put4 M a v) a 4 v.
  Proof.
    intros M a v H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, put4 in G in change_no_check G' end).
    pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 v)) M (Z_to_bv 64 a)) as H.
    rewrite length_N_to_le_bytes in H. apply H. rewrite u64_lit by lia. lia.
  Qed.
  Lemma put8_out : forall M a v (x : word), 0 <= a -> a + 8 <= 2 ^ 64 -> (u x < a \/ a + 8 <= u x) -> put8 M a v x = M x.
  Proof.
    intros M a v x H0 H1 Hx. (lazymatch goal with |- ?G => let G' := eval unfold put8 in G in change_no_check G' end). destruct Hx as [Hx | Hx].
    - apply wbytes_below; rewrite ?length_N_to_le_bytes, u64_lit by lia; lia.
    - apply wbytes_above. rewrite length_N_to_le_bytes, u64_lit by lia. lia.
  Qed.
  Lemma put4_out : forall M a v (x : word), 0 <= a -> a + 4 <= 2 ^ 64 -> (u x < a \/ a + 4 <= u x) -> put4 M a v x = M x.
  Proof.
    intros M a v x H0 H1 Hx. (lazymatch goal with |- ?G => let G' := eval unfold put4 in G in change_no_check G' end). destruct Hx as [Hx | Hx].
    - apply wbytes_below; rewrite ?length_N_to_le_bytes, u64_lit by lia; lia.
    - apply wbytes_above. rewrite length_N_to_le_bytes, u64_lit by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma wbytes_in_def : forall bs M (ad x : word), u ad + Z.of_nat (length bs) <= 2 ^ 64 -> u ad <= u x < u ad + Z.of_nat (length bs) ->
    wbytes M ad bs x <> None.
  Proof.
    induction bs as [|b t IH]; intros M ad x Hn Hx; [cbn in Hx; lia|].
    (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end). cbn [length] in Hn, Hx. destruct (Z.eq_dec (u x) (u ad)) as [E | NE].
    - assert (x = ad) by (apply bv_eq; exact E). subst x.
      destruct t as [|b' t']; [(lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end); rewrite bv_eqb_refl; discriminate|].
      cbn [length] in Hn. rewrite wbytes_below.
      + rewrite bv_eqb_refl. discriminate.
      + rewrite u_add1 by lia. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
      + rewrite u_add1 by lia. lia.
    - pose proof (u64_range x) as Rx. apply IH; rewrite u_add1 by lia; lia.
  Qed.
  Lemma put8_def : forall M a v (x : word), 0 <= a -> a + 8 <= 2 ^ 64 -> a <= u x < a + 8 -> put8 M a v x <> None.
  Proof. intros M a v x H0 H1 Hx. (lazymatch goal with |- ?G => let G' := eval unfold put8 in G in change_no_check G' end). apply wbytes_in_def; rewrite length_N_to_le_bytes, u64_lit by lia; lia. Qed.
  Lemma put4_def : forall M a v (x : word), 0 <= a -> a + 4 <= 2 ^ 64 -> a <= u x < a + 4 -> put4 M a v x <> None.
  Proof. intros M a v x H0 H1 Hx. (lazymatch goal with |- ?G => let G' := eval unfold put4 in G in change_no_check G' end). apply wbytes_in_def; rewrite length_N_to_le_bytes, u64_lit by lia; lia. Qed.
End Put.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RX.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Definition RepX (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) : Prop :=
    exists M0, Rep bt st Lc FF M0 mdl /\ forall a : word, M a <> M0 a -> X (u a) /\ M a <> None.


  Lemma RepX_mono : forall (X X' : Z -> Prop) st Lc FF M mdl, (forall z, X z -> X' z) ->
    RepX X st Lc FF M mdl -> RepX X' st Lc FF M mdl.
  Proof. intros X X' st Lc FF M mdl S (M0 & R & D). exists M0. split; [exact R|]. intros a Ha. destruct (D a Ha) as [Hx Hd]. exact (conj (S _ Hx) Hd). Qed.


  (* [comment removed for export] *)
  Theorem RepX_close : forall X st Lc FF M mdl {qt qg : Z}, WFq bt st Lc FF qt qg ->
    RepX X st Lc FF M mdl -> (forall z, X z -> ~ rep_cells bt st Lc FF z) -> Rep bt st Lc FF M mdl.
  Proof.
    intros X st Lc FF M mdl qt qg W (M0 & R & D) NC.
    apply (Rep_frame_q bt st Lc FF M0 M mdl W R). intros a Ha. destruct (D a Ha) as [Hx Hd]. exact (conj (NC _ Hx) Hd).
  Qed.

  (* [comment removed for export] *)
  Theorem RepX_lift : forall (X RES FOOT : Z -> Prop) (Xd : Xdec X) (Rd : Xdec RES) st st' Lc Lc' FF FF' (M M' : mem) mdl mdl',
    RepX X st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> FOOT (u a) /\ M' a <> None) ->
    (forall z, FOOT z -> X z -> RES z) ->
    (forall z (a : word), RES z -> u a = z -> M' a <> None) ->
    (forall M0 M0' : mem, Rep bt st Lc FF M0 mdl ->
        (forall a : word, M0' a <> M0 a -> (FOOT (u a) \/ RES (u a)) /\ M0' a <> None) ->
        (forall a : word, ~ X (u a) \/ RES (u a) -> M0' a = M' a) ->
        Rep bt st' Lc' FF' M0' mdl') ->
    RepX (fun z => X z /\ ~ RES z) st' Lc' FF' M' mdl'.
  Proof.
    intros X RES FOOT Xd Rd st st' Lc Lc' FF FF' M M' mdl mdl' (M0 & R & D) STEPM FX RDEF STEP.
    set (M0' := fun a : word => if Xd (u a) then (if Rd (u a) then M' a else M0 a) else M' a).
    assert (OFFX : forall a : word, ~ X (u a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E | NE]; [exact E|]. exfalso. exact (NX (proj1 (D a NE))). }
    exists M0'. split.
    - apply (STEP M0 M0' R).
      + intros a Ha. unfold M0' in Ha |- *. destruct (Xd (u a)) as [HX | NX].
        * destruct (Rd (u a)) as [HR | NR]; [| exfalso; exact (Ha eq_refl)].
          split; [right; exact HR | exact (RDEF _ a HR eq_refl)].
        * rewrite <- (OFFX a NX) in Ha. destruct (STEPM a Ha) as [F Dd]. exact (conj (or_introl F) Dd).
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Xd (u a)) as [HX | NX]; [| reflexivity].
        destruct (Rd (u a)) as [HR | NR]; [reflexivity|]. destruct Ha as [Ha | Ha]; [exfalso; exact (Ha HX) | exfalso; exact (NR Ha)].
    - intros a Ha. unfold M0' in Ha. destruct (Xd (u a)) as [HX | NX]; [| exfalso; exact (Ha eq_refl)].
      destruct (Rd (u a)) as [HR | NR]; [exfalso; exact (Ha eq_refl)|].
      split; [exact (conj HX NR)|].
      destruct (decide (M' a = M a)) as [E | NE].
      + rewrite E. rewrite E in Ha. exact (proj2 (D a Ha)).
      + exact (proj2 (STEPM a NE)).
  Qed.
End RX.
End AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsRc23.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b AsAinvOpsD3 AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition rm_lo (rm : option (Z * Z)) : Z := match rm with Some (m, n) => prim_alloc_beg (m + 16) n | None => 0 end.
Definition rm_hi (rm : option (Z * Z)) : Z := match rm with Some (m, n) => prim_alloc_beg (m + 16) n + csize (blk_class n) | None => 0 end.
Definition rms_lo (rm : option (Z * Z)) : Z := match rm with Some (m, n) => sh_lo (m + 16) | None => 0 end.
Definition rms_hi (rm : option (Z * Z)) : Z := match rm with Some (m, n) => sh_hi (m + 16) n | None => 0 end.

Lemma existsb_minus : forall {A} (f : A -> bool) (l l' : list A) (rm : option A),
  (forall x, In x l' <-> In x l /\ Some x <> rm) -> (forall x, rm = Some x -> f x = false) -> existsb f l' = existsb f l.
Proof.
  intros A f l l' rm E F. apply eq_true_iff_eq. rewrite !existsb_exists. split.
  - intros (x & Hx & Fx). exists x. split; [exact (proj1 (proj1 (E x) Hx)) | exact Fx].
  - intros (x & Hx & Fx). exists x. split; [| exact Fx]. apply E. split; [exact Hx|]. intros Er. rewrite (F x (eq_sym Er)) in Fx. discriminate Fx.
Qed.

Section RC2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Definition qhdr (z : Z) : Prop := IB bt + 888 <= z < IB bt + 920.
  Definition gq_objs (st : ast) (z : Z) : Prop := exists b, In b (a_gq st) /\ ba_addr b <= z < ba_addr b + BATCHSZ.
  Definition pc_entry (c z : Z) : Prop := T + T_PC + PC_SZ * c <= z < T + T_PC + PC_SZ * c + PC_SZ.
  Definition foot_gqpush (st : ast) (c : Z) (rm : option (Z * Z)) (z : Z) : Prop :=
    qhdr z \/ gq_objs st z \/ pc_entry c z \/ (rm_lo rm <= z < rm_hi rm) \/ (rms_lo rm <= z < rms_hi rm)
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REP_gqpush : Prop := forall st Lc FF (M M' : mem) mdl mdl' gq' c ks' rm (qt qg : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 ->
    (forall x, In x (flat_map ba_items gq') <-> In x (flat_map ba_items (a_gq st)) /\ Some x <> rm) ->
    (forall m n, rm = Some (m, n) -> In (m, n) (flat_map ba_items (a_gq st)) /\ is_primary n = true) ->
    agrees_off (foot_gqpush st c rm) M M' ->
    rep_list bt M' (IB bt + 888) gq' -> rep_batches bt M' gq' -> rep_pclass bt M' T (a_cinit st) c ks' ->
    (forall m n, rm = Some (m, n) -> fillZ SG M' (sh_lo (m + 16)) (sh_hi (m + 16) n) FA) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    (* [comment removed for export] *)
    (gq' <> [] -> a_gq st <> [] \/ forall a : word, IB bt + 896 <= bv_unsigned a < IB bt + 904 -> M' a <> None) ->
    Rep bt (set_cache (set_gq st gq') c ks') Lc FF M' mdl'.

  Lemma PINdec : forall st c rm, Xdec (fun i => qhdr i \/ gq_objs st i \/ pc_entry c i \/ (rm_lo rm <= i < rm_hi rm) \/ (rms_lo rm <= i < rms_hi rm)).
  Proof.
    intros st c rm. apply Xdec_or; [apply Xdec_iv|]. apply Xdec_or; [| apply Xdec_or; [apply Xdec_iv | apply Xdec_or; apply Xdec_iv]].
    (lazymatch goal with |- ?G => let G' := eval unfold gq_objs in G in change_no_check G' end). apply (Xdec_ex_list (a_gq st) (fun b z => ba_addr b <= z < ba_addr b + BATCHSZ)). intros b. apply Xdec_iv.
  Qed.

  Theorem OPS_REP_gqpush_pf : OPS_REP_gqpush.
  Proof.
    intros st Lc FF M M' mdl mdl' gq' c ks' rm qt qg W R Hc QREL RMIN AGR NLIST NBAT NPC SHFA SBM MI GQD.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _). box J1. box J2. box J3. box J4. box J5. box J6. box J7. box TPI. box TPB. box TPG.
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & DT & DR & _).
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    set (st' := set_cache (set_gq st gq') c ks').
    assert (QSUB : forall x, In x (quar st') <-> In x (quar st) /\ Some x <> rm).
    { intros x. (lazymatch goal with |- ?G => let G' := eval unfold quar, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_cache set_gq] in G in change_no_check G' end). rewrite !flat_map_app, !in_app_iff, (QREL x). split.
      - intros [X | [X Y]]; [| tauto]. split; [left; exact X|]. intros E. destruct x as [m n]. destruct (RMIN m n (eq_sym E)) as [Hin _].
        assert (A1 : In (m, n) (flat_map ba_items (a_tq st) ++ flat_map ba_items (a_gq st))) by (apply in_app_iff; left; exact X).
        unfold quar in WQ6. rewrite flat_map_app, map_app in WQ6.
        destruct (in_split _ _ X) as (l1 & l2 & EX). rewrite EX, map_app in WQ6. cbn [map fst] in WQ6. rewrite <- app_assoc in WQ6. cbn [app] in WQ6.
        apply (NoDup_remove_2 _ _ _ WQ6). apply in_app_iff. right. apply in_app_iff. right. apply (in_map fst _ _ Hin).
      - tauto. }
    (* [comment removed for export] *)
    assert (GQfacts : forall i, gq_objs st i -> exists b, In b (a_tq st ++ a_gq st) /\ In b (a_gq st) /\ carved bt st BATCHCLASS (ba_addr b)
                        /\ SBEG <= ba_addr b /\ ba_addr b + BATCHSZ <= SBEG + KSPACE /\ ba_addr b <= i < ba_addr b + BATCHSZ).
    { intros i (b & Hb & Hi). assert (Hb2 : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; exact Hb).
      destruct (batch_facts bt st Lc FF W b Hb2) as (CVb & _ & Bl1 & Bl2). exists b. repeat (split; [assumption|]). exact Hi. }
    assert (GQspace : forall i, gq_objs st i -> SBEG <= i < SBEG + KSPACE).
    { intros i Gi. destruct (GQfacts i Gi) as (b & _ & _ & _ & Bl1 & Bl2 & Hi). lia. }
    (* [comment removed for export] *)
    assert (RMfacts : forall i, rm_lo rm <= i < rm_hi rm \/ rms_lo rm <= i < rms_hi rm -> exists m n, rm = Some (m, n) /\ In (m, n) (quar st) /\ is_primary n = true
                        /\ 1 <= blk_class n <= 30 /\ carved bt st (blk_class n) (prim_alloc_beg (m + 16) n) /\ in_quar_c st (blk_class n) (prim_alloc_beg (m + 16) n)
                        /\ prim_alloc_beg (m + 16) n + rz n = m + 16 /\ m + 16 + n <= prim_alloc_beg (m + 16) n + csize (blk_class n)
                        /\ SBEG <= prim_alloc_beg (m + 16) n /\ prim_alloc_beg (m + 16) n + csize (blk_class n) <= SBEG + KSPACE /\ prim_alloc_beg (m + 16) n mod 16 = 0 /\ 1 <= n).
    { intros i Hi. destruct rm as [[m n]|]; [| unfold rm_lo, rm_hi, rms_lo, rms_hi in Hi; lia]. exists m, n. split; [reflexivity|].
      destruct (RMIN m n eq_refl) as [Hin HP].
      assert (Hq : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact Hin).
      pose proof (quar_chunk bt st Lc FF W m n Hq HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
      destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _).
      repeat (split; [assumption|]). lia. }
    assert (RMspace : forall i, rm_lo rm <= i < rm_hi rm -> SBEG <= i < SBEG + KSPACE).
    { intros i Hi. destruct (RMfacts i (or_introl Hi)) as (m & n & E & _ & _ & _ & _ & _ & _ & _ & C3 & C4 & _). subst rm. unfold rm_lo, rm_hi in Hi. lia. }
    assert (RMSband : forall i, rms_lo rm <= i < rms_hi rm -> SB <= i < AS_HEAPLO).
    { intros i Hi. destruct (RMfacts i (or_intror Hi)) as (m & n & E & _ & _ & _ & _ & _ & G4 & G5 & C3 & C4 & _ & N1). subst rm. unfold rms_lo, rms_hi, sh_lo, sh_hi in Hi.
      pose proof (rz_range n) as RZ. clear -Hi G4 G5 C3 C4 N1 RZ B6 B7 SP1 SP2 SP3 SBH X14 X15. Zlia. }
    (* [comment removed for export] *)
    set (PIN := fun i : Z => qhdr i \/ gq_objs st i \/ pc_entry c i \/ (rm_lo rm <= i < rm_hi rm) \/ (rms_lo rm <= i < rms_hi rm)).
    pose proof (PINdec st c rm) as PINd. fold PIN in PINd.
    set (Mmid := fun a : word => if PINd (u a) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NEa. unfold Mmid in NEa |- *.
      destruct (PINd (u a)) as [IN|NI]; [exfalso; exact (NEa eq_refl)|].
      destruct (AGR a NEa) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_gqpush in Hf. unfold PIN in NI.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]]]; [tauto | tauto | tauto | tauto | tauto | |].
      - exact (stats_not_cells bt st Lc FF W (u a) Hf HC).
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    (* [comment removed for export] *)
    assert (AG : forall i, ~ PIN i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (PINd i) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (PINd (u a)) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    assert (PCT : forall i, pc_entry c i -> T <= i < T + PG) by (intros i Hi; unfold pc_entry, T_PC, PC_SZ, PG in *; clear -Hi Hc; lia).
    (* [comment removed for export] *)
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> ~ qhdr i -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn. apply AG; [| clear -Hi I1 I2; ulia]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|X]]]].
      - exact (Hn X).
      - pose proof (GQspace i X) as ZS. clear -ZS Hi I2 SBH. ulia.
      - pose proof (PCT i X) as ZT. clear -ZT Hi TPI. Zlia.
      - pose proof (RMspace i X) as ZS. clear -ZS Hi I2 SBH. ulia.
      - pose proof (RMSband i X) as ZS. clear -ZS Hi I2. ulia. }
    assert (TPR : forall i, T <= i < T + PG -> ~ pc_entry c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|X]]]].
      - unfold qhdr in X. clear -X Hi TPI INI. Zlia.
      - pose proof (GQspace i X) as ZS. clear -ZS Hi TPG. Zlia.
      - exact (Hn X).
      - pose proof (RMspace i X) as ZS. clear -ZS Hi TPG. Zlia.
      - pose proof (RMSband i X) as ZS. clear -ZS Hi TPB. Zlia. }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG ->
                   forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin Hlen Hpg i Hi Hr. apply AG; [| exact Hr].
      destruct (fixed_range bt st Lc FF W lo hi Hin) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen) as [SP|SP]; (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|X]]]].
      1,6: unfold qhdr in X; clear -X Hi D4 INI; ulia.
      1,5: pose proof (GQspace i X) as ZS; clear -ZS Hi SP; ulia.
      1,4: pose proof (PCT i X) as ZT; clear -ZT Hi D; ulia.
      1,3: pose proof (RMspace i X) as ZS; clear -ZS Hi SP; ulia.
      1,2: pose proof (RMSband i X) as ZS; clear -ZS Hi D5; ulia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi Hr. apply AG; [| exact Hr].
      destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hin) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hin) as [SP|SP]; (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|X]]]].
      1,6: unfold qhdr in X; clear -X Hi D4 INI; ulia.
      1,5: pose proof (GQspace i X) as ZS; clear -ZS Hi SP; ulia.
      1,4: pose proof (PCT i X) as ZT; clear -ZT Hi D; ulia.
      1,3: pose proof (RMspace i X) as ZS; clear -ZS Hi SP; ulia.
      1,2: pose proof (RMSband i X) as ZS; clear -ZS Hi D5; ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE + PG -> ~ gq_objs st i -> ~ (rm_lo rm <= i < rm_hi rm) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn1 Hn2 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|X]]]].
      - unfold qhdr in X. clear -X Hi SBH INI I2. ulia.
      - exact (Hn1 X).
      - pose proof (PCT i X) as ZT. clear -ZT Hi TPG. Zlia.
      - exact (Hn2 X).
      - pose proof (RMSband i X) as ZS. clear -ZS Hi SBH. ulia. }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> ~ (rms_lo rm <= i < rms_hi rm) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hn Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|X]]]].
      - unfold qhdr in X. clear -X Hi INI I2. ulia.
      - pose proof (GQspace i X) as ZS. clear -ZS Hi SBH. ulia.
      - pose proof (PCT i X) as ZT. clear -ZT Hi TPB. Zlia.
      - pose proof (RMspace i X) as ZS. clear -ZS Hi SBH. ulia.
      - exact (Hn X). }
    (* [comment removed for export] *)
    assert (CHKR : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' ->
               ~ (c' = BATCHCLASS /\ exists b, In b (a_gq st) /\ ba_addr b = a') ->
               ~ (exists m n, rm = Some (m, n) /\ c' = blk_class n /\ a' = prim_alloc_beg (m + 16) n) ->
               forall i, a' <= i < a' + csize c' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros c' a' Hc' CV' NB NR i Hi Hr. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      apply SPCR; [clear -Hi D3 D4; ulia | | | exact Hr].
      - intros Gi. destruct (GQfacts i Gi) as (b & _ & Hb & CVb & Bl1 & Bl2 & Hi2).
        destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS (ba_addr b) Hc' HC24 CV' CVb) as [[EC EA] | D].
        + apply NB. split; [exact EC|]. exists b. split; [exact Hb | symmetry; exact EA].
        + change (csize BATCHCLASS) with 8192 in D. unfold BATCHSZ in *. clear -D Hi Hi2. lia.
      - intros Ri. destruct (RMfacts i (or_introl Ri)) as (m & n & E & _ & _ & HCn & CVn & _ & _ & _ & _ & _ & _ & _). subst rm. unfold rm_lo, rm_hi in Ri.
        destruct (chunk_cases bt st Lc FF W c' a' (blk_class n) (prim_alloc_beg (m + 16) n) Hc' HCn CV' CVn) as [[EC EA] | D].
        + apply NR. exists m, n. repeat split; assumption.
        + clear -D Hi Ri. lia. }
    (* [comment removed for export] *)
    destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). pose proof PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
    (* [comment removed for export] *)
    assert (RMother : forall p' n', In (p', n') Lc \/ (In (p' - 16, n') (quar st) /\ Some (p' - 16, n') <> rm) -> is_primary n' = true -> 1 <= n' ->
               ~ (exists m n, rm = Some (m, n) /\ blk_class n' = blk_class n /\ prim_alloc_beg p' n' = prim_alloc_beg (m + 16) n)).
    { intros p' n' Hown HP' N1' (m & n & E & EC & EA).
      destruct (RMIN m n E) as [Hin HP]. assert (Hq : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact Hin).
      pose proof (quar_chunk bt st Lc FF W m n Hq HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _).
      destruct Hown as [HL | [HQ NE]].
      - pose proof (live_chunk bt st Lc FF W p' n' HL HP') as Gl. cbn zeta in Gl. destruct Gl as (_ & _ & L3 & _).
        destruct (WR1 _ G1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTn & _). destruct PARTn as (_ & LQ & _).
        apply (LQ (prim_alloc_beg (m + 16) n)). split; [rewrite <- EC, <- EA; exact L3 | exact G3].
      - pose proof (rz_unif n n' ltac:(lia) N1' HP HP' (eq_sym EC)) as ER. unfold prim_alloc_beg in EA.
        assert (p' - 16 = m) by (clear -EA ER; lia). apply NE. rewrite E. f_equal. f_equal; [exact H|].
        rewrite H in HQ. exact (NoDup_fst_inj (quar st) m n' n WQ6 HQ Hq). }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    (* [comment removed for export] *)
    assert (BAT : forall b0 i, In b0 (a_tq st) -> ba_addr b0 <= i < ba_addr b0 + BATCHSZ -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (CVb & _ & BL2 & BL3).
      apply (CHKR BATCHCLASS (ba_addr b0) HC24 CVb); [| | change (csize BATCHCLASS) with 8192; unfold BATCHSZ in Hi; exact Hi | exact Hr].
      - intros (_ & b & Hb & EA). destruct (in_split _ _ Hb0) as (t1 & t2 & ET). rewrite ET, !map_app in WQ5. cbn [map] in WQ5. rewrite <- app_assoc in WQ5. cbn [app] in WQ5.
        apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. apply in_app_iff. right. rewrite <- EA. apply in_map. exact Hb.
      - intros (m & n & E & EC & EA). destruct (RMIN m n E) as [Hin HP].
        assert (Hq : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact Hin).
        pose proof (quar_chunk bt st Lc FF W m n Hq HP) as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & QC & _).
        apply (NBL (ba_addr b0) ltac:(exists b0; split; [exact Hb2 | reflexivity]) eq_refl). right; left. rewrite EC, EA. exact QC. }
    (* [comment removed for export] *)
    assert (HDRR : forall p' n' i, In (p', n') Lc \/ (In (p' - 16, n') (quar st) /\ Some (p' - 16, n') <> rm) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
      assert (Hown0 : In (p', n') Lc \/ In (p' - 16, n') (quar st)) by (destruct Hown as [X | [X _]]; [left | right]; exact X).
      destruct (hdr_zone bt st Lc FF W p' n' i Hown0 Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply (CHKR (blk_class n') (prim_alloc_beg p' n') HC' CV'); [| | clear -W1 W2 W3 W4 N1' RZ'; unfold prim_alloc_beg in *; lia | exact Hr].
        + intros (EC & b & Hb & EA). apply (NBL (ba_addr b) ltac:(exists b; split; [apply in_app_iff; right; exact Hb | reflexivity]) eq_refl). rewrite EA, <- EC.
          destruct Hown0 as [Hown1|Hown1].
          * left. pose proof (live_chunk bt st Lc FF W p' n' Hown1 HP') as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & G3 & _). exact G3.
          * right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' Hown1 HP') as Gv. cbn zeta in Gv. replace (p' - 16 + 16) with p' in Gv by lia.
            destruct Gv as (_ & _ & G3 & _). exact G3.
        + exact (RMother p' n' Hown HP' N1').
      - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
    (* [comment removed for export] *)
    assert (CHvsFAd : forall c' a' c0, 1 <= c' <= 30 -> carved bt st c' a' -> 1 <= c0 <= 30 -> a' + csize c' <= fa_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= a').
    { intros c' a' c0 Hc' CVa Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      destruct (carved_range bt st Lc FF W c' a' Hc' CVa) as (D1 & D2 & _).
      pose proof (region_facts bt st Lc FF W c' Hc') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 c') as [LT|[->|GT]]; [| left; clear -D1 D2 F2 F3; lia |].
      * right. assert (c0 * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H D1 D2 F2 F3. lia.
      * left. assert (c' * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c' * 2 ^ 32 + 2 ^ 32) with ((c' + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        pose proof (W) as ((WRx & _) & _). destruct (WRx c' Hc') as (R1 & _ & R3 & _). unfold KREGION_EXHAUST, KUSERMAP in R3. clear -H D1 D2 F2 F3 R1 R3. lia. }
    assert (CHvsFA : forall c' a' c0 i, 1 <= c' <= 30 -> carved bt st c' a' -> 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> ~ (a' <= i < a' + csize c')).
    { intros c' a' c0 i Hc' CVa Hc0 Hi Hin2. destruct (CHvsFAd c' a' c0 Hc' CVa Hc0); lia. }
    clear WR2 WC WQ1 WQ2 WQ3 WQ4 S2 S4 S5 S6 S7 S8 LV1 LV3 WK WD WM' PW' R6a R6b IN6 G PARTB.
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in DC.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _].
             apply (IMGR i LT). intros X. apply (DC c0 Hc0 i Hi). (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). unfold qhdr, IB in X. right; right; left. lia. }
    (* [comment removed for export] *)
    split. { destruct P2 as (I1' & I2' & I3 & I4 & I5 & I6 & IL & IP & IW). (lazymatch goal with |- ?G => let G' := eval unfold rep_instance in G in change_no_check G' end).
             change (a_nres st') with (a_nres st). change (a_sec st') with (a_sec st). change (a_gq st') with gq'.
             assert (AGI : forall i, ((IB bt + 112 <= i < IB bt + 888) \/ (IB bt + 920 <= i < IB bt + 985)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply IMGR; [clear -Hi INI; lia | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -Hi; lia]. }
             split; [frZ AGI I1'|]. split; [frZ AGI I2'|]. split; [frB AGI I3|]. split; [frB AGI I4|]. split; [frB AGI I5|]. split; [frB AGI I6|].
             split; [exact NLIST|].
             split. { intros i s Hs. pose proof (nth_error_lt _ _ _ Hs) as Hl. pose proof (IP i s Hs) as C.
                      eapply (cellZ_frame _ _ _ _ _ _ C); [lia | lia |]. intros j Hj. apply (FIXR _ _ IN8); [ulia | ulia | clear -Hj Hl S1 S3; lia | lia]. }
             frW DEF IW. }
    (* [comment removed for export] *)
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with (a_cinit st).
             assert (AGT : forall i, (T <= i < T + T_PC + PC_SZ \/ T + T_PC + PC_SZ * 31 <= i < T + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply TPR; [clear -Hi; unfold T_PC, PC_SZ, PG in *; lia | (lazymatch goal with |- ?G => let G' := eval unfold pc_entry in G in change_no_check G' end); clear -Hi Hc; unfold T_PC, PC_SZ, PG in *; lia | exact Hr]. }
             assert (AGC : forall i, bt_tctx bt <= i < bt_tctx bt + 160 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply (FIXR _ _ INC); [ulia | ulia | clear -Hi; lia | exact Hr]. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros i Hi Hr. apply AGT; [clear -Hi; lia | exact Hr]. }
             split. { intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NEc]; [exact NPC|].
                      change (a_cache (set_gq st gq') c') with (a_cache st c'). pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                      eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                      unfold T_PC, PC_SZ in *. intros i Hi Hr. apply TPR; [clear -Hi Hc'; lia | (lazymatch goal with |- ?G => let G' := eval unfold pc_entry, T_PC, PC_SZ in G in change_no_check G' end); clear -Hi Hc' Hc NEc; lia | exact Hr]. }
             split; [frW DEF TW|]. split; [frZ AGC TC1|]. split; [frZ AGC TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi].
             - apply SPCR; [clear -Hi E9 E10; ulia | intros Zi; pose proof (GQspace i Zi) as ZS; clear -ZS Hi E9; ulia | intros Zi; pose proof (RMspace i Zi) as ZS; clear -ZS Hi E9; ulia | exact Hr].
             - apply SPCR; [clear -Hi E1 E2 E5 E6 E7 E8; ulia | | | exact Hr].
               + intros Zi. destruct (GQfacts i Zi) as (bl & _ & _ & CVl & Bl1 & Bl2 & Hi2).
                 exact (CHvsFA BATCHCLASS (ba_addr bl) c0 i HC24 CVl Hc0 ltac:(clear -Hi E6 E7; lia) ltac:(change (csize BATCHCLASS) with 8192; unfold BATCHSZ in Hi2; exact Hi2)).
               + intros Zi. destruct (RMfacts i (or_introl Zi)) as (m & n & E & _ & _ & HCn & CVn & _). subst rm. unfold rm_lo, rm_hi in Zi.
                 exact (CHvsFA (blk_class n) _ c0 i HCn CVn Hc0 ltac:(clear -Hi E6 E7; lia) Zi). }
    (* [comment removed for export] *)
    split. { change (a_tq st') with (a_tq st). eapply rep_batches_frame; [exact DEF | exact P5 | intros b0 Hb0; exact (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) |].
             intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. apply (BAT b0 i Hb0); [| exact Hr].
             destruct (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) as (_ & _ & Q3). clear -Hi Q3. ulia. }
    (* [comment removed for export] *)
    split; [exact NBAT|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRR p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq'. apply QSUB in Hq'. destruct Hq' as [Hq NErm]. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRR (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact (conj Hq NErm) | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. apply (IMGR i LT).
               unfold foot_depot_static in Hi. unfold DEPOT_NIDS, DEPOT_MAP1 in Hi. unfold qhdr, IB, DEPOT_TAB, SSOBJ in *. clear -Hi J1 J2. Zlia.
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | clear -Hi; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. apply (IMGR i LT). unfold qhdr, IB in *. clear -Hi J5. Zlia.
               + destruct (dtls_cell_facts bt st Lc FF W i Hi) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7).
                 pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6' & R6a' & R6b' & _) & _).
                 apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|X]]]].
                 * apply DF3. unfold qhdr in X. clear -X INI. lia.
                 * pose proof (GQspace i X) as ZS. apply (DF6 _ _ IN6'); [clear -R6a' R6b'; unfold KSPACE, PG in *; lia | clear -ZS R6a' R6b'; unfold KSPACE, PG in *; lia].
                 * apply DF5. exact (PCT i X).
                 * pose proof (RMspace i X) as ZS. apply (DF6 _ _ IN6'); [clear -R6a' R6b'; unfold KSPACE, PG in *; lia | clear -ZS R6a' R6b'; unfold KSPACE, PG in *; lia].
                 * pose proof (RMSband i X) as ZS. apply DF4. clear -ZS. ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. apply (IMGR i LT).
             unfold ialloc_cells in Hi. unfold qhdr, IB, IA_FLAG, IA_INST, IASZ in *. clear -Hi J3 J4. Zlia. }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st).
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             assert (RMSG : forall g, rms_lo rm <= SB + g < rms_hi rm -> exists m n, rm = Some (m, n) /\ (m + 16) / 8 <= g < (m + 16 + n + 7) / 8).
             { intros g Hg. destruct rm as [[m n]|]; [| unfold rms_lo, rms_hi in Hg; lia]. exists m, n. split; [reflexivity|]. unfold rms_lo, rms_hi, sh_lo, sh_hi in Hg. lia. }
             assert (NOTRMS : forall X Y g, X / 8 <= g < Y / 8 -> (forall m n, rm = Some (m, n) -> (m + 16 + n <= X /\ X mod 8 = 0) \/ Y <= m + 16) -> ~ (rms_lo rm <= SB + g < rms_hi rm)).
             { intros X Y g Hg SEP Hr. destruct (RMSG g Hr) as (m & n & E & Hu). exact (gran_sep X Y (m + 16) n g (SEP m n E) Hu Hg). }
             (* [comment removed for export] *)
             assert (RMvsDYN : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall m n, rm = Some (m, n) -> (m + 16 + n <= lo /\ lo mod 8 = 0) \/ hi <= m + 16).
             { intros lo hi Hin m n E. destruct (RMfacts (rm_lo rm) ltac:(left; rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold rm_lo, rm_hi in G in change_no_check G' end); destruct (RMIN m n E) as [_ HPx]; pose proof (csize_pos (blk_class n)) as CP;
                   assert (HqX : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact (proj1 (RMIN m n E)));
                   pose proof (quar_chunk bt st Lc FF W m n HqX HPx) as Gx; cbn zeta in Gx; destruct Gx as (Gx1 & _); specialize (CP Gx1); lia))
                 as (m2 & n2 & E2 & _ & _ & _ & _ & _ & G4 & G5 & C3 & C4 & _ & N1). rewrite E in E2. injection E2 as <- <-.
               destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as (_ & _ & PGlo & _). pose proof (rz_range n) as RZ.
               destruct (space_vs_dyn bt st Lc FF W lo hi Hin) as [SP|SP]; [right; clear -SP G4 C3 RZ; lia | left; split; [clear -SP G5 C4; unfold KSPACE, PG in *; lia | exact (pg8 lo PGlo)]]. }
             split. { intros c0 g Hc0 Hg NL'. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      destruct (Xdec_iv (rms_lo rm) (rms_hi rm) (SB + g)) as [INR | NOR].
                      - destruct (RMSG g INR) as (m & n & E & Hu).
                        assert (EXF : existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st') = false).
                        { destruct (existsb _ (quar st')) eqn:EX; [| reflexivity]. exfalso. apply existsb_exists in EX. destruct EX as ([m' n'] & Hx & Fx). cbn [fst snd] in Fx.
                          apply andb_prop in Fx. destruct Fx as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
                          apply QSUB in Hx. destruct Hx as [Hq' NErm].
                          destruct (RMfacts (SB + g) (or_intror INR)) as (m2 & n2 & E2 & Hq & HP & HCn & CVn & QCn & G4 & G5 & C3 & C4 & C5 & N1). rewrite E in E2. injection E2 as <- <-.
                          pose proof (csize_pos _ HCn) as (_ & CS16). pose proof (rz_range n) as RZ.
                          destruct (quar_item bt st Lc FF W m' n' Hq') as (N1' & [[HP' CV'] | [HP' RG']]).
                          - pose proof (quar_chunk bt st Lc FF W m' n' Hq' HP') as Gv. cbn zeta in Gv. destruct Gv as (HC' & _ & _ & G4' & G5' & _).
                            destruct (carved_range bt st Lc FF W _ _ HC' CV') as (_ & _ & _ & _ & C5'). pose proof (csize_pos _ HC') as (_ & CS16').
                            destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg (m' + 16) n') (blk_class n) (prim_alloc_beg (m + 16) n) HC' HCn CV' CVn) as [[EC EA] | D].
                            + apply (RMother (m' + 16) n' ltac:(right; replace (m' + 16 - 16) with m' by lia; exact (conj Hq' NErm)) HP' ltac:(lia)).
                              exists m, n. repeat split; assumption.
                            + set (a1 := prim_alloc_beg (m' + 16) n') in *. set (a2 := prim_alloc_beg (m + 16) n) in *. set (s1 := csize (blk_class n')) in *. set (s2 := csize (blk_class n)) in *.
                              pose proof (rz_range n') as RZ'. clear -D G4 G5 G4' G5' C5 C5' CS16 CS16' F1 F2 Hu N1 N1' RZ RZ'. Z.div_mod_to_equations. lia.
                          - destruct RG' as (sc & Hs & Eu & En). destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
                            destruct (RMvsDYN _ _ (sec_dyn st sc Hs) m n E) as [[SEP1 SEP2] | SEP]; rewrite Eu, En in *; unfold PG in *.
                            + clear -SEP1 SEP2 A5 F1 F2 Hu N1 N1'. Z.div_mod_to_equations. lia.
                            + clear -SEP A6 A3 A4 F1 F2 Hu N1 N1'. Z.div_mod_to_equations. lia. }
                        rewrite EXF. exact (SHFA m n E (SB + g) ltac:((lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end); lia)).
                      - rewrite (existsb_minus _ (quar st) (quar st') rm QSUB).
                        + pose proof (SH1 c0 g Hc0 Hg NL') as BY. eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | exact NOR | lia]].
                        + intros [m n] E. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). destruct (((m + 16) / 8 <=? g) && (g <? (m + 16 + n + 7) / 8)) eqn:EB; [| reflexivity]. exfalso. apply NOR.
                          apply andb_prop in EB. destruct EB as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. rewrite E. (lazymatch goal with |- ?G => let G' := eval unfold rms_lo, rms_hi, sh_lo, sh_hi in G in change_no_check G' end). lia. }
             split. { intros c0 g Hc0 Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (NOTRMS (fa_beg SBEG c0) (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) g Hg). intros m n E.
                      destruct (RMfacts (rm_lo rm) ltac:(left; rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold rm_lo, rm_hi in G in change_no_check G' end); destruct (RMIN m n E) as [_ HPx]; pose proof (csize_pos (blk_class n)) as CP;
                          assert (HqX : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact (proj1 (RMIN m n E)));
                          pose proof (quar_chunk bt st Lc FF W m n HqX HPx) as Gx; cbn zeta in Gx; destruct Gx as (Gx1 & _); specialize (CP Gx1); lia))
                        as (m2 & n2 & E2 & _ & _ & HCn & CVn & _ & G4 & G5 & _ & _ & _ & N1). rewrite E in E2. injection E2 as <- <-. pose proof (rz_range n) as RZ.
                      destruct (CHvsFAd _ _ c0 HCn CVn Hc0) as [SEP | SEP]; [left; split; [clear -SEP G5; lia | exact (pg8 _ D12)] | right; clear -SEP G4 RZ D6; lia]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (NOTRMS (sc_map sc) (sc_map sc + sc_mapsz sc) g Hg). exact (RMvsDYN _ _ (sec_dyn st sc Hs)). }
             split. { intros sc g Hs HQ' HU. pose proof (proj1 (proj1 (QSUB _) HQ')) as HQ.
                      pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      intros Hr. destruct (RMSG g Hr) as (m & n & E & Hu).
                      destruct (RMvsDYN _ _ (sec_dyn st sc Hs) m n E) as [[SEP1 SEP2] | SEP]; unfold PG in *.
                      - clear -SEP1 SEP2 A5 HU Hu. Z.div_mod_to_equations. lia.
                      - clear -SEP A6 A3 A4 HU Hu. Z.div_mod_to_equations. lia. }
             split. { intros c0 g Hc0 Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM P13). }
    (* [comment removed for export] *)
    split. { destruct P14 as (BU1 & BU2 & BU3 & BU4 & BU5 & BU6 & BU7 & BU8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st).
             change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact BU1|]. split; [exact MI|]. split; [exact BU3|]. split; [exact BU4|]. split; [exact BU5|]. split; [exact BU6|]. split; [exact BU7|].
             rewrite E3. change (prim_charge st') with (prim_charge st). change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st). exact BU8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    assert (RTC : forall i, ia_rtc_sb IA <= i < ia_rtc_sb IA + 8 \/ ia_rtc_uar IA <= i < ia_rtc_uar IA + 4 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. destruct (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); exact Hi)) as [LT _]. apply (IMGR i LT).
      unfold qhdr, IB in *. clear -Hi J6 J7. Zlia. }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; apply RTC; left; cbn in Hi; lia] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; apply RTC; right; cbn in Hi; lia] |].
    split; [intros z Hz; exact (def_keep Mmid M' _ DEF (proj1 P19 z Hz))|].
    intros NE' a Ha. destruct (GQD NE') as [NE0 | FD]; [apply (def_keep Mmid M' a DEF); exact (proj2 P19 NE0 a Ha) | exact (FD a Ha)].
  Qed.
End RC2.
End AsAinvOpsRc23.
Module AsAinvOpsRc33.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 AsAinvOpsRc23.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint putl (M : mem) (ws : list (Z * Z)) : mem :=
  match ws with [] => M | w :: t => put8 (putl M t) (fst w) (snd w) end.
Definition ws_ok (ws : list (Z * Z)) : Prop := forall a v, In (a, v) ws -> 0 <= a /\ a + 8 <= 2 ^ 64.

Section Putl.
  Variable SEGS : list Segment.
  Lemma putl_out : forall ws M (x : word), ws_ok ws -> (forall a v, In (a, v) ws -> u x < a \/ a + 8 <= u x) -> putl M ws x = M x.
  Proof.
    induction ws as [|[a v] t IH]; intros M x OK OUT; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [putl fst snd] in G in change_no_check G' end).
    destruct (OK a v (or_introl eq_refl)) as [R0 R1].
    rewrite (put8_out (putl M t) a v x R0 R1 (OUT a v (or_introl eq_refl))).
    apply IH; [intros a' v' H; exact (OK a' v' (or_intror H)) | intros a' v' H; exact (OUT a' v' (or_intror H))].
  Qed.
  Lemma putl_def : forall ws M (x : word), ws_ok ws -> (exists a v, In (a, v) ws /\ a <= u x < a + 8) -> putl M ws x <> None.
  Proof.
    induction ws as [|[a v] t IH]; intros M x OK (a0 & v0 & Hin & Hx); [destruct Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [putl fst snd] in G in change_no_check G' end).
    destruct (OK a v (or_introl eq_refl)) as [R0 R1].
    destruct (Z_le_dec a (u x)) as [L1|L1]; [destruct (Z_lt_dec (u x) (a + 8)) as [L2|L2]|].
    - apply (put8_def (putl M t) a v x R0 R1). lia.
    - rewrite (put8_out (putl M t) a v x R0 R1 ltac:(lia)). apply IH; [intros a' v' H; exact (OK a' v' (or_intror H))|].
      destruct Hin as [E | Hin]; [injection E as -> ->; lia | exists a0, v0; exact (conj Hin Hx)].
    - rewrite (put8_out (putl M t) a v x R0 R1 ltac:(lia)). apply IH; [intros a' v' H; exact (OK a' v' (or_intror H))|].
      destruct Hin as [E | Hin]; [injection E as -> ->; lia | exists a0, v0; exact (conj Hin Hx)].
  Qed.
  (* [comment removed for export] *)
  Lemma putl_changed : forall ws M (x : word), ws_ok ws -> putl M ws x <> M x -> (exists a v, In (a, v) ws /\ a <= u x < a + 8) /\ putl M ws x <> None.
  Proof.
    intros ws M x OK NE.
    assert (EX : exists a v, In (a, v) ws /\ a <= u x < a + 8).
    { clear -NE OK. induction ws as [|[a v] t IH]; [exfalso; exact (NE eq_refl)|]. cbn [putl fst snd] in NE.
      destruct (OK a v (or_introl eq_refl)) as [R0 R1].
      destruct (Z_le_dec a (u x)) as [L1|L1]; [destruct (Z_lt_dec (u x) (a + 8)) as [L2|L2]|].
      - exists a, v. split; [left; reflexivity | lia].
      - rewrite (put8_out (putl M t) a v x R0 R1 ltac:(lia)) in NE. destruct (IH ltac:(intros a' v' H; exact (OK a' v' (or_intror H))) NE) as (a' & v' & H & Hx). exists a', v'. split; [right; exact H | exact Hx].
      - rewrite (put8_out (putl M t) a v x R0 R1 ltac:(lia)) in NE. destruct (IH ltac:(intros a' v' H; exact (OK a' v' (or_intror H))) NE) as (a' & v' & H & Hx). exists a', v'. split; [right; exact H | exact Hx]. }
    split; [exact EX | exact (putl_def ws M x OK EX)].
  Qed.
  Lemma putl_hit : forall ws M a v, ws_ok ws -> In (a, v) ws ->
    (forall a' v', In (a', v') ws -> (a' = a /\ v' = v) \/ a' + 8 <= a \/ a + 8 <= a') -> a + 8 < 2 ^ 64 -> cellZ SEGS (putl M ws) a 8 v.
  Proof.
    induction ws as [|[a1 v1] t IH]; intros M a v OK Hin SEP HR; [destruct Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [putl fst snd] in G in change_no_check G' end).
    destruct (OK a1 v1 (or_introl eq_refl)) as [R0 R1].
    destruct (SEP a1 v1 (or_introl eq_refl)) as [[-> ->] | D].
    - apply put8_hit; assumption.
    - assert (Hin' : In (a, v) t) by (destruct Hin as [E | H]; [injection E as -> ->; lia | exact H]).
      destruct (OK a v (or_intror Hin')) as [A0 A1].
      eapply (cellZ_frame SEGS (putl M t)); [apply IH; [intros a' v' H; exact (OK a' v' (or_intror H)) | exact Hin' | intros a' v' H; exact (SEP a' v' (or_intror H)) | exact HR] | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros i Hi. cbn in Hi. apply put8_out; [exact R0 | exact R1 |]. rewrite u64_lit by lia. lia.
  Qed.
End Putl.

(* [comment removed for export] *)
Fixpoint itemw (a : Z) (its : list (Z * Z)) : list (Z * Z) :=
  match its with [] => [] | mn :: t => (a, fst mn) :: itemw (a + 8) t end.
Lemma itemw_nth : forall its a j mn, nth_error its j = Some mn -> In (a + 8 * Z.of_nat j, fst mn) (itemw a its).
Proof.
  induction its as [|x t IH]; intros a j mn H; [destruct j; discriminate H|].
  destruct j as [|j]; [cbn in H; injection H as ->; left; f_equal; lia|]. cbn in H. right.
  replace (a + 8 * Z.of_nat (S j)) with (a + 8 + 8 * Z.of_nat j) by lia. exact (IH (a + 8) j mn H).
Qed.
Lemma itemw_in : forall its a x v, In (x, v) (itemw a its) -> exists j mn, nth_error its j = Some mn /\ x = a + 8 * Z.of_nat j /\ v = fst mn.
Proof.
  induction its as [|y t IH]; intros a x v H; [destruct H|]. destruct H as [E | H].
  - injection E as <- <-. exists 0%nat, y. split; [reflexivity | split; [lia | reflexivity]].
  - destruct (IH (a + 8) x v H) as (j & mn & Hj & Ex & Ev). exists (S j), mn. split; [exact Hj | split; [lia | exact Ev]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XBound.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Definition xb_chunk (st : ast) (a : Z) : Prop :=
    carved bt st BATCHCLASS a /\ (in_batch st a \/ in_cache_c bt st BATCHCLASS a \/ in_fa_c bt st BATCHCLASS a).
  Definition XB (st : ast) (z : Z) : Prop := qhdr bt z \/ exists a, xb_chunk st a /\ a <= z < a + BATCHSZ.

  Lemma XB_mono : forall st st' z,
    (forall a, carved bt st BATCHCLASS a -> carved bt st' BATCHCLASS a) ->
    (forall a, in_batch st a -> in_batch st' a \/ in_cache_c bt st' BATCHCLASS a \/ in_fa_c bt st' BATCHCLASS a) ->
    (forall a, in_cache_c bt st BATCHCLASS a -> in_cache_c bt st' BATCHCLASS a \/ in_fa_c bt st' BATCHCLASS a) ->
    (forall a, in_fa_c bt st BATCHCLASS a -> in_fa_c bt st' BATCHCLASS a) ->
    XB st z -> XB st' z.
  Proof.
    intros st st' z CV HB HC HF [Q | (a & (CVa & OWN) & Hz)]; [left; exact Q|]. right. exists a. split; [| exact Hz]. split; [exact (CV a CVa)|].
    destruct OWN as [X | [X | X]]; [exact (HB a X) | right; exact (HC a X) | right; right; exact (HF a X)].
  Qed.

  Section Geo.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.

    Lemma XB_zone : forall z, XB st z -> (ia_img_lo IA <= z < ia_img_hi IA /\ qhdr bt z) \/ (SBEG <= z < SBEG + KSPACE /\ exists a, xb_chunk st a /\ a <= z < a + BATCHSZ).
    Proof.
      intros z [Q | (a & XC & Hz)].
      - left. split; [| exact Q]. pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
        destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4]. unfold qhdr, IB in *. lia.
      - right. split; [| exists a; exact (conj XC Hz)]. destruct XC as (CVa & _).
        destruct (carved_range bt st Lc FF W BATCHCLASS a ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVa) as (_ & _ & C3 & C4 & _). change (csize BATCHCLASS) with 8192 in C4. unfold BATCHSZ in *. lia.
    Qed.

    Lemma XB_not_T : forall z, XB st z -> ~ (T <= z < T + PG).
    Proof.
      intros z HX HT. pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & INT & _) & _).
      assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
      destruct (XB_zone z HX) as [[HI _] | [HS _]]; [clear -HI HT TPI; Zlia | clear -HS HT TPG; Zlia].
    Qed.
    Lemma XB_not_band : forall z, XB st z -> ~ (SB <= z < AS_HEAPLO).
    Proof.
      intros z HX HB. pose proof (img_lits bt st Lc FF W) as [I1 I2].
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH).
      destruct (XB_zone z HX) as [[HI _] | [HS _]]; [clear -HI HB I2; ulia | clear -HS HB SP7 SPH; ulia].
    Qed.
    Lemma XB_below_ceil : forall z, XB st z -> 0 <= z < CEIL.
    Proof.
      intros z HX. pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      destruct (XB_zone z HX) as [[HI _] | [HS _]]; [clear -HI I1 I2; ulia | clear -HS B3 B4 B5; ulia].
    Qed.
    (* [comment removed for export] *)
    Lemma XB_not_owned : forall z c ab, XB st z -> 1 <= c <= 30 -> carved bt st c ab -> (in_quar_c st c ab \/ in_live_c Lc c ab) -> ~ (ab <= z < ab + csize c).
    Proof.
      intros z c ab HX Hc CVab OWN Hz.
      destruct (XB_zone z HX) as [[HI _] | [HS (a & (CVa & XO) & Ha)]].
      - destruct (carved_range bt st Lc FF W c ab Hc CVab) as (_ & _ & C3 & C4 & _). pose proof (img_lits bt st Lc FF W) as [I1 I2].
        destruct (space_facts bt st Lc FF W) as (_ & SP6 & SP7 & SP8 & SPH). clear -HI Hz C3 C4 I2 SP7 SPH. ulia.
      - assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
        destruct (chunk_cases bt st Lc FF W c ab BATCHCLASS a Hc HC24 CVab CVa) as [[EC EA] | D].
        + subst c ab. pose proof W as ((WR1 & _) & _). destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & _).
          destruct PART as (_ & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
          destruct XO as [XO | [XO | XO]]; destruct OWN as [OW | OW].
          * apply (P8 a XO eq_refl). right; left. exact OW.
          * apply (P8 a XO eq_refl). left. exact OW.
          * exact (P5 a (conj OW XO)).
          * exact (P3 a (conj OW XO)).
          * exact (P6 a (conj OW XO)).
          * exact (P4 a (conj OW XO)).
        + change (csize BATCHCLASS) with 8192 in D. unfold BATCHSZ in *. clear -D Hz Ha. lia.
    Qed.
  End Geo.
End XBound.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma last_addr_map : forall q q', map ba_addr q = map ba_addr q' ->
  (match rev q with [] => 0 | b :: _ => ba_addr b end) = (match rev q' with [] => 0 | b :: _ => ba_addr b end).
Proof.
  intros q q' E. assert (H : forall q0, (match rev q0 with [] => 0 | b :: _ => ba_addr b end) = hd 0 (rev (map ba_addr q0))).
  { intros q0. rewrite <- map_rev. destruct (rev q0); reflexivity. }
  rewrite !H, E. reflexivity.
Qed.

Section RcX.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition foot_recycle_prim (st : ast) (m n c : Z) (z : Z) : Prop :=
    (prim_alloc_beg (m + 16) n <= z < prim_alloc_beg (m + 16) n + csize c) \/ (sh_lo (m + 16) <= z < sh_hi (m + 16) n)
    \/ (T + T_PC + PC_SZ * c <= z < T + T_PC + PC_SZ * c + 4)
    \/ (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length (a_cache st c)) <= z < T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length (a_cache st c)) + 4)
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REPX_recycle_prim : Prop := forall (X : Z -> Prop) (Xd : Xdec X) st Lc FF (M M' : mem) mdl mdl' ba m n its rest c k (qt qg : Z),
    WFq bt st Lc FF qt qg -> RepX bt X st Lc FF M mdl ->
    a_gq st = BATCH ba ((m, n) :: its) :: rest -> is_primary n = true -> c = blk_class n -> k = compact_of SBEG c (prim_alloc_beg (m + 16) n) ->
    Z.of_nat (length (a_cache st c)) < cache_max c ->
    (forall z, X z -> XB bt st z) -> (forall z, qhdr bt z -> X z) -> (forall z, ba <= z < ba + BATCHSZ -> X z) ->
    (forall a : word, qhdr bt (u a) -> M' a <> None) ->
    (forall a : word, M' a <> M a -> (foot_recycle_prim st m n c (u a) \/ X (u a)) /\ M' a <> None) ->
    cellZ SG M' (T + T_PC + PC_SZ * c) 4 (Z.of_nat (length (a_cache st c)) + 1) ->
    cellZ SG M' (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length (a_cache st c))) 4 k ->
    fillZ SG M' (sh_lo (m + 16)) (sh_hi (m + 16) n) FA ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    RepX bt X (op_recycle_prim st c k) Lc FF M' mdl'.

  Theorem OPS_REPX_recycle_prim_pf : OPS_REPX_recycle_prim.
  Proof.
    intros X Xd st Lc FF M M' mdl mdl' ba m n its rest c k qt qg W (M0 & R & D) Hgq HP Hc Hk HLEN XBD XQ XO HDEF STEP CCNT CCH SHFA SBM MI.
    set (b := BATCH ba ((m, n) :: its)) in *. set (b' := BATCH ba its). set (gq' := b' :: rest).
    set (len := Z.of_nat (length (a_cache st c))) in *.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & _).
    assert (Hb : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; left; reflexivity).
    destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & BB1 & BB2). unfold b in CVB, BL, BB1, BB2. cbn [ba_addr ba_items length] in CVB, BL, BB1, BB2.
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    destruct (quar_gq_head st ba (m, n) its rest Hgq) as [EQ0 _].
    assert (Hq : In (m, n) (quar st)) by (rewrite EQ0; apply in_app_iff; right; left; reflexivity).
    pose proof (quar_chunk bt st Lc FF W m n Hq HP) as Gv. cbn zeta in Gv. rewrite <- Hc in Gv. set (ab := prim_alloc_beg (m + 16) n) in *.
    destruct Gv as (Hc30 & CVab & QCab & G4 & G5 & G6).
    pose proof (cache_len bt st Lc FF W c Hc30) as CL. fold len in CL.
    assert (LEN15 : 0 <= len <= 15) by (unfold len, cache_max, cache_hint in *; lia).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    destruct (space_facts bt st Lc FF W) as (_ & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & _).
    destruct R2 as (_ & _ & _ & _ & _ & _ & IL & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TP & _).
    (* [comment removed for export] *)
    set (ws := (IB bt + 912, q_bytes gq') :: (ba + 8, ba_bytes b') :: (ba + 16, Z.of_nat (length its)) :: itemw (ba + 24) its).
    assert (WSZ : forall a v, In (a, v) ws -> (a = IB bt + 912) \/ (ba + 8 <= a /\ a + 8 <= ba + BATCHSZ)).
    { intros a v [E | [E | [E | Hi]]]; [left; congruence | right; injection E as <- _; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia | right; injection E as <- _; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia|].
      right. destruct (itemw_in its (ba + 24) a v Hi) as (j & mn & Hj & -> & _). pose proof (nth_error_lt _ _ _ Hj) as Hl. unfold BATCHSZ, BATCHCAP in *. lia. }
    assert (WSOK : ws_ok ws).
    { intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [clear -INI I1 I2; ulia | clear -A1 A2 BB1 BB2 SBH B3 B4 B5; ulia]. }
    set (IDEAL := putl M0 ws).
    set (M0' := fun a : word => if Xd (u a) then IDEAL a else M' a).
    assert (WSX : forall a v z, In (a, v) ws -> a <= z < a + 8 -> X z /\ (qhdr bt z \/ ba <= z < ba + BATCHSZ)).
    { intros a v z Hin Hz. destruct (WSZ a v Hin) as [-> | [A1 A2]].
      - assert (Q : qhdr bt z) by ((lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); lia). split; [exact (XQ z Q) | left; exact Q].
      - assert (Q : ba <= z < ba + BATCHSZ) by lia. split; [exact (XO z Q) | right; exact Q]. }
    assert (OFFX : forall i, ~ X i -> 0 <= i < 2 ^ 64 -> M0' (Z_to_bv 64 i) = M' (Z_to_bv 64 i)).
    { intros i NX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (Xd i); [contradiction | reflexivity]. }
    assert (INX : forall i, X i -> 0 <= i < 2 ^ 64 -> M0' (Z_to_bv 64 i) = IDEAL (Z_to_bv 64 i)).
    { intros i HX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (Xd i); [reflexivity | contradiction]. }
    assert (MM0 : forall a : word, ~ X (u a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E | NE]; [exact E | exfalso; exact (NX (proj1 (D a NE)))]. }
    assert (KEEP : forall i, ~ X i -> ~ foot_recycle_prim st m n c i -> 0 <= i < 2 ^ 64 -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros i NX NF Hr. rewrite (OFFX i NX Hr). rewrite <- (MM0 (Z_to_bv 64 i)) by (rewrite u64_lit by lia; exact NX).
      destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E | NE]; [exact E | exfalso].
      destruct (STEP _ NE) as [[F | F] _]; rewrite u64_lit in F by lia; [exact (NF F) | exact (NX F)]. }
    assert (IDOUT : forall i, (forall a v, In (a, v) ws -> i < a \/ a + 8 <= i) -> 0 <= i < 2 ^ 64 -> IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros i OUT Hr. (lazymatch goal with |- ?G => let G' := eval unfold IDEAL in G in change_no_check G' end). apply putl_out; [exact WSOK|]. intros a v Hin. rewrite u64_lit by lia. exact (OUT a v Hin). }
    (* [comment removed for export] *)
    assert (FNX : forall z, foot_recycle_prim st m n c z -> ~ X z).
    { intros z Hf HX. pose proof (XBD z HX) as HXB. unfold foot_recycle_prim in Hf. fold ab len in Hf.
      destruct Hf as [F|[F|[F|[F|[F|F]]]]].
      - exact (XB_not_owned bt st Lc FF W z c ab HXB Hc30 CVab (or_introl QCab) F).
      - apply (XB_not_band bt st Lc FF W z HXB). unfold sh_lo, sh_hi in F.
        destruct (carved_range bt st Lc FF W c ab Hc30 CVab) as (_ & _ & C3 & C4 & _). pose proof (rz_range n) as RZ.
        destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _). clear -F G4 G5 C3 C4 RZ N1 B3 B4 B5 B6 B7. Zlia.
      - apply (XB_not_T bt st Lc FF W z HXB). clear -F Hc30. unfold T_PC, PC_SZ, PG in *. lia.
      - apply (XB_not_T bt st Lc FF W z HXB). clear -F Hc30 LEN15. unfold T_PC, PC_SZ, PG in *. lia.
      - apply (XB_not_T bt st Lc FF W z HXB). clear -F. unfold PG in *. lia.
      - pose proof (XB_below_ceil bt st Lc FF W z HXB). lia. }
    (* [comment removed for export] *)
    assert (AGR : agrees_off (foot_gqpush bt st c (Some (m, n))) M0 M0').
    { intros a NE. unfold M0' in NE |- *. destruct (Xd (u a)) as [HX | NX].
      - destruct (putl_changed ws M0 a WSOK NE) as ((a0 & v0 & Hin & Hz) & Dd). split; [| exact Dd].
        destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | Q]); [left; exact Q | right; left; exists b; split; [rewrite Hgq; left; reflexivity | exact Q]].
      - rewrite <- (MM0 a NX) in NE. destruct (STEP a NE) as [[F | F] Dd]; [| contradiction]. split; [| exact Dd].
        unfold foot_recycle_prim in F. fold ab len in F. (lazymatch goal with |- ?G => let G' := eval unfold foot_gqpush, rm_lo, rm_hi, rms_lo, rms_hi, pc_entry in G in change_no_check G' end). fold ab. rewrite <- Hc.
        destruct F as [F|[F|[F|[F|[F|F]]]]]; [do 3 right; left; exact F | do 4 right; left; exact F | right; right; left | right; right; left | do 5 right; left; exact F | do 6 right; exact F].
        + clear -F. unfold PC_SZ in *. lia.
        + clear -F LEN15. unfold PC_SZ in *. lia. }
    assert (WSI : forall a v, In (a, v) ws -> (a = IB bt + 912 /\ v = q_bytes gq') \/ (a = ba + 8 /\ v = ba_bytes b') \/ (a = ba + 16 /\ v = Z.of_nat (length its))
                    \/ (exists j mn, nth_error its j = Some mn /\ a = ba + 24 + 8 * Z.of_nat j /\ v = fst mn)).
    { intros a v [E | [E | [E | Hi]]]; [left | right; left | right; right; left | right; right; right]; try (injection E as <- <-; split; reflexivity).
      exact (itemw_in its (ba + 24) a v Hi). }
    assert (FARI : IB bt + 920 <= ba) by (clear -BB1 INI I2 SBH; ulia).
    assert (SEPH : forall a' v', In (a', v') ws -> (a' = IB bt + 912 /\ v' = q_bytes gq') \/ a' + 8 <= IB bt + 912 \/ IB bt + 912 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [X0 | [[-> _] | [[-> _] | (j & mn & _ & -> & _)]]]; [left; exact X0 | right; right; lia | right; right; lia | right; right; lia]. }
    assert (SEP8 : forall a' v', In (a', v') ws -> (a' = ba + 8 /\ v' = ba_bytes b') \/ a' + 8 <= ba + 8 \/ ba + 8 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [X0 | [[-> _] | (j & mn & _ & -> & _)]]]; [right; left; lia | left; exact X0 | right; right; lia | right; right; lia]. }
    assert (SEP16 : forall a' v', In (a', v') ws -> (a' = ba + 16 /\ v' = Z.of_nat (length its)) \/ a' + 8 <= ba + 16 \/ ba + 16 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [[-> _] | [X0 | (j & mn & _ & -> & _)]]]; [right; left; lia | right; left; lia | left; exact X0 | right; right; lia]. }
    assert (SEPI : forall j mn, nth_error its j = Some mn -> forall a' v', In (a', v') ws ->
                     (a' = ba + 24 + 8 * Z.of_nat j /\ v' = fst mn) \/ a' + 8 <= ba + 24 + 8 * Z.of_nat j \/ ba + 24 + 8 * Z.of_nat j + 8 <= a').
    { intros j mn Hj a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [[-> _] | [[-> _] | (j' & mn' & Hj' & -> & ->)]]]; [right; left; lia | right; left; lia | right; left; lia |].
      destruct (Nat.eq_dec j' j) as [-> | NEj]; [left; split; [reflexivity | congruence] | right; lia]. }
    (* [comment removed for export] *)
    assert (HDRX : forall i, IB bt + 888 <= i < IB bt + 920 -> 0 <= i < 2 ^ 64 /\ X i) by (intros i Hi; split; [clear -Hi INI I1 I2; ulia | apply XQ; exact Hi]).
    assert (OBJX : forall i, ba <= i < ba + BATCHSZ -> 0 <= i < 2 ^ 64 /\ X i) by (intros i Hi; split; [clear -Hi BB1 BB2 SBH B3 B4 B5; ulia | apply XO; exact Hi]).
    assert (HDRSAME : forall i, IB bt + 888 <= i < IB bt + 912 -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros i Hi. destruct (HDRX i ltac:(lia)) as [Hr HX]. rewrite (INX i HX Hr). apply IDOUT; [| exact Hr].
      intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [lia | clear -Hi A1 BB1 INI I2 SBH; ulia]. }
    assert (NL : rep_list bt M0' (IB bt + 888) gq').
    { destruct IL as (L1 & L2 & L3 & L4). rewrite Hgq in L1, L2, L3. (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end).
      assert (RI : 0 <= IB bt + 888 /\ IB bt + 920 < 2 ^ 64) by (clear -INI I1 I2; ulia).
      split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [length] in L1 |- *. eapply (cellZ_frame _ _ _ _ _ _ L1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [ba_addr] in L2 |- *. eapply (cellZ_frame _ _ _ _ _ _ L2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      split. { rewrite (last_addr_map gq' (b :: rest) eq_refl). eapply (cellZ_frame _ _ _ _ _ _ L3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      replace (IB bt + 888 + 24) with (IB bt + 912) by lia.
      eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (IB bt + 912) (q_bytes gq') WSOK ltac:(left; reflexivity) SEPH ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros i Hi. cbn in Hi. destruct (HDRX i ltac:(lia)) as [Hr HX]. exact (INX i HX Hr). }
    (* [comment removed for export] *)
    assert (OBJI : forall i, ba <= i < ba + BATCHSZ -> M0' (Z_to_bv 64 i) = IDEAL (Z_to_bv 64 i)) by (intros i Hi; destruct (OBJX i Hi) as [Hr HX]; exact (INX i HX Hr)).
    (* [comment removed for export] *)
    assert (RESTSAME : forall b0, In b0 rest -> forall i, ba_addr b0 <= i < ba_addr b0 + BATCHSZ -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros b0 Hb0 i Hi. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; right; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (CV0 & _ & C1 & C2).
      assert (Hr : 0 <= i < 2 ^ 64) by (clear -Hi C1 C2 SBH B3 B4 B5; ulia).
      assert (DIS : ba + BATCHSZ <= ba_addr b0 \/ ba_addr b0 + BATCHSZ <= ba).
      { destruct (chunk_cases bt st Lc FF W BATCHCLASS ba BATCHCLASS (ba_addr b0) HC24 HC24 CVB CV0) as [[_ EA] | Dj]; [| change (csize BATCHCLASS) with 8192 in Dj; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia].
        exfalso. rewrite Hgq, map_app in WQ5. cbn [map ba_addr] in WQ5. apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. change (ba_addr b) with ba. rewrite EA. apply in_map. exact Hb0. }
      assert (IDS : IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
      { apply IDOUT; [| exact Hr]. intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [clear -Hi C1 INI I2 SBH; ulia | clear -Hi A1 A2 DIS; lia]. }
      destruct (Xd i) as [HX | NX]; [rewrite (INX i HX Hr); exact IDS|].
      apply (KEEP i NX); [| exact Hr]. intros Hf.
      assert (HXB : XB bt st i). { right. exists (ba_addr b0). split; [split; [exact CV0 | left; exists b0; split; [exact Hb2 | reflexivity]] | exact Hi]. }
      unfold foot_recycle_prim in Hf. fold ab len in Hf. destruct Hf as [F|[F|[F|[F|[F|F]]]]].
      - exact (XB_not_owned bt st Lc FF W i c ab HXB Hc30 CVab (or_introl QCab) F).
      - apply (XB_not_band bt st Lc FF W i HXB). unfold sh_lo, sh_hi in F.
        destruct (carved_range bt st Lc FF W c ab Hc30 CVab) as (_ & _ & C3 & C4 & _). pose proof (rz_range n) as RZ.
        destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _). clear -F G4 G5 C3 C4 RZ N1 B3 B4 B5 B6 B7. Zlia.
      - apply (XB_not_T bt st Lc FF W i HXB). clear -F Hc30. unfold T_PC, PC_SZ, PG in *. lia.
      - apply (XB_not_T bt st Lc FF W i HXB). clear -F Hc30 LEN15. unfold T_PC, PC_SZ, PG in *. lia.
      - apply (XB_not_T bt st Lc FF W i HXB). clear -F. unfold PG in *. lia.
      - pose proof (XB_below_ceil bt st Lc FF W i HXB). lia. }
    assert (NB : rep_batches bt M0' gq').
    { intros i b0 Hb0. destruct i as [|i].
      - cbn in Hb0. injection Hb0 as <-. destruct (R6 0%nat b ltac:(rewrite Hgq; reflexivity)) as (C1 & C2 & C3 & C4 & CW). unfold b in C1, CW. cbn [ba_addr] in C1, CW |- *.
        assert (RB : 0 <= ba /\ ba + BATCHSZ < 2 ^ 64) by (clear -BB1 BB2 SBH B3 B4 B5; ulia). unfold BATCHSZ, BATCHCAP in *.
        split. { rewrite Hgq in C1. (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [nth_error] in C1 |- *. eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. intros i Hi. cbn in Hi.
                 rewrite (OBJI i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia)). apply IDOUT; [| lia]. intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; lia. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 8) (ba_bytes b') WSOK ltac:(right; left; reflexivity) SEP8 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 16) (Z.of_nat (length its)) WSOK ltac:(right; right; left; reflexivity) SEP16 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl.
                 eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 24 + 8 * Z.of_nat j) (fst mn) WSOK ltac:(do 3 right; exact (itemw_nth its (ba + 24) j mn Hj)) (SEPI j mn Hj) ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        eapply (writableZ_frame _ _ _ _ _ CW). intros i Hi. rewrite (OBJI i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hi)).
        destruct (decide (IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i))) as [E | NE]; [left; exact E | right; exact (proj2 (putl_changed ws M0 _ WSOK NE))].
      - unfold gq' in Hb0. cbn [nth_error] in Hb0. pose proof (nth_error_In _ _ Hb0) as Hin0.
        destruct (R6 (S i) b0 ltac:(rewrite Hgq; exact Hb0)) as (C1 & C2 & C3 & C4 & CW). rewrite Hgq in C1.
        assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; right; exact Hin0).
        destruct (batch_facts bt st Lc FF W b0 Hb2) as (_ & BL0 & D1 & D2).
        assert (RB : 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64) by (clear -D1 D2 SBH B3 B4 B5; ulia). unfold BATCHSZ, BATCHCAP in *.
        assert (SM : forall i0, ba_addr b0 <= i0 < ba_addr b0 + 8192 -> M0' (Z_to_bv 64 i0) = M0 (Z_to_bv 64 i0)) by (intros i0 Hi0; apply (RESTSAME b0 Hin0); (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hi0).
        split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [nth_error] in C1 |- *. eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ C2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ C3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. eapply (cellZ_frame _ _ _ _ _ _ (C4 j mn Hj)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        eapply (writableZ_frame _ _ _ _ _ CW). intros i0 Hi0. left. apply SM. exact Hi0. }
    (* [comment removed for export] *)
    assert (TNX : forall i, T <= i < T + PG -> ~ X i) by (intros i Hi HX; exact (XB_not_T bt st Lc FF W i (XBD i HX) Hi)).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & TP0 & TP1 & _).
    assert (NPC : rep_pclass bt M0' T (a_cinit st) c (a_cache st c ++ [k])).
    { destruct (TP c Hc30) as (Q1 & Q2 & Q3 & Q4). unfold rep_pclass in *. cbn zeta in *. unfold T_PC, PC_SZ, PG in *.
      assert (RT0 : 0 <= T /\ T + 4096 < 2 ^ 64) by (clear -TP0 TP1; ulia).
      assert (PCK : forall i, T + 208 + 80 * c + 4 <= i < T + 208 + 80 * c + 16 + 4 * len -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
      { intros i Hi. apply KEEP; [apply TNX; clear -Hi Hc30 LEN15; lia | | clear -Hi RT0 Hc30 LEN15; lia].
        (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_prim in G in change_no_check G' end). fold ab len. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros [F|[F|[F|[F|[F|F]]]]]; try (clear -F Hi Hc30 LEN15; lia).
        - apply (XB_not_T bt st Lc FF W i); [| clear -Hi Hc30 LEN15; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia]. exfalso.
          destruct (carved_range bt st Lc FF W c ab Hc30 CVab) as (_ & _ & C3 & C4 & _).
          pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & INT & _) & _).
          assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
          clear -F Hi C3 C4 TPG Hc30 LEN15. ulia.
        - exfalso. unfold sh_lo, sh_hi in F. pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & TPB).
          destruct (carved_range bt st Lc FF W c ab Hc30 CVab) as (_ & _ & C3 & C4 & _). pose proof (rz_range n) as RZ.
          destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _). clear -F Hi G4 G5 C3 C4 RZ N1 B3 B4 B5 B6 B7 TPB Hc30 LEN15. Zlia.
        - exfalso. clear -F Hi RT0 TP1 Hc30 LEN15. ulia. }
      assert (OFFT : forall i, T <= i < T + 4096 -> M0' (Z_to_bv 64 i) = M' (Z_to_bv 64 i)) by (intros i Hi; apply OFFX; [apply TNX; exact Hi | lia]).
      rewrite length_app, Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). fold len. change (Z.of_nat 1) with 1.
      split. { eapply (cellZ_frame _ _ _ _ _ _ CCNT); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply OFFT; clear -Hi Hc30; lia]. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply PCK; clear -Hi LEN15; lia]. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply PCK; clear -Hi LEN15; lia]. }
      intros i k0 Hk0. destruct (Nat.lt_ge_cases i (length (a_cache st c))) as [LT | GE].
      - rewrite nth_error_app1 in Hk0 by exact LT. eapply (cellZ_frame _ _ _ _ _ _ (Q4 i k0 Hk0)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply PCK; (lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hi0 LT; lia].
      - rewrite nth_error_app2 in Hk0 by exact GE. destruct (i - length (a_cache st c))%nat as [|d] eqn:ED; [| destruct d; discriminate Hk0]. cbn in Hk0. injection Hk0 as <-.
        assert (Ei : Z.of_nat i = len) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia). rewrite Ei.
        eapply (cellZ_frame _ _ _ _ _ _ CCH); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply OFFT; clear -Hi0 Hc30 LEN15; lia]. }
    (* [comment removed for export] *)
    assert (NSH : forall m0 n0, Some (m, n) = Some (m0, n0) -> fillZ SG M0' (sh_lo (m0 + 16)) (sh_hi (m0 + 16) n0) FA).
    { intros m0 n0 E. injection E as <- <-.
      destruct (carved_range bt st Lc FF W c ab Hc30 CVab) as (_ & _ & C3 & C4 & _). pose proof (rz_range n) as RZ. destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _).
      assert (SHB : forall i, sh_lo (m + 16) <= i < sh_hi (m + 16) n -> SB <= i < AS_HEAPLO) by (intros i Hi; unfold sh_lo, sh_hi in Hi; clear -Hi G4 G5 C3 C4 RZ N1 B3 B4 B5 B6 B7; Zlia).
      eapply (fillZ_frame _ _ _ _ _ _ SHFA).
      - (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). clear -G4 C3 RZ B3. Zlia.
      - pose proof (SHB (sh_hi (m + 16) n - 1)) as Q. unfold sh_lo, sh_hi in *. clear -Q N1. Zlia.
      - intros i Hi. apply OFFX; [intros HX; exact (XB_not_band bt st Lc FF W i (XBD i HX) (SHB i Hi)) | pose proof (SHB i Hi) as Q; clear -Q; ulia]. }
    (* [comment removed for export] *)
    assert (NDQ : List.NoDup (flat_map ba_items (a_tq st) ++ (m, n) :: (its ++ flat_map ba_items rest))) by (rewrite <- EQ0; exact (NoDup_map_inv _ _ WQ6)).
    assert (QREL : forall x, In x (flat_map ba_items gq') <-> In x (flat_map ba_items (a_gq st)) /\ Some x <> Some (m, n)).
    { intros x. rewrite Hgq. (lazymatch goal with |- ?G => let G' := eval unfold gq', b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items] in G in change_no_check G' end). pose proof (NoDup_app_remove_l _ _ NDQ) as ND2. inversion ND2 as [| ? ? NI _]; subst. split.
      - intros Hx. split; [right; exact Hx | intros E; injection E as ->; exact (NI Hx)].
      - intros [[E | Hx] NE]; [exfalso; apply NE; rewrite E; reflexivity | exact Hx]. }
    (* [comment removed for export] *)
    assert (RC : Rep bt (set_cache (set_gq st gq') c (a_cache st c ++ [k])) Lc FF M0' mdl').
    { apply (OPS_REP_gqpush_pf bt st Lc FF M0 M0' mdl mdl' gq' c (a_cache st c ++ [k]) (Some (m, n)) qt qg W R Hc30 QREL); [| exact AGR | exact NL | exact NB | exact NPC | exact NSH | exact SBM | exact MI | intros _; left; rewrite Hgq; discriminate].
      intros m0 n0 E. injection E as <- <-. split; [rewrite Hgq; (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items] in G in change_no_check G' end); left; reflexivity | exact HP]. }
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim in G in change_no_check G' end). rewrite (op_qitem_eq st ba (m, n) its rest Hgq). (lazymatch goal with |- ?G => let G' := eval unfold op_cache_push in G in change_no_check G' end). change (a_cache (set_gq st (BATCH ba its :: rest)) c) with (a_cache st c).
    exists M0'. split; [exact RC|].
    intros a NE. unfold M0' in NE. destruct (Xd (u a)) as [HX | NX]; [| exfalso; exact (NE eq_refl)]. split; [exact HX|].
    destruct (decide (M' a = M a)) as [E1 | NE1]; [| exact (proj2 (STEP a NE1))].
    destruct (decide (M a = M0 a)) as [E2 | NE2]; [| rewrite E1; exact (proj2 (D a NE2))].
    rewrite E1, E2 in NE. assert (NE3 : IDEAL a <> M0 a) by (intros E3; apply NE; symmetry; exact E3).
    destruct (putl_changed ws M0 a WSOK NE3) as ((a0 & v0 & Hin & Hz) & _).
    destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | Q]); [exact (HDEF a Q)|].
    rewrite E1, E2. destruct (R6 0%nat b ltac:(rewrite Hgq; reflexivity)) as (_ & _ & _ & _ & CW). unfold b in CW. cbn [ba_addr] in CW.
    pose proof (proj1 (CW (u a) Q)) as DF. assert (EA : Z_to_bv 64 (u a) = a) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range a); lia); reflexivity). rewrite EA in DF. exact DF.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma nth_error_remove : forall {A} (l : list A) i j, (i < length l)%nat ->
    nth_error (firstn i l ++ skipn (S i) l) j = if (j <? i)%nat then nth_error l j else nth_error l (S j).
  Proof.
    intros A l i j Hi. assert (LF : length (firstn i l) = i) by (rewrite length_firstn; lia).
    destruct (Nat.ltb_spec j i) as [LT | GE].
    - rewrite nth_error_app1 by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec j i); [reflexivity | lia].
    - rewrite nth_error_app2 by lia. rewrite LF, nth_error_skipn. f_equal. lia.
  Qed.

  Definition foot_qbatch_free (st : ast) (z : Z) : Prop :=
    (T + T_PC + PC_SZ * BATCHCLASS <= z < T + T_PC + PC_SZ * BATCHCLASS + 4)
    \/ (T + T_PC + PC_SZ * BATCHCLASS + 16 + 4 * Z.of_nat (length (a_cache st BATCHCLASS)) <= z < T + T_PC + PC_SZ * BATCHCLASS + 16 + 4 * Z.of_nat (length (a_cache st BATCHCLASS)) + 4)
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REPX_qbatch_free : Prop := forall (X : Z -> Prop) (Xd : Xdec X) st Lc FF (M M' : mem) mdl mdl' i ba (qt qg : Z),
    WFq bt st Lc FF qt qg -> RepX bt X st Lc FF M mdl ->
    nth_error (a_gq st) i = Some (BATCH ba []) ->
    Z.of_nat (length (a_cache st BATCHCLASS)) < cache_max BATCHCLASS ->
    (forall z, X z -> XB bt st z) -> (forall z, qhdr bt z -> X z) ->
    (forall i' bp, i = S i' -> nth_error (a_gq st) i' = Some bp -> forall z, ba_addr bp <= z < ba_addr bp + 8 -> X z) ->
    (forall a : word, qhdr bt (u a) -> M' a <> None) ->
    (forall a : word, M' a <> M a -> (foot_qbatch_free st (u a) \/ X (u a)) /\ M' a <> None) ->
    cellZ SG M' (T + T_PC + PC_SZ * BATCHCLASS) 4 (Z.of_nat (length (a_cache st BATCHCLASS)) + 1) ->
    cellZ SG M' (T + T_PC + PC_SZ * BATCHCLASS + 16 + 4 * Z.of_nat (length (a_cache st BATCHCLASS))) 4 (compact_of SBEG BATCHCLASS ba) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    RepX bt X (op_qbatch_free SBEG st i) Lc FF M' mdl'.

  Theorem OPS_REPX_qbatch_free_pf : OPS_REPX_qbatch_free.
  Proof.
    intros X Xd st Lc FF M M' mdl mdl' i ba qt qg W (M0 & R & D) Hnth HLEN XBD XQ XP HDEF STEP CCNT CCH SBM MI.
    set (c := BATCHCLASS) in *. set (k := compact_of SBEG c ba) in *. set (len := Z.of_nat (length (a_cache st c))) in *.
    pose proof (nth_error_split_fs (a_gq st) i _ Hnth) as Hgq. pose proof (nth_error_lt _ _ _ Hnth) as Hil.
    set (G1 := firstn i (a_gq st)) in *. set (G2 := skipn (S i) (a_gq st)) in *. set (gq' := G1 ++ G2).
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & _).
    assert (Hc30 : 1 <= c <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold c, BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (cache_len bt st Lc FF W c Hc30) as CL. fold len in CL.
    assert (LEN15 : 0 <= len <= 15) by (unfold len, c, cache_max, cache_hint, BATCHCLASS in *; change (csize 24) with 8192 in *; lia).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & _).
    destruct R2 as (_ & _ & _ & _ & _ & _ & IL & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TP & _).
    assert (BF : forall b0, In b0 (a_gq st) -> carved bt st BATCHCLASS (ba_addr b0) /\ SBEG <= ba_addr b0 /\ ba_addr b0 + BATCHSZ <= SBEG + KSPACE
                   /\ 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP /\ IB bt + 920 <= ba_addr b0).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 ltac:(apply in_app_iff; right; exact Hb0)) as (CV0 & BL0 & C1 & C2).
      split; [exact CV0|]. split; [exact C1|]. split; [exact C2|]. clear -BL0 C1 C2 B3 B4 B5 INI I2. ulia. }
    assert (NDG : List.NoDup (map ba_addr (a_gq st))) by (rewrite map_app in WQ5; exact (NoDup_app_remove_l _ _ WQ5)).
    assert (OBJDIS : forall j1 j2 b1 b2, nth_error (a_gq st) j1 = Some b1 -> nth_error (a_gq st) j2 = Some b2 -> j1 <> j2 ->
                       ba_addr b1 + BATCHSZ <= ba_addr b2 \/ ba_addr b2 + BATCHSZ <= ba_addr b1).
    { intros j1 j2 b1 b2 H1 H2 NEj. destruct (BF b1 (nth_error_In _ _ H1)) as (CV1 & _). destruct (BF b2 (nth_error_In _ _ H2)) as (CV2 & _).
      destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr b1) BATCHCLASS (ba_addr b2) Hc30 Hc30 CV1 CV2) as [[_ EA] | Dj]; [| change (csize BATCHCLASS) with 8192 in Dj; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia].
      exfalso. apply NEj. apply (proj1 (NoDup_nth_error (map ba_addr (a_gq st))) NDG j1 j2); [rewrite length_map; exact (nth_error_lt _ _ _ H1)|].
      rewrite !nth_error_map, H1, H2. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite EA. reflexivity. }
    (* [comment removed for export] *)
    set (nxt := match nth_error (a_gq st) (S i) with Some b2 => ba_addr b2 | None => 0 end).
    set (prevw := match i with O => [] | S i' => match nth_error (a_gq st) i' with Some bp => [(ba_addr bp, nxt)] | None => [] end end).
    set (ws := (IB bt + 888, Z.of_nat (length gq')) :: (IB bt + 896, match gq' with [] => 0 | b0 :: _ => ba_addr b0 end)
               :: (IB bt + 904, match rev gq' with [] => 0 | b0 :: _ => ba_addr b0 end) :: (IB bt + 912, q_bytes gq') :: prevw).
    assert (PWI : forall a v, In (a, v) prevw -> exists i' bp, i = S i' /\ nth_error (a_gq st) i' = Some bp /\ a = ba_addr bp /\ v = nxt).
    { intros a v Hin. unfold prevw in Hin. destruct i as [|i']; [destruct Hin|]. destruct (nth_error (a_gq st) i') as [bp|] eqn:EP; [| destruct Hin].
      destruct Hin as [E | []]. injection E as <- <-. exists i', bp. split; [reflexivity | split; [exact EP | split; reflexivity]]. }
    assert (WSI : forall a v, In (a, v) ws -> (IB bt + 888 <= a /\ a + 8 <= IB bt + 920) \/ In (a, v) prevw).
    { intros a v [E | [E | [E | [E | Hin]]]]; [left | left | left | left | right; exact Hin]; injection E as <- _; lia. }
    assert (WSOK : ws_ok ws).
    { intros a v Hin. destruct (WSI a v Hin) as [A | Hp]; [clear -A INI I1 I2; ulia|].
      destruct (PWI a v Hp) as (i' & bp & _ & Hbp & -> & _). destruct (BF bp (nth_error_In _ _ Hbp)) as (_ & _ & _ & Q1 & Q2 & _). unfold BATCHSZ in Q2. lia. }
    set (IDEAL := putl M0 ws).
    set (M0' := fun a : word => if Xd (u a) then IDEAL a else M' a).
    assert (WSX : forall a v z, In (a, v) ws -> a <= z < a + 8 -> X z /\ (qhdr bt z \/ exists bp, In bp (a_gq st) /\ ba_addr bp <= z < ba_addr bp + 8)).
    { intros a v z Hin Hz. destruct (WSI a v Hin) as [A | Hp].
      - assert (Q : qhdr bt z) by ((lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); lia). split; [exact (XQ z Q) | left; exact Q].
      - destruct (PWI a v Hp) as (i' & bp & Ei & Hbp & -> & _). split; [exact (XP i' bp Ei Hbp z Hz) | right; exists bp; split; [exact (nth_error_In _ _ Hbp) | exact Hz]]. }
    assert (OFFX : forall z, ~ X z -> 0 <= z < 2 ^ 64 -> M0' (Z_to_bv 64 z) = M' (Z_to_bv 64 z)).
    { intros z NX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Xd z); [contradiction | reflexivity]. }
    assert (INX : forall z, X z -> 0 <= z < 2 ^ 64 -> M0' (Z_to_bv 64 z) = IDEAL (Z_to_bv 64 z)).
    { intros z HX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Xd z); [reflexivity | contradiction]. }
    assert (MM0 : forall a : word, ~ X (u a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E | NE]; [exact E | exfalso; exact (NX (proj1 (D a NE)))]. }
    assert (KEEP : forall z, ~ X z -> ~ foot_qbatch_free st z -> 0 <= z < 2 ^ 64 -> M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros z NX NF Hr. rewrite (OFFX z NX Hr). rewrite <- (MM0 (Z_to_bv 64 z)) by (rewrite u64_lit by lia; exact NX).
      destruct (decide (M' (Z_to_bv 64 z) = M (Z_to_bv 64 z))) as [E | NE]; [exact E | exfalso].
      destruct (STEP _ NE) as [[F | F] _]; rewrite u64_lit in F by lia; [exact (NF F) | exact (NX F)]. }
    assert (IDOUT : forall z, (forall a v, In (a, v) ws -> z < a \/ a + 8 <= z) -> 0 <= z < 2 ^ 64 -> IDEAL (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros z OUT Hr. (lazymatch goal with |- ?G => let G' := eval unfold IDEAL in G in change_no_check G' end). apply putl_out; [exact WSOK|]. intros a v Hin. rewrite u64_lit by lia. exact (OUT a v Hin). }
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & TP0 & TP1 & _).
    assert (TNX : forall z, T <= z < T + PG -> ~ X z) by (intros z Hz HX; exact (XB_not_T bt st Lc FF W z (XBD z HX) Hz)).
    assert (FMT : forall z, foot_qbatch_free st z -> (T <= z < T + PG) \/ CEIL <= z).
    { intros z Hf. unfold foot_qbatch_free in Hf. fold c len in Hf. unfold c, BATCHCLASS, T_PC, PC_SZ, PG in *. clear -Hf LEN15. lia. }
    (* [comment removed for export] *)
    assert (AGR : agrees_off (foot_gqpush bt st c None) M0 M0').
    { intros a NE. unfold M0' in NE |- *. destruct (Xd (u a)) as [HX | NX].
      - destruct (putl_changed ws M0 a WSOK NE) as ((a0 & v0 & Hin & Hz) & Dd). split; [| exact Dd].
        destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | (bp & Hbp & Q)]); [left; exact Q | right; left; exists bp; split; [exact Hbp | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia]].
      - rewrite <- (MM0 a NX) in NE. destruct (STEP a NE) as [[F | F] Dd]; [| contradiction]. split; [| exact Dd].
        unfold foot_qbatch_free in F. fold c len in F. (lazymatch goal with |- ?G => let G' := eval unfold foot_gqpush, pc_entry in G in change_no_check G' end).
        destruct F as [F|[F|[F|F]]]; [right; right; left | right; right; left | do 5 right; left; exact F | do 6 right; exact F].
        + clear -F. unfold PC_SZ in *. lia.
        + clear -F LEN15. unfold PC_SZ in *. lia. }
    (* [comment removed for export] *)
    assert (HDRX : forall z, IB bt + 888 <= z < IB bt + 920 -> 0 <= z < 2 ^ 64 /\ X z) by (intros z Hz; split; [clear -Hz INI I1 I2; ulia | apply XQ; exact Hz]).
    assert (PWFAR : forall a' v', In (a', v') prevw -> IB bt + 920 <= a').
    { intros a' v' Hq. destruct (PWI a' v' Hq) as (i' & bp & _ & Hbp & -> & _). destruct (BF bp (nth_error_In _ _ Hbp)) as (_ & _ & _ & _ & _ & _ & Q). exact Q. }
    assert (SEP0 : forall a' v', In (a', v') ws -> (a' = IB bt + 888 /\ v' = Z.of_nat (length gq')) \/ a' + 8 <= IB bt + 888 \/ IB bt + 888 + 8 <= a').
    { intros a' v' [E|[E|[E|[E|Hq]]]]; [injection E as <- <-; left; split; reflexivity | injection E as <- _; right; right; lia | injection E as <- _; right; right; lia | injection E as <- _; right; right; lia |].
      pose proof (PWFAR a' v' Hq). right; right; lia. }
    assert (SEP1 : forall a' v', In (a', v') ws -> (a' = IB bt + 896 /\ v' = match gq' with [] => 0 | b0 :: _ => ba_addr b0 end) \/ a' + 8 <= IB bt + 896 \/ IB bt + 896 + 8 <= a').
    { intros a' v' [E|[E|[E|[E|Hq]]]]; [injection E as <- _; right; left; lia | injection E as <- <-; left; split; reflexivity | injection E as <- _; right; right; lia | injection E as <- _; right; right; lia |].
      pose proof (PWFAR a' v' Hq). right; right; lia. }
    assert (SEP2 : forall a' v', In (a', v') ws -> (a' = IB bt + 904 /\ v' = match rev gq' with [] => 0 | b0 :: _ => ba_addr b0 end) \/ a' + 8 <= IB bt + 904 \/ IB bt + 904 + 8 <= a').
    { intros a' v' [E|[E|[E|[E|Hq]]]]; [injection E as <- _; right; left; lia | injection E as <- _; right; left; lia | injection E as <- <-; left; split; reflexivity | injection E as <- _; right; right; lia |].
      pose proof (PWFAR a' v' Hq). right; right; lia. }
    assert (SEP3 : forall a' v', In (a', v') ws -> (a' = IB bt + 912 /\ v' = q_bytes gq') \/ a' + 8 <= IB bt + 912 \/ IB bt + 912 + 8 <= a').
    { intros a' v' [E|[E|[E|[E|Hq]]]]; [injection E as <- _; right; left; lia | injection E as <- _; right; left; lia | injection E as <- _; right; left; lia | injection E as <- <-; left; split; reflexivity |].
      pose proof (PWFAR a' v' Hq). right; right; lia. }
    assert (NL : rep_list bt M0' (IB bt + 888) gq').
    { assert (RI : 0 <= IB bt + 888 /\ IB bt + 920 < 2 ^ 64) by (clear -INI I1 I2; ulia). (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end).
      replace (IB bt + 888 + 8) with (IB bt + 896) by lia. replace (IB bt + 888 + 16) with (IB bt + 904) by lia. replace (IB bt + 888 + 24) with (IB bt + 912) by lia.
      split. { eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 _ _ WSOK ltac:(left; reflexivity) SEP0 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
               intros z Hz. cbn in Hz. destruct (HDRX z ltac:(lia)) as [Hr HX]. exact (INX z HX Hr). }
      split. { eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 _ _ WSOK ltac:(right; left; reflexivity) SEP1 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
               intros z Hz. cbn in Hz. destruct (HDRX z ltac:(lia)) as [Hr HX]. exact (INX z HX Hr). }
      split. { eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 _ _ WSOK ltac:(right; right; left; reflexivity) SEP2 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
               intros z Hz. cbn in Hz. destruct (HDRX z ltac:(lia)) as [Hr HX]. exact (INX z HX Hr). }
      eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 _ _ WSOK ltac:(do 3 right; left; reflexivity) SEP3 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros z Hz. cbn in Hz. destruct (HDRX z ltac:(lia)) as [Hr HX]. exact (INX z HX Hr). }
    (* [comment removed for export] *)
    assert (SAMEB : forall b0, In b0 (a_gq st) -> forall z, ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> (forall a v, In (a, v) prevw -> z < a \/ a + 8 <= z) ->
                      M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros b0 Hb0 z Hz NP. destruct (BF b0 Hb0) as (CV0 & C1 & C2 & C3 & C4 & _ & C6).
      assert (Hr : 0 <= z < 2 ^ 64) by lia.
      assert (IDS : IDEAL (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
      { apply IDOUT; [| exact Hr]. intros a v Hin. destruct (WSI a v Hin) as [A | Hp]; [lia | exact (NP a v Hp)]. }
      destruct (Xd z) as [HX | NX]; [rewrite (INX z HX Hr); exact IDS|].
      apply (KEEP z NX); [| exact Hr]. intros Hf. destruct (FMT z Hf) as [F | F]; [| clear -F Hz C2 B4; ulia].
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & INT & _) & _).
      assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
      clear -F Hz C1 C2 TPG. ulia. }
    assert (NB : rep_batches bt M0' gq').
    { intros j b0 Hj. unfold gq', G1, G2 in Hj |- *. rewrite (nth_error_remove (a_gq st) i j Hil) in Hj. rewrite (nth_error_remove (a_gq st) i (S j) Hil).
      set (oj := if (j <? i)%nat then j else S j) in *.
      assert (Hoj : nth_error (a_gq st) oj = Some b0) by ((lazymatch goal with |- ?G => let G' := eval unfold oj in G in change_no_check G' end); destruct (j <? i)%nat; exact Hj).
      assert (NEoj : oj <> i) by ((lazymatch goal with |- ?G => let G' := eval unfold oj in G in change_no_check G' end); destruct (Nat.ltb_spec j i); lia).
      pose proof (nth_error_In _ _ Hoj) as Hin0. destruct (BF b0 Hin0) as (CV0 & C1 & C2 & C3 & C4 & C5 & C6). unfold BATCHSZ, BATCHCAP in *.
      destruct (R6 oj b0 Hoj) as (Q1 & Q2 & Q3 & Q4 & QW).
      (* [comment removed for export] *)
      assert (PWB : forall a v z, In (a, v) prevw -> ba_addr b0 <= z < ba_addr b0 + 8192 -> ~ (ba_addr b0 <= z < ba_addr b0 + 8 /\ S oj = i) -> z < a \/ a + 8 <= z).
      { intros a v z Hp Hz NO. destruct (PWI a v Hp) as (i' & bp & Ei & Hbp & -> & _).
        destruct (Nat.eq_dec oj i') as [E | NEi]; [rewrite E in Hoj; rewrite Hoj in Hbp; injection Hbp as <-; destruct (Z_lt_dec z (ba_addr b0 + 8)); [exfalso; apply NO; split; [lia | lia] | right; lia]|].
        destruct (OBJDIS oj i' b0 bp Hoj Hbp NEi); unfold BATCHSZ in *; lia. }
      split.
      { destruct (Nat.eq_dec (S oj) i) as [ES | NES].
        - (* [comment removed for export] *)
          assert (EJ : (j <? i)%nat = true) by (unfold oj in ES; destruct (Nat.ltb_spec j i); [reflexivity | lia]).
          assert (Eoj : oj = j) by ((lazymatch goal with |- ?G => let G' := eval unfold oj in G in change_no_check G' end); rewrite EJ; reflexivity).
          assert (ESJ : (S j <? i)%nat = false) by (apply Nat.ltb_ge; lia). rewrite ESJ.
          assert (INP : In (ba_addr b0, nxt) prevw).
          { (lazymatch goal with |- ?G => let G' := eval unfold prevw in G in change_no_check G' end). rewrite <- ES. rewrite Hoj. left. reflexivity. }
          assert (ENX : nxt = match nth_error (a_gq st) (S (S j)) with Some b' => ba_addr b' | None => 0 end) by ((lazymatch goal with |- ?G => let G' := eval unfold nxt in G in change_no_check G' end); rewrite <- ES, Eoj; reflexivity).
          rewrite <- ENX.
          assert (SEPP : forall a' v', In (a', v') ws -> (a' = ba_addr b0 /\ v' = nxt) \/ a' + 8 <= ba_addr b0 \/ ba_addr b0 + 8 <= a').
          { intros a' v' Hin'. destruct (WSI a' v' Hin') as [A | Hp]; [right; left; lia|].
            destruct (PWI a' v' Hp) as (i' & bp & Ei & Hbp & -> & ->). left. split; [| reflexivity].
            assert (i' = oj) by lia. subst i'. rewrite Hoj in Hbp. injection Hbp as <-. reflexivity. }
          eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 _ _ WSOK ltac:(do 4 right; exact INP) SEPP ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          intros z Hz. cbn in Hz. apply INX; [| lia]. destruct (PWI _ _ INP) as (i' & bp & Ei & Hbp & EA & _).
          apply (XP i' bp Ei Hbp z). rewrite <- EA. lia.
        - (* [comment removed for export] *)
          assert (ENX : (if (S j <? i)%nat then nth_error (a_gq st) (S j) else nth_error (a_gq st) (S (S j))) = nth_error (a_gq st) (S oj)).
          { unfold oj in NES |- *. destruct (Nat.ltb_spec j i) as [LT | GE]; [destruct (Nat.ltb_spec (S j) i); [reflexivity | lia] | destruct (Nat.ltb_spec (S j) i); [lia | reflexivity]]. }
          rewrite ENX. eapply (cellZ_frame _ _ _ _ _ _ Q1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. intros z Hz. cbn in Hz.
          apply (SAMEB b0 Hin0 z ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia)). intros a v Hp. apply (PWB a v z Hp ltac:(lia)). intros [_ E]. exact (NES E). }
      assert (SM : forall z, ba_addr b0 + 8 <= z < ba_addr b0 + 8192 -> M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
      { intros z Hz. apply (SAMEB b0 Hin0 z ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia)). intros a v Hp. apply (PWB a v z Hp ltac:(lia)). intros [E _]. lia. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply SM; lia]. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply SM; lia]. }
      split. { intros j0 mn Hj0. pose proof (nth_error_lt _ _ _ Hj0) as Hl. eapply (cellZ_frame _ _ _ _ _ _ (Q4 j0 mn Hj0)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply SM; lia]. }
      eapply (writableZ_frame _ _ _ _ _ QW). intros z Hz. unfold BATCHSZ in Hz.
      destruct (decide (M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z))) as [E | NE]; [left; exact E | right].
      assert (Hr : 0 <= z < 2 ^ 64) by lia. destruct (Xd z) as [HX | NX].
      - rewrite (INX z HX Hr) in NE |- *. exact (proj2 (putl_changed ws M0 _ WSOK NE)).
      - rewrite (OFFX z NX Hr) in NE |- *. rewrite <- (MM0 (Z_to_bv 64 z)) in NE by (rewrite u64_lit by lia; exact NX). exact (proj2 (STEP _ NE)). }
    (* [comment removed for export] *)
    assert (NPC : rep_pclass bt M0' T (a_cinit st) c (a_cache st c ++ [k])).
    { destruct (TP c Hc30) as (Q1 & Q2 & Q3 & Q4). unfold rep_pclass in *. cbn zeta in *. unfold T_PC, PC_SZ, PG in *.
      assert (RT0 : 0 <= T /\ T + 4096 < 2 ^ 64) by (clear -TP0 TP1; ulia).
      assert (PCK : forall z, T + 208 + 80 * c + 4 <= z < T + 208 + 80 * c + 16 + 4 * len -> M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
      { intros z Hz. apply KEEP; [apply TNX; clear -Hz Hc30 LEN15; lia | | clear -Hz RT0 Hc30 LEN15; lia].
        (lazymatch goal with |- ?G => let G' := eval unfold foot_qbatch_free in G in change_no_check G' end). fold c len. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros [F|[F|[F|F]]]; try (clear -F Hz Hc30 LEN15; lia).
        exfalso. clear -F Hz RT0 TP1 Hc30 LEN15. ulia. }
      assert (OFFT : forall z, T <= z < T + 4096 -> M0' (Z_to_bv 64 z) = M' (Z_to_bv 64 z)) by (intros z Hz; apply OFFX; [apply TNX; exact Hz | lia]).
      rewrite length_app, Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). fold len. change (Z.of_nat 1) with 1.
      split. { eapply (cellZ_frame _ _ _ _ _ _ CCNT); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply OFFT; clear -Hz Hc30; lia]. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply PCK; clear -Hz LEN15; lia]. }
      split. { eapply (cellZ_frame _ _ _ _ _ _ Q3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply PCK; clear -Hz LEN15; lia]. }
      intros i0 k0 Hk0. destruct (Nat.lt_ge_cases i0 (length (a_cache st c))) as [LT | GE].
      - rewrite nth_error_app1 in Hk0 by exact LT. eapply (cellZ_frame _ _ _ _ _ _ (Q4 i0 k0 Hk0)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply PCK; (lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hz LT; lia].
      - rewrite nth_error_app2 in Hk0 by exact GE. destruct (i0 - length (a_cache st c))%nat as [|d] eqn:ED; [| destruct d; discriminate Hk0]. cbn in Hk0. injection Hk0 as <-.
        assert (Ei : Z.of_nat i0 = len) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia). rewrite Ei.
        eapply (cellZ_frame _ _ _ _ _ _ CCH); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply OFFT; clear -Hz Hc30 LEN15; lia]. }
    (* [comment removed for export] *)
    assert (QREL : forall x, In x (flat_map ba_items gq') <-> In x (flat_map ba_items (a_gq st)) /\ Some x <> @None (Z * Z)).
    { intros x. rewrite Hgq. (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). rewrite !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items app] in G in change_no_check G' end). split; [intros H; split; [exact H | discriminate] | intros [H _]; exact H]. }
    assert (RC : Rep bt (set_cache (set_gq st gq') c (a_cache st c ++ [k])) Lc FF M0' mdl').
    { apply (OPS_REP_gqpush_pf bt st Lc FF M0 M0' mdl mdl' gq' c (a_cache st c ++ [k]) None qt qg W R Hc30 QREL); [| exact AGR | exact NL | exact NB | exact NPC | | exact SBM | exact MI | intros _; left; intros E0; rewrite E0 in Hnth; destruct i; discriminate Hnth].
      - intros m0 n0 E. discriminate E.
      - intros m0 n0 E. discriminate E. }
    (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). rewrite Hnth. (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end). fold G1 G2 gq' c k.
    exists M0'. split; [exact RC|].
    intros a NE. unfold M0' in NE. destruct (Xd (u a)) as [HX | NX]; [| exfalso; exact (NE eq_refl)]. split; [exact HX|].
    destruct (decide (M' a = M a)) as [E1 | NE1]; [| exact (proj2 (STEP a NE1))].
    destruct (decide (M a = M0 a)) as [E2 | NE2]; [| rewrite E1; exact (proj2 (D a NE2))].
    rewrite E1, E2 in NE. assert (NE3 : IDEAL a <> M0 a) by (intros E3; apply NE; symmetry; exact E3).
    destruct (putl_changed ws M0 a WSOK NE3) as ((a0 & v0 & Hin & Hz) & _).
    destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | (bp & Hbp & Q)]); [exact (HDEF a Q)|].
    rewrite E1, E2. destruct (In_nth_error _ _ Hbp) as [jp Hjp]. destruct (R6 jp bp Hjp) as (_ & _ & _ & _ & CW).
    pose proof (proj1 (CW (u a) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia))) as DF.
    assert (EA : Z_to_bv 64 (u a) = a) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range a); lia); reflexivity). rewrite EA in DF. exact DF.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Rep_proj_ext : forall st st' Lc FF M mdl,
    a_reg st' = a_reg st -> a_cinit st' = a_cinit st -> (forall c0, a_cache st' c0 = a_cache st c0) -> a_tq st' = a_tq st -> a_gq st' = a_gq st ->
    a_sec st' = a_sec st -> a_nres st' = a_nres st -> a_dep st' = a_dep st -> a_hint st' = a_hint st -> a_ialloc st' = a_ialloc st ->
    a_aa st' = a_aa st -> a_kact st' = a_kact st -> a_shsec st' = a_shsec st ->
    Rep bt st Lc FF M mdl -> Rep bt st' Lc FF M mdl.
  Proof.
    intros [r ci ca tq gq se nr de hi ia aa ka sh] [r' ci' ca' tq' gq' se' nr' de' hi' ia' aa' ka' sh']. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    intros Lc FF M mdl -> -> EC -> -> -> -> -> -> -> -> -> ->.
    intros (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). split; [exact P1|]. split; [exact P2|].
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TREST). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end). cbn [a_tq a_cinit a_cache] in *.
             split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. split; [exact T5|]. split; [exact T6|]. split; [exact TL|].
             split; [| exact TREST]. intros c0 Hc0. rewrite (EC c0). exact (TP c0 Hc0). }
    split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|]. split; [exact P11|].
    split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|]. split; [exact P17|]. split; [exact P18|]. exact P19.
  Qed.

  Theorem RepX_resync_qhdr : forall (X : Z -> Prop) st Lc FF (M : mem) mdl (qt qg : Z),
    WFq bt st Lc FF qt qg -> RepX bt X st Lc FF M mdl ->
    rep_list bt M (IB bt + 888) (a_gq st) -> (forall a : word, qhdr bt (u a) -> M a <> None) ->
    RepX bt (fun z => X z /\ ~ qhdr bt z) st Lc FF M mdl.
  Proof.
    intros X st Lc FF M mdl qt qg W (M0 & R & D) NLM HDEF.
    pose proof (Xdec_iv (IB bt + 888) (IB bt + 920)) as Qd.
    set (M0' := fun a : word => if Qd (u a) then M a else M0 a).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    assert (INQ : forall z, IB bt + 888 <= z < IB bt + 920 -> 0 <= z < 2 ^ 64 -> M0' (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
    { intros z Hz Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Qd z); [reflexivity | lia]. }
    assert (OUTQ : forall z, ~ (IB bt + 888 <= z < IB bt + 920) -> 0 <= z < 2 ^ 64 -> M0' (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros z Hz Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Qd z); [lia | reflexivity]. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & _ & _ & _ & _ & _ & _ & _ & (_ & BU2 & _) & _).
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TP & _).
    assert (HC1 : 1 <= 1 <= 30) by lia.
    assert (RC : Rep bt (set_cache (set_gq st (a_gq st)) 1 (a_cache st 1)) Lc FF M0' mdl).
    { apply (OPS_REP_gqpush_pf bt st Lc FF M0 M0' mdl mdl (a_gq st) 1 (a_cache st 1) None qt qg W R HC1); [idtac .. | intros NE0; left; exact NE0].
      - intros x. split; [intros H; split; [exact H | discriminate] | intros [H _]; exact H].
      - intros m0 n0 E. discriminate E.
      - intros a NE. unfold M0' in NE |- *. destruct (Qd (u a)) as [Q | NQ]; [| exfalso; exact (NE eq_refl)]. split; [left; exact Q | exact (HDEF a Q)].
      - destruct NLM as (L1 & L2 & L3 & L4). assert (RI : 0 <= IB bt + 888 /\ IB bt + 920 < 2 ^ 64) by (clear -INI I1 I2; ulia). (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end).
        split; [eapply (cellZ_frame _ _ _ _ _ _ L1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply INQ; lia]|].
        split; [eapply (cellZ_frame _ _ _ _ _ _ L2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply INQ; lia]|].
        split; [eapply (cellZ_frame _ _ _ _ _ _ L3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply INQ; lia]|].
        eapply (cellZ_frame _ _ _ _ _ _ L4); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply INQ; lia].
      - assert (DEF : DEFK M0 M0') by (intros a NE; unfold M0' in NE |- *; destruct (Qd (u a)) as [Q | NQ]; [exact (HDEF a Q) | exfalso; exact (NE eq_refl)]).
        eapply (rep_batches_frame bt M0 M0' DEF); [exact R6 | |].
        + intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 ltac:(apply in_app_iff; right; exact Hb0)) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 B3 B4 B5. ulia.
        + intros b0 z Hb0 Hz Hr. apply OUTQ; [| exact Hr]. destruct (batch_facts bt st Lc FF W b0 ltac:(apply in_app_iff; right; exact Hb0)) as (_ & BL1 & BL2 & BL3).
          unfold foot_batch in Hz. clear -Hz BL2 B3 INI I2. ulia.
      - pose proof (cache_len bt st Lc FF W 1 HC1) as CL'. pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & TP0 & TP1 & TPI & _).
        eapply (rep_pclass_frame bt M0 M0'); [exact (TP 1 HC1) | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -TP0; ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -TP1; ulia | exact CL' |].
        intros z Hz Hr. apply OUTQ; [| exact Hr]. unfold T_PC, PC_SZ in Hz. clear -Hz TPI INI. ulia.
      - intros m0 n0 E. discriminate E.
      - apply same_but_materialized_refl.
      - exact BU2. }
    exists M0'. split.
    - apply (Rep_proj_ext _ st Lc FF M0' mdl) in RC; try reflexivity; [exact RC|].
      intros c0. (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_gq] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 1) as [-> | NE]; reflexivity.
    - intros a NE. unfold M0' in NE. destruct (Qd (u a)) as [Q | NQ]; [exfalso; exact (NE eq_refl)|].
      destruct (D a NE) as [HX Dd]. split; [split; [exact HX | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); exact NQ] | exact Dd].
  Qed.

  (* [comment removed for export] *)
  Theorem XB_free_not_cells : forall st Lc FF (qt qg : Z) a z, WFq bt st Lc FF qt qg ->
    carved bt st BATCHCLASS a -> (in_cache_c bt st BATCHCLASS a \/ in_fa_c bt st BATCHCLASS a) -> a <= z < a + BATCHSZ -> ~ rep_cells bt st Lc FF z.
  Proof.
    intros st Lc FF qt qg a z W CVa OWN Hz RCz.
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    destruct (carved_range bt st Lc FF W BATCHCLASS a HC24 CVa) as (C1 & C2 & C3 & C4 & C5). change (csize BATCHCLASS) with 8192 in C2, C4. unfold BATCHSZ in Hz.
    pose proof W as ((WR1 & _) & _). destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & _).
    destruct PART as (_ & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    assert (XBz : XB bt st z). { right. exists a. split; [split; [exact CVa | right; exact OWN] | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
    destruct RCz as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
    - destruct (img_kinds bt st Lc FF W z ltac:(left; exact K)) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
    - destruct (decide (bt_ptrarr bt <= z < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
      + pose proof W as (_ & _ & _ & (S1 & _ & S3 & _) & _ & _ & _ & _ & (_ & _ & _ & _ & _ & IN8 & _) & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as [SP | SP]; clear -SP IN Hz C3 C4 S1 S3; ulia.
      + destruct (img_kinds bt st Lc FF W z ltac:(right; left; split; [exact K | exact NI])) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
    - destruct (thread_cells_where bt z K) as [TZ | TZ].
      + apply (XB_not_T bt st Lc FF W z XBz). unfold T_UNW, PG in *. clear -TZ. lia.
      + pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INC & _) & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as [SP | SP]; clear -SP TZ Hz C3 C4; ulia.
    - destruct K as (c0 & Hc0 & K). pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
      unfold foot_region in K. destruct K as [[K _] | K]; [clear -K E9 Hz C4; ulia|].
      pose proof (region_facts bt st Lc FF W BATCHCLASS HC24) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 BATCHCLASS) as [LT|[EQ|GT]].
      * assert (c0 * 2 ^ 32 + 2 ^ 32 <= BATCHCLASS * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H K Hz C1 C2 E6 E7. lia.
      * subst c0. clear -K Hz C1 C2 F2 F3 E6 E7. lia.
      * assert (BATCHCLASS * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (BATCHCLASS * 2 ^ 32 + 2 ^ 32) with ((BATCHCLASS + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        destruct (WR1 BATCHCLASS HC24) as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'. clear -H K Hz C1 C2 F2 F3 R1' R3'. lia.
    - destruct K as (b0 & Hb0 & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BL & _).
      destruct (chunk_cases bt st Lc FF W BATCHCLASS a BATCHCLASS (ba_addr b0) HC24 HC24 CVa CVb) as [[_ EA] | Dj].
      + apply (P8 a ltac:(exists b0; split; [exact Hb0 | symmetry; exact EA]) eq_refl). right; right. exact OWN.
      + change (csize BATCHCLASS) with 8192 in Dj. unfold BATCHCAP in BL. clear -Dj K Hz BL. lia.
    - destruct K as (sc & Hs & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      pose proof (rz_range (sc_n sc)) as RZ. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [SP | SP]; clear -SP K Hz C3 C4 A5 A6 A7 RZ; ulia.
    - destruct K as (p' & n' & Hown & K). pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' z Hown K) as [(HP' & Z1' & Z2 & Z3' & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1' & N1')].
      + apply (XB_not_owned bt st Lc FF W z (blk_class n') (prim_alloc_beg p' n') XBz HC' CV'); [| unfold prim_alloc_beg in *; clear -Z1' Z2 Z3' Z4 N1' RZ'; lia].
        destruct Hown as [HL | HQ].
        * right. pose proof (live_chunk bt st Lc FF W p' n' HL HP') as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & G3 & _). exact G3.
        * left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ HP') as Gv. cbn zeta in Gv. replace (p' - 16 + 16) with p' in Gv by lia. destruct Gv as (_ & _ & G3 & _). exact G3.
      + destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')) as [SP | SP]; rewrite Eu', En' in *; clear -SP Z1' Hz C3 C4 A5 A6 N1'; ulia.
    - destruct (img_kinds bt st Lc FF W z ltac:(right; right; left; exact K)) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
    - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
      pose proof (node_addr_block bt st id Hid) as Hb. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
      destruct HIn as [Eb | Hnb].
      + pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & INN & _) & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INN ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as [SP | SP]; rewrite Eb in *; clear -SP K Hb Hz C3 C4; ulia.
      + destruct (space_vs_dyn bt st Lc FF W _ _ (node_dyn st bb Hnb)) as [SP | SP]; clear -SP K Hb Hz C3 C4; ulia.
    - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
      unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, FAKE_SIZE in G in change_no_check G' end); lia)) as [SP | SP]; clear -SP K Hz C3 C4; ulia.
      + destruct (img_kinds bt st Lc FF W z ltac:(do 3 right; left; exact K)) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
      + destruct (space_vs_fixed bt st Lc FF W _ _ (dtls_member bt st Lc FF W) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as [SP | SP]; clear -SP K Hz C3 C4; ulia.
    - destruct K as (f & k0 & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (F1 & F2 & F3 & F4 & _).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
      destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, FAKE_SIZE in G in change_no_check G' end); lia)) as [SP | SP]; clear -SP K Hz C3 C4 F1 F2 F4; ulia.
    - destruct (img_kinds bt st Lc FF W z ltac:(do 4 right; left; exact K)) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
    - apply (XB_not_band bt st Lc FF W z XBz). destruct K as (c0 & Hc0 & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). clear -K Q1 Q2 Q3 Q4 Q5 Q6 B3 B4 B5 B6 B7. Zlia.
    - apply (XB_not_band bt st Lc FF W z XBz). destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). clear -K A1 A2 B6 B7. Zlia.
    - destruct (img_kinds bt st Lc FF W z ltac:(do 5 right; exact K)) as [LT _]. clear -LT Hz C3 I2 B3. ulia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma XB_recycle_prim : forall st ba it its rest c k z, a_gq st = BATCH ba (it :: its) :: rest -> XB bt st z -> XB bt (op_recycle_prim st c k) z.
  Proof.
    intros st ba it its rest c k z Hgq. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim in G in change_no_check G' end). rewrite (op_qitem_eq st ba it its rest Hgq). apply XB_mono.
    - intros a H. exact H.
    - intros a H. left. apply (proj2 (in_batch_gq_head st ba it its rest a Hgq)). exact H.
    - intros a (k0 & Hk0 & E). left. exists k0. split; [| exact E]. (lazymatch goal with |- ?G => let G' := eval unfold op_cache_push in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_gq] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
      destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; [apply in_app_iff; left; exact Hk0 | exact Hk0].
    - intros a H. exact H.
  Qed.
  Lemma XB_recycle_sec : forall st ba it its rest i z, a_gq st = BATCH ba (it :: its) :: rest -> XB bt st z -> XB bt (op_recycle_sec st i) z.
  Proof.
    intros st ba it its rest i z Hgq. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec in G in change_no_check G' end). rewrite (op_qitem_eq st ba it its rest Hgq). apply XB_mono.
    - intros a H. exact H.
    - intros a H. left. apply (proj2 (in_batch_gq_head st ba it its rest a Hgq)). exact H.
    - intros a H. left. exact H.
    - intros a H. exact H.
  Qed.
  Lemma XB_qbatch_free : forall st Lc FF (qt qg : Z) i ba z, WFq bt st Lc FF qt qg -> nth_error (a_gq st) i = Some (BATCH ba []) ->
    XB bt st z -> XB bt (op_qbatch_free SBEG st i) z.
  Proof.
    intros st Lc FF qt qg i ba z W Hnth. (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). rewrite Hnth. (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end). pose proof (nth_error_split_fs (a_gq st) i _ Hnth) as Hgq. apply XB_mono.
    - intros a H. exact H.
    - intros a (b0 & Hb0 & E). destruct (Z.eq_dec a ba) as [-> | NE].
      + right; left. exists (compact_of SBEG BATCHCLASS ba). split; [(lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end); rewrite fupdZ_same; apply in_app_iff; right; left; reflexivity|].
        symmetry. apply (carved_roundtrip bt st Lc FF BATCHCLASS ba W ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)).
        destruct (batch_facts bt st Lc FF W (BATCH ba []) ltac:(apply in_app_iff; right; exact (nth_error_In _ _ Hnth))) as (CV & _). exact CV.
      + left. exists b0. split; [| exact E]. (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_cache set_gq] in G in change_no_check G' end). rewrite Hgq in Hb0. rewrite !in_app_iff in Hb0 |- *. cbn [In] in Hb0.
        destruct Hb0 as [H | [H | [H | H]]]; [left; exact H | right; left; exact H | exfalso; apply NE; rewrite <- E, <- H; reflexivity | right; right; exact H].
    - intros a (k0 & Hk0 & E). left. exists k0. split; [| exact E]. (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache] in G in change_no_check G' end). rewrite fupdZ_same. apply in_app_iff. left. exact Hk0.
    - intros a H. exact H.
  Qed.
  Lemma XB_drain_top : forall st c m z, XB bt st z -> XB bt (op_drain_top st c m) z.
  Proof.
    intros st c m z. (lazymatch goal with |- ?G => let G' := eval unfold op_drain_top in G in change_no_check G' end). cbn zeta. set (j := Z.to_nat (Z.of_nat (length (a_cache st c)) - m)). apply XB_mono.
    - intros a (j0 & H0 & H1 & H2). exists j0. split; [exact H0|]. split; [| exact H2]. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_cache set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); exact H1.
    - intros a H. left. exact H.
    - intros a (k0 & Hk0 & E). (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, in_fa_c in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_reg set_cache set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; [| left; exists k0; exact (conj Hk0 E)].
      (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). rewrite <- (firstn_skipn j (a_cache st BATCHCLASS)) in Hk0. apply in_app_iff in Hk0. destruct Hk0 as [H | H].
      + left. exists k0. exact (conj H E).
      + right. exists k0. split; [apply in_app_iff; right; exact H | exact E].
    - intros a (k0 & Hk0 & E). exists k0. split; [| exact E]. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_cache set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; [(lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end); apply in_app_iff; left; exact Hk0 | exact Hk0].
  Qed.


End RcX.
End AsAinvOpsRc33.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.








Section Merge.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

End Merge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 AsAinvRepX3 AsAinvOpsRc23 AsAinvOpsRc33.
Section MergeRep.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Notation u := bv_unsigned.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.


End MergeRep.
