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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regcore_eq (r r' : region) : Prop :=
  r_alloc_user r' = r_alloc_user r /\ r_mapped_fa r' = r_mapped_fa r /\ r_free r' = r_free r /\ r_fhole r' = r_fhole r.
Definition st_regcore (st st' : ast) : Prop :=
  (forall c, regcore_eq (a_reg st c) (a_reg st' c))
  /\ (forall c, ~ (1 <= c <= 30) -> a_reg st' c = a_reg st c)
  /\ a_cinit st' = a_cinit st /\ a_cache st' = a_cache st /\ a_tq st' = a_tq st /\ a_gq st' = a_gq st
  /\ a_sec st' = a_sec st /\ a_nres st' = a_nres st /\ a_dep st' = a_dep st /\ a_hint st' = a_hint st
  /\ a_ialloc st' = a_ialloc st /\ a_aa st' = a_aa st /\ a_kact st' = a_kact st /\ a_shsec st' = a_shsec st.

Lemma st_regcore_usermap : forall st c, 1 <= c <= 30 -> st_regcore st (op_usermap st c).
Proof.
  intros st c Hc. (lazymatch goal with |- ?G => let G' := eval unfold st_regcore, op_usermap, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
  split. { intros c'. (lazymatch goal with |- ?G => let G' := eval unfold regcore_eq, fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity. }
  split. { intros c' NC. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; [exfalso; exact (NC Hc) | reflexivity]. }
  repeat split; reflexivity.
Qed.

Section RegCore.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables st st' : ast.
  Hypothesis EQ : st_regcore st st'.
  (* [comment removed for export] *)
  Hypothesis MU : forall c, 1 <= c <= 30 ->
    r_alloc_user (a_reg st' c) <= r_mapped_user (a_reg st' c) /\ r_mapped_user (a_reg st' c) mod KUSERMAP = 0
    /\ r_mapped_user (a_reg st' c) + KUSERMAP <= KREGION_EXHAUST
    (* [comment removed for export] *)
    /\ (r_mapped_user (a_reg st' c) - r_alloc_user (a_reg st' c) < csize c \/ KUSERMAP <= r_mapped_user (a_reg st' c) - r_alloc_user (a_reg st' c) < KUSERMAP + csize c).
  (* [comment removed for export] *)
  Hypothesis MUGE : forall c, 1 <= c <= 30 -> r_mapped_user (a_reg st c) <= r_mapped_user (a_reg st' c).
  Hypothesis MUSUM : sum_mu st <= KUSERMAP * (a_kact st / EVT) -> sum_mu st' <= KUSERMAP * (a_kact st / EVT).

  Lemma carved_regcore : forall c a, carved bt st' c a <-> carved bt st c a.
  Proof using EQ. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end). destruct (proj1 EQ c) as (RAU & _). rewrite RAU. am_tauto. Qed.
  Lemma quar_regcore : quar st' = quar st.
  Proof using EQ. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & ETQ & EGQ & _). rewrite ETQ, EGQ. reflexivity. Qed.
  Lemma registered_regcore : forall p n, registered st' p n <-> registered st p n.
  Proof using EQ. intros p n. (lazymatch goal with |- ?G => let G' := eval unfold registered in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & _ & _ & ES & _). rewrite ES. am_tauto. Qed.
  Lemma in_quar_c_regcore : forall c a, in_quar_c st' c a <-> in_quar_c st c a.
  Proof using EQ. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). rewrite quar_regcore. am_tauto. Qed.
  Lemma in_cache_c_regcore : forall c a, in_cache_c bt st' c a <-> in_cache_c bt st c a.
  Proof using EQ. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c in G in change_no_check G' end). destruct EQ as (_ & _ & _ & EC & _). rewrite EC. am_tauto. Qed.
  Lemma in_fa_c_regcore : forall c a, in_fa_c bt st' c a <-> in_fa_c bt st c a.
  Proof using EQ. intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_fa_c in G in change_no_check G' end). destruct (proj1 EQ c) as (_ & _ & RFR & _). rewrite RFR. am_tauto. Qed.
  Lemma in_batch_regcore : forall a, in_batch st' a <-> in_batch st a.
  Proof using EQ. intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & ETQ & EGQ & _). rewrite ETQ, EGQ. am_tauto. Qed.

  Lemma partition_regcore : forall Lc c, partition_c bt st Lc c -> partition_c bt st' Lc c.
  Proof using EQ.
    intros Lc c P. unfold partition_c in *.
    destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    destruct EQ as (RD & _ & _ & EC & _). destruct (RD c) as (_ & _ & RFR & _).
    pose proof carved_regcore as CV. pose proof in_quar_c_regcore as IQ. pose proof in_cache_c_regcore as ICC. pose proof in_fa_c_regcore as IFA. pose proof in_batch_regcore as IB.
    split; [intros a; rewrite (CV c a), (IQ c a), (ICC c a), (IFA c a), (IB a); exact (P1 a)|].
    split; [intros a; rewrite (IQ c a); exact (P2 a)|].
    split; [intros a; rewrite (ICC c a); exact (P3 a)|].
    split; [intros a; rewrite (IFA c a); exact (P4 a)|].
    split; [intros a; rewrite (IQ c a), (ICC c a); exact (P5 a)|].
    split; [intros a; rewrite (IQ c a), (IFA c a); exact (P6 a)|].
    split; [intros a; rewrite (ICC c a), (IFA c a); exact (P7 a)|].
    split; [intros a Hb Hc; rewrite (IQ c a), (ICC c a), (IFA c a); apply P8; [apply IB; exact Hb | exact Hc]|].
    rewrite EC, RFR. exact (conj P9 P10).
  Qed.

  Lemma wf_batch_regcore : forall b, wf_batch bt st b -> wf_batch bt st' b.
  Proof using EQ.
    intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply carved_regcore; exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV] | [HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | apply carved_regcore; exact CV].
    - right. split; [exact HP | apply registered_regcore; exact RG].
  Qed.
  Lemma wf_batch_regcore0 : forall b, wf_batch0 bt st b -> wf_batch0 bt st' b.
  Proof using EQ.
    intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply carved_regcore; exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV] | [HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | apply carved_regcore; exact CV].
    - right. split; [exact HP | apply registered_regcore; exact RG].
  Qed.

  Lemma dyn_ranges_regcore : dyn_ranges st' = dyn_ranges st.
  Proof using EQ. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). destruct EQ as (_ & _ & _ & _ & _ & _ & ES & _ & ED & _). rewrite ES, ED. reflexivity. Qed.

  Theorem WF_regcore : forall Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg -> WFq bt st' Lc FF qt qg.
  Proof using MU MUGE MUSUM EQ.
    intros Lc FF qt qg W.
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & (K1 & K2 & K3) & WD & WM & WMP & G).
    pose proof EQ as (RD & RO & ECI & EC & ETQ & EGQ & ES & ENR & ED & EH & EIA & EAA & EK & ESH).
    pose proof quar_regcore as QR. pose proof dyn_ranges_regcore as DR.
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split. { split.
             - intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK). destruct (RD c) as (RAU & RFA & RFR & RFH).
               destruct (MU c Hc) as (M1 & M2 & M3 & M4). rewrite RAU in M1, M4.
               (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). rewrite RAU, RFA, RFR, RFH. split; [split; [split; [lia | exact M1] | split; [exact M4 | destruct Y1 as (_ & _ & YA); exact YA]]|]. split; [exact M2|]. split; [exact M3|].
               repeat (split; [assumption|]). split.
               + intros k Hk. destruct (Y9 k Hk) as [Kr CV]. split; [exact Kr | apply carved_regcore; exact CV].
               + split; [apply partition_regcore; exact PART | exact FHK].
             - intros c NC. destruct (WR2 c NC) as [E1 E2]. rewrite (RO c NC), EC. exact (conj E1 E2). }
    split. { intros c Hc. destruct (WC c Hc) as (C1 & C2 & C3). rewrite EC, ECI. split; [exact C1|]. split; [destruct (RD c) as (RAU' & _); rewrite RAU'; exact C2|].
             intros k Hk. destruct (C3 k Hk) as [Kr CV]. split; [exact Kr | apply carved_regcore; exact CV]. }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). rewrite ETQ, EGQ, QR.
             split; [rewrite Forall_forall in Q1 |- *; intros b Hb; apply wf_batch_regcore; exact (Q1 b Hb)|].
             split; [rewrite Forall_forall in Q2 |- *; intros b Hb; apply wf_batch_regcore0; exact (Q2 b Hb)|].
             exact (conj Q3 (conj Q4 (conj Q5 Q6))). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). rewrite ES, ENR, QR. repeat (split; [assumption|]).
             split; [intros p n Hin HP; apply registered_regcore; exact (S7 p n Hin HP)|].
             intros m n Hin HP. apply registered_regcore. exact (S8 m n Hin HP). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| exact (conj LV2 LV3)]. intros p n Hin. destruct (LV1 p n Hin) as (A1 & A2 & A3 & CVL).
             split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros HP. apply carved_regcore. exact (CVL HP). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_fake in G in change_no_check G' end). rewrite EH. exact (conj K1 (conj K2 K3)). }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_depot in G in change_no_check G' end). rewrite ED, EK. exact WD. }
    split. { (* [comment removed for export] *)
             destruct WM as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end). rewrite EK, ESH, ES.
             split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact (MUSUM M4)|].
             intros c Hc. destruct (RD c) as (_ & RFA & _). rewrite RFA.
             pose proof (M5 c Hc) as F5. pose proof (MUGE c Hc) as GE. pose proof (csize_pos c Hc) as [CS1 _].
             assert (DV : r_mapped_user (a_reg st c) / csize c <= r_mapped_user (a_reg st' c) / csize c) by (apply Z.div_le_mono; lia).
             clear -F5 GE DV. lia. }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_maps, all_ranges in G in change_no_check G' end). rewrite DR. exact WMP. }
    exact G.
  Qed.
End RegCore.

Section Usermap.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  (* [comment removed for export] *)
  Ltac fzri A B Cc D E AGc H := eapply (cellZ_frame _ _ _ _ _ _ H);
    [clear -A B; lia | clear -Cc D E; lia | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply AGc; clear -Hi; cbn in Hi; lia].

  Theorem OPS_WF_usermap_pf : OPS_WF_usermap bt.
  Proof using.
    intros st Lc FF c W Hc EX TI MR. pose proof W as ((WR1 & _) & _).
    apply (WF_regcore bt st (op_usermap st c) (st_regcore_usermap st c Hc)); [| | | exact W].
    - intros c0 Hc0. destruct (usermap_fields st c c0) as (RMU & RAU & _). rewrite RMU, RAU.
      destruct (WR1 c0 Hc0) as ((Y1 & YT) & Y2 & Y3 & _). destruct (Z.eqb_spec c0 c) as [-> | NE]; [| split; [lia | split; [exact Y2 | split; [exact Y3 | exact (proj1 YT)]]]].
      split; [unfold KUSERMAP in *; lia|]. split; [| split; [exact EX | right; clear -TI Y1; lia]].
      replace (r_mapped_user (a_reg st c) + KUSERMAP) with (r_mapped_user (a_reg st c) + 1 * KUSERMAP) by lia.
      rewrite Z.mod_add; [exact Y2 | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia].
    - (* [comment removed for export] *)
      intros c0 Hc0. destruct (usermap_fields st c c0) as (RMU & _). rewrite RMU. destruct (Z.eqb_spec c0 c); (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia.
    - (* [comment removed for export] *)
      intros M4. rewrite (sum_mu_upd st (op_usermap st c) c Hc)
        by (intros c0 Hc0 NE0; destruct (usermap_fields st c c0) as (RMU & _); rewrite RMU; destruct (Z.eqb_spec c0 c) as [E|_]; [exfalso; exact (NE0 E) | reflexivity]).
      destruct (usermap_fields st c c) as (RMU & _). rewrite RMU, Z.eqb_refl. unfold mu_room in MR. clear -MR M4. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sum_classes_upd : forall f g c d k, (forall c0, c0 <> c -> g c0 = f c0) -> g c = f c + d -> 1 <= c ->
    sum_classes g k = sum_classes f k + (if c <=? Z.of_nat k then d else 0).
  Proof using.
    intros f g c d k Hne Hc H1. induction k as [|k IH].
    - (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). destruct (Z.leb_spec c (Z.of_nat 0)); lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH. destruct (Z.eq_dec (Z.of_nat (Datatypes.S k)) c) as [E|NE].
      + rewrite E, Hc. destruct (Z.leb_spec c (Z.of_nat k)); destruct (Z.leb_spec c c); lia.
      + rewrite (Hne _ NE). destruct (Z.leb_spec c (Z.of_nat k)); destruct (Z.leb_spec c (Z.of_nat (Datatypes.S k))); lia.
  Qed.

  Lemma range_allowed_last : forall AA lo hi, lo mod PG = 0 -> hi mod PG = 0 -> 0 <= lo -> hi <= 2 ^ 64 ->
    range_allowed (AA ++ [(lo, hi)]) lo hi.
  Proof using.
    intros AA lo hi Hl Hh H0 H1 a Ha. (lazymatch goal with |- ?G => let G' := eval unfold page_allowedb in G in change_no_check G' end). rewrite existsb_app. (lazymatch goal with |- ?G => let G' := eval cbn [existsb fst snd] in G in change_no_check G' end). rewrite orb_false_r.
    apply orb_true_iff. right. (lazymatch goal with |- ?G => let G' := eval unfold page_base, page_base_of, page_size in G in change_no_check G' end). rewrite (u64_lit a) by lia.
    unfold PG in *. rewrite u64_lit by (Z.div_mod_to_equations; lia). apply andb_true_iff. rewrite !Z.leb_le. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fa_holes_ok (st : ast) : Prop :=
    forall c, 1 <= c <= 30 -> r_fhole (a_reg st c) = true -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.


  Definition OPS_REP_usermap_h : Prop := forall st Lc FF M M' mdl mdl' c,
    fa_holes_ok st ->
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    agrees_off (foot_usermap bt st c) M M' ->
    cellZ SG M' (reginfo bt c + 48) 8 (r_mapped_user (a_reg st c) + KUSERMAP) ->
    writableZ SG M' (reginfo bt c) (reginfo bt c + 128) ->
    writableZ SG M' lo (lo + KUSERMAP) ->
    fillZ SG M' (sh_lo lo) (sh_lo lo + KUSERMAP / 8) FA ->
    (r_uhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl)) ->
    (r_uhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: vm_maps (m_vmmaps mdl))) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KUSERMAP)) ->
    (* [comment removed for export] *)
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KUSERMAP)) ->
    Forall (fun iv : word * word => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL
                                   /\ (u (fst iv) + u (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u (fst iv))) (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) -> vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    MInv (a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)]) mdl' -> eager_used mdl' <= eager_used mdl + KUSERMAP ->
    Rep bt (add_meter (op_usermap st c) 0 [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] 0) Lc FF M' mdl'.

  (* [comment removed for export] *)
  Lemma fa_holes_ok_of_WF : forall st Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg -> fa_holes_ok st.
  Proof using. intros st Lc FF qt qg W c Hc. pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FHK). exact FHK. Qed.

  Theorem OPS_REP_usermap_h_pf : OPS_REP_usermap_h.
  Proof using.
    intros st Lc FF M M' mdl mdl' c FHO W R Hc EX lo AGR C48 W128 WSL FSH VMK VMP NA NP' LZ FL' E1 E2 E3 E4 E5 E6 MI EAG.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    assert (Elo : lo = region_beg SBEG c + r_mapped_user (a_reg st c)) by reflexivity.
    assert (SL : lo mod 8 = 0 /\ SBEG <= lo /\ region_beg SBEG c <= lo /\ lo + KUSERMAP + KUSERMAP <= fa_beg SBEG c /\ fa_beg SBEG c + 2 ^ 29 <= SBEG + KSPACE
                 /\ bt_resv6 bt <= lo /\ lo + KUSERMAP <= bt_resv6 bt + bt_resv6_len bt /\ 0 <= lo /\ lo + KUSERMAP < 2 ^ 64 /\ AS_HEAPLO <= lo /\ lo + KUSERMAP <= CEIL
                 /\ region_beg SBEG c mod 2 ^ 16 = 0 /\ lo mod 2 ^ 16 = 0).
    { rewrite Elo. unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *. clear -Y2 Y3 EX Q1 Q5 Q8 X14 X15 X16 Hc SP7 SP8 SPH.
      Z.div_mod_to_equations. ulia. }
    destruct SL as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7 & SL8 & SL9 & SL10 & SL11 & SL12 & SL13).
    (* [comment removed for export] *)
    set (Mmid := fun a : word => if decide (reginfo bt c + 48 <= u a < reginfo bt c + 56) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NE. unfold Mmid in NE |- *.
      destruct (decide (reginfo bt c + 48 <= u a < reginfo bt c + 56)) as [IN|NI]; [exfalso; exact (NE eq_refl)|].
      destruct (AGR a NE) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_usermap in Hf.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]].
      - exact (NI Hf).
      - exact (rijunk_not_cells bt st Lc FF W c (u a) Hc Hf HC).
      - exact (ushadow_not_cells bt st Lc FF W c (u a) Hc Hf HC).
      - exact (uslot_not_supp bt st Lc FF c _ _ W Hc (u a) (or_introl HC) Hf).
      - apply (stats_not_cells bt st Lc FF W (u a)); [unfold T_UNW in Hf; exact Hf | exact HC].
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    clearbody lo.
    (* [comment removed for export] *)
    assert (AG : forall i, ~ (reginfo bt c + 48 <= i < reginfo bt c + 56) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia.
      destruct (decide (reginfo bt c + 48 <= i < reginfo bt c + 56)) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NE. unfold Mmid in NE. destruct (decide (reginfo bt c + 48 <= u a < reginfo bt c + 56)) as [IN|NI]; [| exfalso; exact (NE eq_refl)].
      destruct (W128 (u a) ltac:(lia)) as [D _]. rewrite Z_to_bv_bv_unsigned in D. exact D. }
    assert (AGP : forall i, ~ (SBEG + KSPACE <= i < SBEG + KSPACE + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AG; [| exact Hr]. clear -Hi Q9 Q10. intros X. apply Hi. lia. }
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. apply AGP; [clear -Hi I2 SBH; ulia | clear -Hi I1 I2; ulia]. }
    assert (FIXR : forall lo' hi', In (lo', hi') (bt_fixed bt) -> hi' - lo' < KSPACE -> forall i, lo' <= i < hi' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo' hi' Hin Hlen i Hi Hr. apply AGP; [| exact Hr]. destruct (space_vs_fixed bt st Lc FF W lo' hi' Hin Hlen); clear -H Hi; ulia. }
    assert (DYNR : forall lo' hi', In (lo', hi') (dyn_ranges st) -> forall i, lo' <= i < hi' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo' hi' Hin i Hi Hr. apply AGP; [| exact Hr]. destruct (space_vs_dyn bt st Lc FF W lo' hi' Hin); clear -H Hi; ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AGP; [clear -Hi; lia | exact Hr]. }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AGP; [clear -Hi SBH; ulia | exact Hr]. }
    assert (RIR : forall c0, 1 <= c0 <= 30 -> c0 <> c -> forall i, reginfo bt c0 <= i < reginfo bt c0 + 128 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros c0 Hc0 NE i Hi Hr. apply AG; [| exact Hr]. unfold reginfo in *. clear -Hi Hc0 Hc NE. lia. }
    (* [comment removed for export] *)
    set (r' := REG (r_mapped_user (a_reg st c) + KUSERMAP) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) (r_free (a_reg st c)) false (r_fhole (a_reg st c))).
    set (st' := add_meter (op_usermap st c) 0 [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] 0).
    assert (ER : a_reg st' = fupdZ (a_reg st) c r') by reflexivity.
    assert (FLD : forall c0, r_mapped_user (a_reg st' c0) = (if c0 =? c then r_mapped_user (a_reg st c0) + KUSERMAP else r_mapped_user (a_reg st c0))
                        /\ r_alloc_user (a_reg st' c0) = r_alloc_user (a_reg st c0) /\ r_mapped_fa (a_reg st' c0) = r_mapped_fa (a_reg st c0)
                        /\ r_free (a_reg st' c0) = r_free (a_reg st c0)
                        /\ r_uhole (a_reg st' c0) = (if c0 =? c then false else r_uhole (a_reg st c0)) /\ r_fhole (a_reg st' c0) = r_fhole (a_reg st c0))
      by (intros c0; exact (usermap_fields st c c0)).
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact P2 | uilia | uilia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXR _ _ IN8); [ulia | clear -IN S1 S3; lia | exact Hr].
             - destruct (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { change (rep_thread bt st' M') with (rep_thread bt st M'). eapply rep_thread_frame; [exact DEF | exact P3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. destruct (thread_cells_where bt i Hi) as [A|A].
             - apply (FIXR _ _ INT); [ulia | clear -A; unfold T_UNW, PG in *; lia | exact Hr].
             - apply (FIXR _ _ INC); [ulia | clear -A; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. rewrite ER. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
             - destruct (P4 c Hc) as [G0 F0]. destruct G0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct F0 as (F1 & F2 & F3). (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end).
               assert (AGc : forall i, reginfo bt c <= i < reginfo bt c + 128 -> ~ (reginfo bt c + 48 <= i < reginfo bt c + 56) -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
               { intros i Hi Hn. apply AG; [exact Hn | clear -Hi Q9 Q10 X14 X15; ulia]. }
               unfold KSPACE, PG in Q9, Q10, X15. pose proof ceil_rng as CR.
               split.
               + unfold rep_reginfo in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_alloc_user r_mapped_user] in G in change_no_check G' end).
                 split; [fzri Q9 X14 Q10 X15 CR AGc G1|]. split; [fzri Q9 X14 Q10 X15 CR AGc G2|]. split; [fzri Q9 X14 Q10 X15 CR AGc G3|].
                 split; [fzri Q9 X14 Q10 X15 CR AGc G4|]. split; [fzri Q9 X14 Q10 X15 CR AGc G5|]. split; [fzri Q9 X14 Q10 X15 CR AGc G6|].
                 split; [exact C48|]. split; [fzri Q9 X14 Q10 X15 CR AGc G8|]. destruct G9 as [G9a G9b].
                 split; [eapply (byteZ_frame _ _ _ _ _ G9a); [clear -Q9 X14; lia | clear -Q10 X15 CR; lia | apply AGc; clear; lia] | exact W128].
               + unfold rep_freearray in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_mapped_user] in G in change_no_check G' end). split; [| split; [frW DEF F2 |]].
                 * intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (F1 i k Hk) as C.
                   eapply (cellZ_frame _ _ _ _ _ _ C); [clear -Q1 Q2 Q8 X14; ulia | clear -Hl Q5 Q6 Q7 X15 CR; ulia |].
                   intros i0 Hi0. apply SPCR; [clear -Hi0 Hl Q1 Q2 Q5 Q6 Q7 Q8; ulia | clear -Hi0 Hl Q1 Q2 Q5 Q6 Q7 Q8 X14 X15 CR; ulia].
                 * pose proof (writableZ_keep _ _ _ _ _ DEF F3) as F3'. intros i Hi.
                   destruct (Z.lt_ge_cases i lo) as [LT|GE]; [apply F3'; clear -Hi LT Elo; lia | apply WSL; clear -Hi GE Elo; lia].
             - destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
               destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
               eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | clear -D9 X14; ulia | clear -D10 X15; ulia | clear -D1 D2 D8 X14; ulia | clear -D2 D5 D6 D8 X15; ulia | exact D7 |].
               intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply (RIR c0 Hc0 NE); [clear -Hi; lia | exact Hr] | apply SPCR; [clear -Hi D1 D2 D3 D4 D5 D6 D7; ulia | exact Hr]]. }
    (* [comment removed for export] *)
    assert (BAfree : forall q, rep_batches bt Mmid q -> (forall b, In b q -> In b (a_tq st ++ a_gq st)) -> rep_batches bt M' q).
    { intros q RB SUB. eapply rep_batches_frame; [exact DEF | exact RB | |].
      - intros b Hb. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & BB1 & BB2). clear -BL BB1 BB2 X14 X15. ulia.
      - intros b i Hb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & BB1 & BB2).
        apply SPCR; [clear -Hi BL BB1 BB2; ulia | exact Hr]. }
    split; [change (a_tq st') with (a_tq st); apply (BAfree _ P5); intros b Hb; apply in_app_iff; left; exact Hb|].
    split; [change (a_gq st') with (a_gq st); apply (BAfree _ P6); intros b Hb; apply in_app_iff; right; exact Hb|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct P8 as [HLh HQh].
             assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
               destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
               - apply SPCR; [clear -W1 W2 W3 W4 N1'; lia | exact Hr].
               - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
                 rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
             split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRfree p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRfree (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. exact (IMGR i LT).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear -Hi; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. exact (IMGR i LT).
               + apply (FIXR _ _ (dtls_member bt st Lc FF W)); [clear; ulia | clear -Hi; ulia | exact Hr].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1. Zlia. }
             assert (USL : forall g, lo / 8 <= g < lo / 8 + KUSERMAP / 8 -> uslot bt st c (8 * g)).
             { intros g Hg. (lazymatch goal with |- ?G => let G' := eval unfold uslot in G in change_no_check G' end). rewrite <- Elo. clear -Hg SL1. unfold KUSERMAP in *. Z.div_mod_to_equations. lia. }
             split. { intros c0 g Hc0 Hg NL'. destruct (FLD c0) as (RMU & _). rewrite RMU in Hg.
                      destruct (Z.eqb_spec c0 c) as [-> | NE].
                      - destruct (Z.lt_ge_cases g (lo / 8)) as [OLD | NEW].
                        + pose proof (SH1 c g Hc ltac:(rewrite Elo in OLD; clear -Hg OLD; lia) NL') as BY.
                          destruct (SHR (region_beg SBEG c) lo g ltac:(clear -Hg OLD; lia) ltac:(clear -Q1 X14; lia) ltac:(clear -SL11; unfold KUSERMAP in SL11; lia)) as (QQ1 & QQ2 & QQ3).
                          eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]].
                        + assert (GR : lo / 8 <= g < lo / 8 + KUSERMAP / 8) by (clear -NEW Hg Elo SL1; unfold KUSERMAP in *; Z.div_mod_to_equations; lia).
                          destruct (existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st)) eqn:EXQ.
                          * exfalso. apply existsb_exists in EXQ. destruct EXQ as ([m0 n0] & Hq & Hmn). cbn [fst snd] in Hmn.
                            apply andb_true_iff in Hmn. destruct Hmn as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.ltb_lt in Hm2.
                            destruct (is_primary n0) eqn:HP.
                            -- pose proof (quar_chunk bt st Lc FF W m0 n0 Hq HP) as G'. cbn zeta in G'. destruct G' as (K1 & K2 & K3 & K4 & K5 & K6).
                               apply (uslot_vs_carved bt st Lc FF c _ _ W Hc (blk_class n0) (prim_alloc_beg (m0 + 16) n0) (8 * g) K1 K2); [| exact (USL g GR)].
                               clear -Hm1 Hm2 K4 K5 K6. Z.div_mod_to_equations. lia.
                            -- destruct (quar_sec bt st Lc FF W m0 n0 Hq HP) as (sc & Hsc & Eu & En). destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                               apply (uslot_not_supp bt st Lc FF c _ _ W Hc (8 * g)); [| exact (USL g GR)]. right. do 4 right. left. exists sc. split; [exact Hsc|].
                               rewrite Eu, En in *. clear -Hm1 Hm2 A3 A4 A5 A6. unfold PG in *. Z.div_mod_to_equations. lia.
                          * apply FSH. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). clear -GR. lia.
                      - pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                        destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                        eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. destruct (FLD c0) as (_ & _ & RFA & _). rewrite RFA in Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. destruct (FLD c0) as (RMU & _). rewrite RMU in Hg.
                      destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg))].
                      destruct (Z.lt_ge_cases g (lo / 8)) as [OLD | NEW]; [exact (def_keep Mmid M' _ DEF (SH5 c g Hc ltac:(rewrite Elo in OLD; clear -Hg OLD; lia)))|].
                      (* [comment removed for export] *)
                      apply (def_keep Mmid M' _ DEF). apply (proj1 P19). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI in G in change_no_check G' end). right.
                      clear -NEW Hg Elo SL1 SL10 SL11 B6. unfold KUSERMAP in *. Zlia. }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { destruct P13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (dyn_maps st') with (dyn_maps st). change (a_dep st') with (a_dep st).
             assert (COM : forall a, committed bt st' a <-> committed bt st a \/ lo <= a < lo + KUSERMAP).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_nres st') with (a_nres st). split.
               - intros [(c0 & Hc0 & X) | X]; [| left; right; exact X]. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA in X.
                 destruct (Z.eqb_spec c0 c) as [-> | NE]; [| left; left; exists c0; exact (conj Hc0 X)].
                 destruct X as [X | X]; [| left; left; exists c; split; [exact Hc | right; exact X]].
                 destruct (Z.lt_ge_cases a lo); [left; left; exists c; split; [exact Hc | left; rewrite Elo in *; clear -X H; lia] | right; rewrite Elo in *; clear -X H; unfold KUSERMAP in *; lia].
               - intros [[(c0 & Hc0 & X) | X] | X].
                 + left. exists c0. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA. split; [exact Hc0|].
                   destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact X]. destruct X as [X | X]; [left; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); clear -X; lia | right; exact X].
                 + right. exact X.
                 + left. exists c. destruct (FLD c) as (RMU & _). rewrite Z.eqb_refl in RMU. rewrite RMU. split; [exact Hc|]. left. rewrite Elo in X. clear -X Q8. lia. }
             assert (HOL1 : forall a, holes bt st' a -> holes bt st a).
             { intros a (c0 & Hc0 & X). exists c0. split; [exact Hc0|]. destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH). rewrite RMU, RFA, RUH, RFH in X.
               destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact X]. destruct X as [[F _] | X]; [discriminate F | right; exact X]. }
             assert (HOL2 : forall a, holes bt st a -> holes bt st' a \/ (r_uhole (a_reg st c) = true /\ lo <= a < lo + KUSERMAP)).
             { intros a (c0 & Hc0 & X). destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH).
               destruct (Z.eqb_spec c0 c) as [E | NE].
               - subst c0. destruct X as [[HU X] | X]; [right; split; [exact HU | rewrite Elo; exact X]|].
                 left. exists c. rewrite RMU, RFA, RUH, RFH. split; [exact Hc|]. right. exact X.
               - left. exists c0. rewrite RMU, RFA, RUH, RFH. exact (conj Hc0 X). }
             (* [comment removed for export] *)
             assert (SLOTH : forall a, lo <= a < lo + KUSERMAP -> holes bt st' a -> False).
             { intros a Ha (c0 & Hc0 & X). destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH). rewrite RMU, RFA, RUH, RFH in X.
               destruct (Z.eqb_spec c0 c) as [-> | NE].
               - destruct X as [[F _] | [_ X]]; [discriminate F|]. clear -Ha X SL4 Q6. unfold KUSERMAP in *. lia.
               - pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (PP1 & PP2 & PP3 & PP4 & PP5 & PP6 & PP7 & PP8 & _).
                 destruct (WR1 c0 Hc0) as (_ & _ & W3 & _). pose proof (FHO c0 Hc0) as FH0.
                 assert (XR : region_beg SBEG c0 <= a < region_beg SBEG c0 + KREGION).
                 { unfold fa_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP, KFAMAP in *. destruct X as [[_ X] | [HF X]]; [clear -X PP8 W3; lia | specialize (FH0 HF); clear -X PP6 FH0; lia]. }
                 rewrite Elo in Ha. unfold region_beg, KREGION, KREGION_EXHAUST, KUSERMAP in *.
                 destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
                 + assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (clear -LT; nia). clear -Ha XR HM Q8. lia.
                 + assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (clear -GT; nia). clear -Ha XR HM Y3 Q8. lia. }
             split. { destruct L1 as (F6 & PF & FOK & FPW & FH).
                      assert (WF6 : ivs_wf F6).
                      { intros q Hq. rewrite Forall_forall in FOK. destruct (FOK q Hq) as (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in G in change_no_check G' end).
                        clear -A1 A2 A3 SP3. ulia. }
                      destruct (r_uhole (a_reg st c)) eqn:HU.
                      - (* [comment removed for export] *)
                        assert (FREE : forall a, lo <= a < lo + KUSERMAP -> covered F6 a = false).
                        { intros a Ha. destruct (covered F6 a) eqn:CV; [| reflexivity]. exfalso.
                          apply (proj1 (FH a ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_resv6 in G in change_no_check G' end); clear -Ha SL6 SL7; lia)) ltac:(apply in_ivz_covered; exact CV)).
                          exists c. split; [exact Hc|]. left. split; [exact HU | rewrite <- Elo; exact Ha]. }
                        pose proof (frag_remapped bt ltac:(clear -SP3; ulia) F6 lo (Z_to_bv 64 lo) (Z_to_bv 64 KUSERMAP) FOK (seps_of_split F6 FPW) WF6
                                      ltac:(rewrite Elo; apply user_slot_aligned; exact Y2) SL6 SL7
                                      ltac:(rewrite u64_lit; [reflexivity | clear -SL8 SL9; unfold KUSERMAP in *; lia]) ltac:(rewrite u64_lit; [reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia]) FREE) as FRM.
                        cbn zeta in FRM. destruct FRM as (FOK' & FSP' & FWF' & FCV').
                        exists ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: F6).
                        split. { eapply Permutation_trans; [exact (VMP eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). apply Permutation_cons; [reflexivity | exact PF]. }
                        split; [exact FOK'|]. split; [exact (split_of_seps _ FSP')|].
                        intros a Ha. rewrite !in_ivz_covered, (FCV' a). rewrite <- in_ivz_covered. split.
                        + intros [X | X]; [| intros H'; exact (SLOTH a X H')]. intros H'. exact (proj1 (FH a Ha) X (HOL1 a H')).
                        + intros NH. destruct (decide (lo <= a < lo + KUSERMAP)) as [IN | NI]; [right; exact IN | left].
                          apply (proj2 (FH a Ha)). intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (NH H') | exact (NI X)].
                      - (* [comment removed for export] *)
                        exists F6. rewrite (VMK eq_refl). split; [exact PF|]. split; [exact FOK|]. split; [exact FPW|].
                        intros a Ha. rewrite (FH a Ha). split.
                        + intros NH H'. exact (NH (HOL1 a H')).
                        + intros NH Hh. destruct (HOL2 a Hh) as [H' | [F _]]; [exact (NH H') | discriminate F]. }
             split. { intros a. rewrite (NA a), (L2 a), (COM a). split.
                      - intros [(A & B & Cn) D]. split; [exact A|]. split; [intros [X|X]; [exact (B X) | exact (D X)]|]. intros H'. exact (Cn (HOL1 a H')).
                      - intros (A & B & Cn). assert (NS : ~ (lo <= a < lo + KUSERMAP)) by (intros X; apply B; right; exact X).
                        split; [| exact NS]. split; [exact A|]. split; [intros X; apply B; left; exact X|].
                        intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (Cn H') | exact (NS X)]. }
             split. { intros a. rewrite (LZ a), (L3 a), (COM a). split.
                      - intros [[(A & B & Cn) | S] D]; [left | right; exact S]. split; [exact A|]. split; [intros [X|X]; [exact (B X) | exact (D X)]|].
                        intros H'. exact (Cn (HOL1 a H')).
                      - intros [(A & B & Cn) | S].
                        + assert (NS : ~ (lo <= a < lo + KUSERMAP)) by (intros X; apply B; right; exact X).
                          split; [| exact NS]. left. split; [exact A|]. split; [intros X; apply B; left; exact X|].
                          intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (Cn H') | exact (NS X)].
                        + split; [right; exact S|]. destruct S as (b & Hb & Rb). intros X.
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st b Hb)) as D. hnf in D. cbn in D. clear -Rb X D SL6 SL7. unfold KUSERMAP in *. lia. }
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E5, E6. repeat (split; [assumption|]). exact NP'. }
    (* [comment removed for export] *)
    split. { destruct P14 as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & Bu6 & Bu7 & Bu8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)]). change (a_sec st') with (a_sec st).
             change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st + 0). change (a_nres st') with (a_nres st).
             assert (SHLO : sh_lo lo = sh_lo (region_beg SBEG c) + r_mapped_user (a_reg st c) / 8 /\ sh_lo lo mod PG = 0 /\ (KUSERMAP / 8) mod PG = 0 /\ 0 <= sh_lo lo /\ sh_lo lo + KUSERMAP / 8 <= 2 ^ 64
                            /\ (r_mapped_user (a_reg st c) + KUSERMAP) / 8 = r_mapped_user (a_reg st c) / 8 + KUSERMAP / 8).
             { (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Elo. clear -Y2 SL12 SL8 SL9 Elo. unfold KUSERMAP, PG, SB in *. Z.div_mod_to_equations. lia. }
             destruct SHLO as (SH1' & SH2' & SH3' & SH4' & SH5' & SH6').
             split. { unfold A_wf in *. apply Forall_app. split; [exact Bu1|]. apply Forall_cons; [| apply Forall_nil]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end).
                      clear -SH2' SH3' SH4'. unfold PG, KUSERMAP in *. Z.div_mod_to_equations. lia. }
             split; [exact MI|].
             split; [intros lo1 hi1 H; apply range_allowed_app; exact (Bu3 lo1 hi1 H)|].
             split; [intros p n H; apply range_allowed_app; exact (Bu4 p n H)|].
             split. { intros c0 Hc0. rewrite ER. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
                      - destruct (Bu5 c Hc) as [X Y]. (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_mapped_fa] in G in change_no_check G' end). split; [| apply range_allowed_app; exact Y].
                        rewrite SH6'. intros a Ha. destruct (Z.lt_ge_cases a (sh_lo lo)) as [LT | GE].
                        + apply (range_allowed_app _ _ _ _ X). clear -Ha LT SH1'. lia.
                        + apply (range_allowed_last (a_aa st) (sh_lo lo) (sh_lo lo + KUSERMAP / 8) SH2' ltac:(clear -SH2' SH3'; unfold PG in *; Z.div_mod_to_equations; lia) SH4' SH5').
                          clear -Ha GE SH1'. lia.
                      - destruct (Bu5 c0 Hc0) as [X Y]. split; apply range_allowed_app; assumption. }
             split; [intros s Hs; apply range_allowed_app; exact (Bu6 s Hs)|].
             split; [intros b Hb; apply range_allowed_app; exact (Bu7 b Hb)|].
             rewrite A_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes fst snd] in G in change_no_check G' end).
             change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st).
             assert (PC : prim_charge st' = prim_charge st + (KUSERMAP + KUSERMAP / 8)).
             { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end). rewrite (sum_classes_upd (fun c0 : Z => r_mapped_user (a_reg st c0) + r_mapped_user (a_reg st c0) / 8 + r_mapped_fa (a_reg st c0) + r_mapped_fa (a_reg st c0) / 8)
                                           (fun c0 : Z => r_mapped_user (a_reg st' c0) + r_mapped_user (a_reg st' c0) / 8 + r_mapped_fa (a_reg st' c0) + r_mapped_fa (a_reg st' c0) / 8)
                                           c (KUSERMAP + KUSERMAP / 8) 30).
               - destruct (Z.leb_spec c (Z.of_nat 30)); [reflexivity | exfalso; lia].
               - intros c0 NE. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA. destruct (Z.eqb_spec c0 c) as [E | _]; [exfalso; exact (NE E) | reflexivity].
               - destruct (FLD c) as (RMU & _ & RFA & _). rewrite Z.eqb_refl in RMU. rewrite RMU, RFA, SH6'. lia.
               - lia. }
             rewrite PC. destruct Bu8 as [Bu8 Bu9]. split; [clear -Bu8 EAG; lia|].
             (* [comment removed for export] *)
             intros s0 Hs0. apply in_app_iff. left. exact (Bu9 s0 Hs0). }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [V1 V2]. split; [frW DEF V1 | frW DEF V2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; exact (IMGR i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia))))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; exact (IMGR i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia))))] |].
    exact (rep_last_keep bt _ _ Mmid M' DEF P19 (fun H => H)).
  Qed.

  Theorem OPS_REP_usermap_pf : OPS_REP_usermap bt.
  Proof using. intros st Lc FF M M' mdl mdl' c W. exact (OPS_REP_usermap_h_pf st Lc FF M M' mdl mdl' c (fa_holes_ok_of_WF st Lc FF W) W). Qed.
End Usermap.
