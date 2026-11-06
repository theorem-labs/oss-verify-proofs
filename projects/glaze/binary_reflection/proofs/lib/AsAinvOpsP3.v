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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition op_famap (st : ast) (c : Z) : ast :=
  let r := a_reg st c in set_reg st c (REG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r + KFAMAP) (r_free r) (r_uhole r) false).

Definition carve_n (r : region) (c : Z) : Z := (r_mapped_user r - r_alloc_user r) / csize c.
Definition op_carve (spacebeg : Z) (st : ast) (c : Z) : ast :=
  let r := a_reg st c in let newn := carve_n r c in
  set_reg st c (REG (r_mapped_user r) (r_alloc_user r + newn * csize c) (r_mapped_fa r)
                    (r_free r ++ carve_list spacebeg c (r_alloc_user r / csize c) newn) (r_uhole r) (r_fhole r)).

Lemma famap_fields : forall st c c',
  r_mapped_user (a_reg (op_famap st c) c') = r_mapped_user (a_reg st c')
  /\ r_alloc_user (a_reg (op_famap st c) c') = r_alloc_user (a_reg st c')
  /\ r_mapped_fa (a_reg (op_famap st c) c') = (if Z.eqb c' c then r_mapped_fa (a_reg st c') + KFAMAP else r_mapped_fa (a_reg st c'))
  /\ r_free (a_reg (op_famap st c) c') = r_free (a_reg st c')
  /\ r_uhole (a_reg (op_famap st c) c') = r_uhole (a_reg st c')
  /\ r_fhole (a_reg (op_famap st c) c') = (if Z.eqb c' c then false else r_fhole (a_reg st c')).
Proof.
  intros st c c'. (lazymatch goal with |- ?G => let G' := eval unfold op_famap, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity.
Qed.

Lemma carve_fields : forall spacebeg st c c',
  let r := a_reg st c' in
  r_mapped_user (a_reg (op_carve spacebeg st c) c') = r_mapped_user r
  /\ r_alloc_user (a_reg (op_carve spacebeg st c) c') = (if Z.eqb c' c then r_alloc_user r + carve_n r c * csize c else r_alloc_user r)
  /\ r_mapped_fa (a_reg (op_carve spacebeg st c) c') = r_mapped_fa r
  /\ r_free (a_reg (op_carve spacebeg st c) c') = (if Z.eqb c' c then r_free r ++ carve_list spacebeg c (r_alloc_user r / csize c) (carve_n r c) else r_free r)
  /\ r_uhole (a_reg (op_carve spacebeg st c) c') = r_uhole r
  /\ r_fhole (a_reg (op_carve spacebeg st c) c') = r_fhole r.
Proof.
  intros spacebeg st c c'. cbn zeta. (lazymatch goal with |- ?G => let G' := eval unfold op_carve, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma famap_rest : forall st c,
  a_cinit (op_famap st c) = a_cinit st /\ a_cache (op_famap st c) = a_cache st /\ a_tq (op_famap st c) = a_tq st /\ a_gq (op_famap st c) = a_gq st
  /\ a_sec (op_famap st c) = a_sec st /\ a_nres (op_famap st c) = a_nres st /\ a_dep (op_famap st c) = a_dep st /\ a_hint (op_famap st c) = a_hint st
  /\ a_ialloc (op_famap st c) = a_ialloc st /\ a_aa (op_famap st c) = a_aa st /\ a_kact (op_famap st c) = a_kact st /\ a_shsec (op_famap st c) = a_shsec st.
Proof. intros st c. repeat split; reflexivity. Qed.
Lemma carve_rest : forall spacebeg st c,
  a_cinit (op_carve spacebeg st c) = a_cinit st /\ a_cache (op_carve spacebeg st c) = a_cache st /\ a_tq (op_carve spacebeg st c) = a_tq st
  /\ a_gq (op_carve spacebeg st c) = a_gq st /\ a_sec (op_carve spacebeg st c) = a_sec st /\ a_nres (op_carve spacebeg st c) = a_nres st
  /\ a_dep (op_carve spacebeg st c) = a_dep st /\ a_hint (op_carve spacebeg st c) = a_hint st /\ a_ialloc (op_carve spacebeg st c) = a_ialloc st
  /\ a_aa (op_carve spacebeg st c) = a_aa st /\ a_kact (op_carve spacebeg st c) = a_kact st /\ a_shsec (op_carve spacebeg st c) = a_shsec st.
Proof. intros spacebeg st c. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Lemma carved_famap : forall st c c0 a, carved bt (op_famap st c) c0 a <-> carved bt st c0 a.
  Proof using. intros st c c0 a. (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end). destruct (famap_fields st c c0) as (_ & RAU & _). rewrite RAU. am_tauto. Qed.

  Lemma in_fa_c_famap : forall st c c0 a, in_fa_c bt (op_famap st c) c0 a <-> in_fa_c bt st c0 a.
  Proof using. intros st c c0 a. (lazymatch goal with |- ?G => let G' := eval unfold in_fa_c in G in change_no_check G' end). destruct (famap_fields st c c0) as (_ & _ & _ & RFR & _). rewrite RFR. am_tauto. Qed.




  (* [comment removed for export] *)
  Definition OPS_WF_famap : Prop := forall st Lc FF c,
    WF bt st Lc FF -> 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) ->
    WF bt (op_famap st c) Lc FF.

  Theorem OPS_WFq_famap_pf : forall st Lc FF c {qt qg : Z},
    WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) ->
    WFq bt (op_famap st c) Lc FF qt qg.
  Proof using.
    intros st Lc FF c qt qg W Hc ROOM FAQ.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    assert (CVE : forall c0 a, carved bt (op_famap st c) c0 a <-> carved bt st c0 a) by (intros; apply carved_famap).
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split. { split.
             - intros c0 Hc0. destruct (WR1 c0 Hc0) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
               destruct (famap_fields st c c0) as (RMU & RAU & RFA & RFR & RUH & RFH). (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). cbn zeta. rewrite RMU, RAU, RFA, RFR, RFH.
               split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
               split. { destruct (Z.eqb_spec c0 c) as [-> | NE]; [unfold KFAMAP in *; lia | exact Y5]. }
               split. { destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact Y6].
                        replace (r_mapped_fa (a_reg st c) + KFAMAP) with (r_mapped_fa (a_reg st c) + 1 * KFAMAP) by lia. rewrite Z.mod_add; [exact Y6 | (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia]. }
               split. { destruct (Z.eqb_spec c0 c) as [-> | NE]; [unfold KFAMAP in *; lia | exact Y7]. }
               split. { destruct (Z.eqb_spec c0 c) as [-> | NE]; [exact ROOM | exact Y8]. }
               split. { intros k Hk. destruct (Y9 k Hk) as [Kr CV]. split; [exact Kr | apply CVE; exact CV]. }
               split.
               + (* [comment removed for export] *)
                 destruct PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). (lazymatch goal with |- ?G => let G' := eval unfold partition_c in G in change_no_check G' end).
                 assert (EF : forall a, in_fa_c bt (op_famap st c) c0 a <-> in_fa_c bt st c0 a) by (intros; apply in_fa_c_famap).
                 change (a_cache (op_famap st c) c0) with (a_cache st c0).
                 change (in_cache_c bt (op_famap st c) c0) with (in_cache_c bt st c0). change (in_quar_c (op_famap st c) c0) with (in_quar_c st c0).
                 change (in_batch (op_famap st c)) with (in_batch st). change (in_live_c Lc c0) with (in_live_c Lc c0).
                 rewrite RFR.
                 split. { intros a. rewrite CVE, EF. exact (P1 a). }
                 split; [exact P2|]. split; [exact P3|]. split; [intros a [A B]; apply (P4 a); split; [exact A | apply EF; exact B]|].
                 split; [exact P5|]. split; [intros a [A B]; apply (P6 a); split; [exact A | apply EF; exact B]|].
                 split; [intros a [A B]; apply (P7 a); split; [exact A | apply EF; exact B]|].
                 split; [| exact (conj P9 P10)].
                 intros a HB EC [X|[X|[X|X]]]; apply (P8 a HB EC); [left; exact X | right; left; exact X | right; right; left; exact X | right; right; right; apply EF; exact X].
               + destruct (Z.eqb_spec c0 c) as [-> | NE]; [intros F; discriminate F | exact FHK].
             - intros c0 NC. destruct (WR2 c0 NC) as [E1 E2]. (lazymatch goal with |- ?G => let G' := eval unfold op_famap, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
               destruct (Z.eqb_spec c0 c) as [-> | NE]; [exfalso; exact (NC Hc) | exact (conj E1 E2)]. }
    split. { intros c0 Hc0. destruct (WC c0 Hc0) as (C1 & C2 & C3). change (a_cache (op_famap st c) c0) with (a_cache st c0). change (a_cinit (op_famap st c)) with (a_cinit st).
             split; [exact C1|]. split; [intros F; destruct (C2 F) as [F1 F2]; split; [exact F1|]; (lazymatch goal with |- ?G => let G' := eval unfold op_famap, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE0]; (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); exact F2|]. intros k Hk. destruct (C3 k Hk) as [Kr CV]. split; [exact Kr | apply CVE; exact CV]. }
    split. { destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq (op_famap st c)) with (a_tq st). change (a_gq (op_famap st c)) with (a_gq st). change (quar (op_famap st c)) with (quar st).
             assert (WB : forall b, wf_batch bt st b -> wf_batch bt (op_famap st c) b).
             { intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply CVE; exact B2|]. intros m n Hmn.
               destruct (B3 m n Hmn) as [N [[HP CV]|[HP RG]]]; (split; [exact N|]); [left; split; [exact HP | apply CVE; exact CV] | right; split; [exact HP | exact RG]]. }
             split; [rewrite Forall_forall in Q1 |- *; intros b Hb; apply WB; exact (Q1 b Hb)|].
             split; [rewrite Forall_forall in Q2 |- *; intros b Hb; apply (wf_batch0_mono bt st); [intros c0 a0; apply CVE | intros p0 n0 H0; exact H0 | exact (Q2 b Hb)]|].
             exact (conj Q3 (conj Q4 (conj Q5 Q6))). }
    split; [exact WS|].
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| exact (conj LV2 LV3)]. intros p n Hin. destruct (LV1 p n Hin) as (A1 & A2 & A3 & CVL).
             split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros HP. apply CVE. exact (CVL HP). }
    split; [exact WK|]. split; [exact WD|].
    split. { (* [comment removed for export] *)
             destruct WM as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end).
             change (a_kact (op_famap st c)) with (a_kact st). change (a_shsec (op_famap st c)) with (a_shsec st). change (a_sec (op_famap st c)) with (a_sec st).
             rewrite (sum_mu_ext st (op_famap st c)) by (intros c1 Hc1; exact (proj1 (famap_fields st c c1))).
             split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
             intros c1 Hc1. destruct (famap_fields st c c1) as (RMU1 & _ & RFA1 & _). rewrite RMU1, RFA1.
             destruct (Z.eqb_spec c1 c) as [-> | NE]; [clear -FAQ; lia | exact (M5 c1 Hc1)]. }
    split; [exact WMP|]. exact G.
  Qed.

  Theorem OPS_WF_famap_pf : OPS_WF_famap.
  Proof using. intros st Lc FF c W Hc ROOM FAQ. exact (OPS_WFq_famap_pf st Lc FF c W Hc ROOM FAQ). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma chunk_roundtrip : forall c j, 1 <= c <= 30 -> chunk_of_compact SBEG c (compact_of SBEG c (chunk_addr SBEG c j)) = chunk_addr SBEG c j.
  Proof using.
    intros c j Hc. pose proof (csize_pos c Hc) as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold chunk_of_compact, compact_of, chunk_addr in G in change_no_check G' end).
    replace (region_beg SBEG c + j * csize c - region_beg SBEG c) with (j * csize c) by lia.
    assert (E : csize c = 16 * (csize c / 16)) by (apply Z.div_exact; lia). set (q := csize c / 16) in *.
    rewrite E. replace (j * (16 * q)) with ((j * q) * 16) by lia. rewrite Z.div_mul by lia. lia.
  Qed.
  Lemma chunk_addr_inj : forall c j j', 1 <= c <= 30 -> chunk_addr SBEG c j = chunk_addr SBEG c j' -> j = j'.
  Proof using. intros c j j' Hc E. pose proof (csize_pos c Hc) as [S1 S2]. unfold chunk_addr in E. nia. Qed.

  Lemma in_carve_list : forall c j0 newn k, 0 <= newn ->
    In k (carve_list SBEG c j0 newn) <-> exists t, 0 <= t < newn /\ k = compact_of SBEG c (chunk_addr SBEG c (j0 + t)).
  Proof using.
    intros c j0 newn k Hn. (lazymatch goal with |- ?G => let G' := eval unfold carve_list in G in change_no_check G' end). rewrite in_map_iff. split.
    - intros (i & Ek & Hi). apply in_seq in Hi. exists (newn - 1 - Z.of_nat i). split; [lia | symmetry; exact Ek].
    - intros (t & Ht & Ek). exists (Z.to_nat (newn - 1 - t)). split; [rewrite Z2Nat.id by lia; replace (newn - 1 - (newn - 1 - t)) with t by lia; symmetry; exact Ek | apply in_seq; lia].
  Qed.
  Lemma carve_list_length : forall c j0 newn, 0 <= newn -> Z.of_nat (length (carve_list SBEG c j0 newn)) = newn.
  Proof using. intros c j0 newn Hn. (lazymatch goal with |- ?G => let G' := eval unfold carve_list in G in change_no_check G' end). rewrite length_map, length_seq. lia. Qed.
  Lemma carve_list_NoDup : forall c j0 newn, 1 <= c <= 30 -> List.NoDup (carve_list SBEG c j0 newn).
  Proof using.
    intros c j0 newn Hc. (lazymatch goal with |- ?G => let G' := eval unfold carve_list in G in change_no_check G' end). apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros i i' Hi Hi' E. apply (f_equal (chunk_of_compact SBEG c)) in E. rewrite !chunk_roundtrip in E by exact Hc.
    apply chunk_addr_inj in E; [lia | exact Hc].
  Qed.

  Definition OPS_WF_carve : Prop := forall st Lc FF c,
    WF bt st Lc FF -> 1 <= c <= 30 -> a_cinit st = true ->        (* [comment removed for export] *)
    r_alloc_user (a_reg st c) + carve_n (a_reg st c) c * csize c <= AMAX ->      (* [comment removed for export] *)
    4 * (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c) <= r_mapped_fa (a_reg st c) ->
    WF bt (op_carve SBEG st c) Lc FF.

  Theorem OPS_WFq_carve_pf : forall st Lc FF c {qt qg : Z},
    WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> a_cinit st = true ->
    r_alloc_user (a_reg st c) + carve_n (a_reg st c) c * csize c <= AMAX ->
    4 * (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c) <= r_mapped_fa (a_reg st c) ->
    WFq bt (op_carve SBEG st c) Lc FF qt qg.
  Proof using.
    intros st Lc FF c qt qg W Hc HCINIT HROOM ROOM.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    pose proof (csize_pos c Hc) as [S1 S2].
    set (r := a_reg st c) in *. set (cs := csize c) in *. set (N := carve_n r c) in *. set (j0 := r_alloc_user r / cs).
    assert (EJ : r_alloc_user r = j0 * cs) by ((lazymatch goal with |- ?G => let G' := eval unfold j0 in G in change_no_check G' end); rewrite Z.mul_comm; apply Z.div_exact; lia).
    assert (HN : 0 <= N /\ N * cs <= r_mapped_user r - r_alloc_user r).
    { (lazymatch goal with |- ?G => let G' := eval unfold N, carve_n in G in change_no_check G' end). fold cs. split; [apply Z.div_pos; lia | rewrite Z.mul_comm; apply Z.mul_div_le; lia]. }
    destruct HN as [N0 N1].
    set (NEW := fun a => exists t, 0 <= t < N /\ a = chunk_addr SBEG c (j0 + t)).
    (* [comment removed for export] *)
    assert (CVc : forall a, carved bt (op_carve SBEG st c) c a <-> carved bt st c a \/ NEW a).
    { intros a. (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end). destruct (carve_fields SBEG st c c) as (_ & RAU & _). rewrite RAU, Z.eqb_refl. fold r. fold N. fold cs. (lazymatch goal with |- ?G => let G' := eval unfold NEW in G in change_no_check G' end). split.
      - intros (j & Hj & Hle & Ea). destruct (Z.lt_ge_cases j j0) as [LT|GE].
        + left. exists j. split; [exact Hj|]. split; [nia | exact Ea].
        + right. exists (j - j0). split; [nia | replace (j0 + (j - j0)) with j by lia; exact Ea].
      - intros [(j & Hj & Hle & Ea) | (t & Ht & Ea)].
        + exists j. split; [exact Hj|]. split; [nia | exact Ea].
        + exists (j0 + t). assert (0 <= j0) by ((lazymatch goal with |- ?G => let G' := eval unfold j0 in G in change_no_check G' end); apply Z.div_pos; lia). split; [lia|]. split; [nia | exact Ea]. }
    assert (CVo : forall c0 a, c0 <> c -> (carved bt (op_carve SBEG st c) c0 a <-> carved bt st c0 a)).
    { intros c0 a NE. (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end). destruct (carve_fields SBEG st c c0) as (_ & RAU & _). rewrite RAU. destruct (Z.eqb_spec c0 c) as [E|_]; [exfalso; exact (NE E)|]. am_tauto. }
    assert (CVM : forall c0 a, carved bt st c0 a -> carved bt (op_carve SBEG st c) c0 a).
    { intros c0 a CV. destruct (Z.eq_dec c0 c) as [-> | NE]; [apply CVc; left; exact CV | apply (CVo c0 a NE); exact CV]. }
    assert (NEWnot : forall a, NEW a -> ~ carved bt st c a).
    { intros a (t & Ht & Ea) (j & Hj & Hle & Ea'). rewrite Ea in Ea'. apply chunk_addr_inj in Ea'; [| exact Hc]. subst j. fold r in Hle. fold cs in Hle. clear -Hle Ht EJ N1 S1 Y1. nia. }
    assert (FAc : forall a, in_fa_c bt (op_carve SBEG st c) c a <-> in_fa_c bt st c a \/ NEW a).
    { intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_fa_c in G in change_no_check G' end). destruct (carve_fields SBEG st c c) as (_ & _ & _ & RFR & _). rewrite RFR, Z.eqb_refl. fold r. fold cs. fold N. fold j0. split.
      - intros (k & Hk & Ea). apply in_app_iff in Hk. destruct Hk as [Hk|Hk]; [left; exists k; exact (conj Hk Ea)|].
        right. apply in_carve_list in Hk; [| exact N0]. destruct Hk as (t & Ht & Ek). exists t. split; [exact Ht|]. rewrite Ea, Ek. apply chunk_roundtrip. exact Hc.
      - intros [(k & Hk & Ea) | (t & Ht & Ea)]; [exists k; split; [apply in_app_iff; left; exact Hk | exact Ea]|].
        exists (compact_of SBEG c a). split; [apply in_app_iff; right; apply in_carve_list; [exact N0 | exists t; split; [exact Ht | rewrite Ea; reflexivity]]|].
        rewrite Ea. symmetry. apply chunk_roundtrip. exact Hc. }
    assert (FAo : forall c0 a, c0 <> c -> (in_fa_c bt (op_carve SBEG st c) c0 a <-> in_fa_c bt st c0 a)).
    { intros c0 a NE. (lazymatch goal with |- ?G => let G' := eval unfold in_fa_c in G in change_no_check G' end). destruct (carve_fields SBEG st c c0) as (_ & _ & _ & RFR & _). rewrite RFR. destruct (Z.eqb_spec c0 c) as [E|_]; [exfalso; exact (NE E)|]. am_tauto. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split. { split.
             - intros c0 Hc0. destruct (WR1 c0 Hc0) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & PART0 & FHK0).
               destruct (carve_fields SBEG st c c0) as (RMU & RAU & RFA & RFR & RUH & RFH). (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). cbn zeta. rewrite RMU, RAU, RFA, RFR, RFH.
               change (in_cache_c bt (op_carve SBEG st c) c0) with (in_cache_c bt st c0). change (in_quar_c (op_carve SBEG st c) c0) with (in_quar_c st c0).
               change (in_batch (op_carve SBEG st c)) with (in_batch st). change (a_cache (op_carve SBEG st c) c0) with (a_cache st c0).
               destruct (Z.eqb_spec c0 c) as [-> | NE].
               + fold r. fold cs. fold N. fold j0.
                 split. { split; [lia|]. split; [| fold r cs N in HROOM; exact HROOM]. left. pose proof (Z.div_mod (r_mapped_user r - r_alloc_user r) cs ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (r_mapped_user r - r_alloc_user r) cs ltac:(lia)) as MB.
                          assert (EN : N = (r_mapped_user r - r_alloc_user r) / cs) by reflexivity. rewrite <- EN in DM. clear -DM MB. lia. }
                 split; [exact Y2|]. split; [exact Y3|].
                 split. { rewrite EJ. replace (j0 * cs + N * cs) with ((j0 + N) * cs) by lia. apply Z_mod_mult. }
                 split; [exact Y5|]. split; [exact Y6|].
                 split. { rewrite length_app, Nat2Z.inj_add, carve_list_length by exact N0. lia. }
                 split; [exact Y8|].
                 split. { intros k Hk. apply in_app_iff in Hk. destruct Hk as [Hk|Hk].
                          - destruct (Y9 k Hk) as [Kr CV]. split; [exact Kr | apply CVM; exact CV].
                          - apply in_carve_list in Hk; [| exact N0]. destruct Hk as (t & Ht & Ek). split.
                            + rewrite Ek. (lazymatch goal with |- ?G => let G' := eval unfold compact_of, chunk_addr in G in change_no_check G' end). fold cs.
                              replace (region_beg SBEG c + (j0 + t) * cs - region_beg SBEG c) with ((j0 + t) * cs) by lia.
                              assert (J0 : 0 <= j0) by ((lazymatch goal with |- ?G => let G' := eval unfold j0 in G in change_no_check G' end); apply Z.div_pos; lia).
                              assert (UB : (j0 + t) * cs + cs <= r_mapped_user r) by (clear -Ht N1 EJ J0 S1 Y1; nia). unfold KREGION_EXHAUST, KUSERMAP in Y3.
                              clear -J0 Ht UB S1 Y3. split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; [lia | nia]].
                            + apply CVc. right. exists t. split; [exact Ht|]. rewrite Ek. apply chunk_roundtrip. exact Hc. }
                 split.
                 * destruct PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). (lazymatch goal with |- ?G => let G' := eval unfold partition_c in G in change_no_check G' end).
                   assert (OLD : forall a, in_live_c Lc c a \/ in_quar_c st c a \/ in_cache_c bt st c a \/ in_fa_c bt st c a \/ (c = BATCHCLASS /\ in_batch st a) -> ~ NEW a).
                   { intros a Ha Hn. exact (NEWnot a Hn (proj2 (P1 a) Ha)). }
                   split. { intros a. rewrite CVc, FAc. rewrite (P1 a). am_tauto. }
                   split; [exact P2|]. split; [exact P3|].
                   split. { intros a [A B]. apply FAc in B. destruct B as [B|B]; [exact (P4 a (conj A B)) | exact (OLD a (or_introl A) B)]. }
                   split; [exact P5|].
                   split. { intros a [A B]. apply FAc in B. destruct B as [B|B]; [exact (P6 a (conj A B)) | exact (OLD a (or_intror (or_introl A)) B)]. }
                   split. { intros a [A B]. apply FAc in B. destruct B as [B|B]; [exact (P7 a (conj A B)) | exact (OLD a (or_intror (or_intror (or_introl A))) B)]. }
                   split. { intros a HB EC X. apply (P8 a HB EC). destruct X as [X|[X|[X|X]]]; [am_tauto | am_tauto | am_tauto |].
                            apply FAc in X. destruct X as [X|X]; [am_tauto|]. exfalso. apply (OLD a); [do 4 right; exact (conj EC HB) | exact X]. }
                   split; [exact P9|]. rewrite RFR. try rewrite Z.eqb_refl. (lazymatch goal with |- ?G => let G' := eval cbn [negb andb orb] in G in change_no_check G' end). fold r. fold cs. fold N. fold j0.
                   apply NoDup_app; [exact P10 | apply carve_list_NoDup; exact Hc |].
                   intros k Hk Hk2. apply in_carve_list in Hk2; [| exact N0]. destruct Hk2 as (t & Ht & Ek).
                   apply (OLD (chunk_of_compact SBEG c k)); [do 3 right; left; exists k; split; [exact Hk | reflexivity] |].
                   exists t. split; [exact Ht|]. rewrite Ek. apply chunk_roundtrip. exact Hc.
                 * exact FHK.
               + split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|].
                 split. { intros k Hk. destruct (W9 k Hk) as [Kr CV]. split; [exact Kr | apply CVM; exact CV]. }
                 split; [| exact FHK0].
                 destruct PART0 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). (lazymatch goal with |- ?G => let G' := eval unfold partition_c in G in change_no_check G' end).
                 assert (EF : forall a, in_fa_c bt (op_carve SBEG st c) c0 a <-> in_fa_c bt st c0 a) by (intros a; exact (FAo c0 a NE)).
                 rewrite RFR.
                 split. { intros a. rewrite (CVo c0 a NE), EF. exact (P1 a). }
                 split; [exact P2|]. split; [exact P3|]. split; [intros a [A B]; apply (P4 a); split; [exact A | apply EF; exact B]|].
                 split; [exact P5|]. split; [intros a [A B]; apply (P6 a); split; [exact A | apply EF; exact B]|].
                 split; [intros a [A B]; apply (P7 a); split; [exact A | apply EF; exact B]|].
                 split; [| exact (conj P9 P10)].
                 intros a HB EC [X|[X|[X|X]]]; apply (P8 a HB EC); [left; exact X | right; left; exact X | right; right; left; exact X | right; right; right; apply EF; exact X].
             - intros c0 NC. destruct (WR2 c0 NC) as [E1 E2]. (lazymatch goal with |- ?G => let G' := eval unfold op_carve, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
               destruct (Z.eqb_spec c0 c) as [-> | NE]; [exfalso; exact (NC Hc) | exact (conj E1 E2)]. }
    split. { intros c0 Hc0. destruct (WC c0 Hc0) as (C1 & C2 & C3). change (a_cache (op_carve SBEG st c) c0) with (a_cache st c0). change (a_cinit (op_carve SBEG st c)) with (a_cinit st).
             split; [exact C1|]. split; [intros F; rewrite HCINIT in F; discriminate F|]. intros k Hk. destruct (C3 k Hk) as [Kr CV]. split; [exact Kr | apply CVM; exact CV]. }
    split. { destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq (op_carve SBEG st c)) with (a_tq st). change (a_gq (op_carve SBEG st c)) with (a_gq st). change (quar (op_carve SBEG st c)) with (quar st).
             assert (WB : forall b, wf_batch bt st b -> wf_batch bt (op_carve SBEG st c) b).
             { intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply CVM; exact B2|]. intros m n Hmn.
               destruct (B3 m n Hmn) as [Nn [[HP CV]|[HP RG]]]; (split; [exact Nn|]); [left; split; [exact HP | apply CVM; exact CV] | right; split; [exact HP | exact RG]]. }
             split; [rewrite Forall_forall in Q1 |- *; intros b Hb; apply WB; exact (Q1 b Hb)|].
             split; [rewrite Forall_forall in Q2 |- *; intros b Hb; apply (wf_batch0_mono bt st); [intros c0 a0; apply CVM | intros p0 n0 H0; exact H0 | exact (Q2 b Hb)]|].
             exact (conj Q3 (conj Q4 (conj Q5 Q6))). }
    split; [exact WS|].
    split. { (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| exact (conj LV2 LV3)]. intros p n Hin. destruct (LV1 p n Hin) as (A1 & A2 & A3 & CVL).
             split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros HP. apply CVM. exact (CVL HP). }
    split; [exact WK|]. split; [exact WD|].
    split. { (* [comment removed for export] *)
             apply (wf_meter_transfer st (op_carve SBEG st c) eq_refl eq_refl eq_refl); [| exact WM].
             intros c1 Hc1. pose proof (carve_fields SBEG st c c1) as (RMU1 & _ & RFA1 & _). exact (conj RMU1 RFA1). }
    split; [exact WMP|]. exact G.
  Qed.

  Theorem OPS_WF_carve_pf : OPS_WF_carve.
  Proof using. intros st Lc FF c W Hc HCI HR ROOM. exact (OPS_WFq_carve_pf st Lc FF c W Hc HCI HR ROOM). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation T := (bt_thread bt).

  Definition foot_famap (st : ast) (c : Z) (a : Z) : Prop :=
    (reginfo bt c + 24 <= a < reginfo bt c + 32) \/ (reginfo bt c + 72 <= a < reginfo bt c + 128)
    \/ (sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) <= a < sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) + KFAMAP / 8)
    \/ fslot bt st c a
    \/ (T + 2768 <= a < T + T_UNW) \/ CEIL <= a.

  Definition OPS_REP_famap : Prop := forall st Lc FF M M' mdl mdl' c,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    agrees_off (foot_famap st c) M M' ->
    cellZ SG M' (reginfo bt c + 24) 8 (r_mapped_fa (a_reg st c) + KFAMAP) ->
    writableZ SG M' (reginfo bt c) (reginfo bt c + 128) ->
    writableZ SG M' lo (lo + KFAMAP) ->
    fillZ SG M' (sh_lo lo) (sh_lo lo + KFAMAP / 8) FA ->
    (r_fhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl)) ->
    (r_fhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: vm_maps (m_vmmaps mdl))) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KFAMAP)) ->
    (* [comment removed for export] *)
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KFAMAP)) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) -> vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    MInv (a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)]) mdl' -> eager_used mdl' <= eager_used mdl + KFAMAP ->
    Rep bt (add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0) Lc FF M' mdl'.

  (* [comment removed for export] *)
  Definition foot_carve (st : ast) (c : Z) (a : Z) : Prop :=
    let r := a_reg st c in let len := Z.of_nat (length (r_free r)) in
    (fa_beg SBEG c + 4 * len <= a < fa_beg SBEG c + 4 * (len + carve_n r c))
    \/ (reginfo bt c + 16 <= a < reginfo bt c + 24) \/ (reginfo bt c + 32 <= a < reginfo bt c + 40) \/ a = reginfo bt c + 68
    \/ (reginfo bt c + 72 <= a < reginfo bt c + 128)
    \/ (T + 2768 <= a < T + T_UNW) \/ CEIL <= a.

  Definition OPS_REP_carve : Prop := forall st Lc FF M M' mdl mdl' c,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 ->
    let r := a_reg st c in let len := Z.of_nat (length (r_free r)) in let newn := carve_n r c in
    4 * (len + newn) <= r_mapped_fa r ->
    agrees_off (foot_carve st c) M M' ->
    (forall i k, nth_error (carve_list SBEG c (r_alloc_user r / csize c) newn) i = Some k ->
       cellZ SG M' (fa_beg SBEG c + 4 * (len + Z.of_nat i)) 4 k) ->
    cellZ SG M' (reginfo bt c + 16) 8 (len + newn) ->
    cellZ SG M' (reginfo bt c + 32) 8 (r_alloc_user r + newn * csize c) ->
    byteZ SG M' (reginfo bt c + 68) 0 ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_carve SBEG st c) Lc FF M' mdl'.
End P.
