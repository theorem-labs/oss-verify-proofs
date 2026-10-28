(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutSM CmpCutSmA BzCFactsSmA BzCFactsSmA2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm BzCSmF1 BzCSmF2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSd2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSmB BzCFactsSmB2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.BzCFactsHm2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCHuffF7 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSd2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB2.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sm_len_init_spec : forall n len A t0, 0 <= A <= 258 -> 0 <= t0 ->
  (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A ->
     zget (sm_len_init n len A t0) (258 * t + v) = BZ_GREATER_ICOST /\ zdef (sm_len_init n len A t0) (258 * t + v) = true) /\
  (forall x, (x < 258 * t0 \/ 258 * (t0 + Z.of_nat n) <= x) ->
     zget (sm_len_init n len A t0) x = zget len x /\ zdef (sm_len_init n len A t0) x = zdef len x).
Proof.
  induction n as [|n IH]; intros len A t0 HA Ht0.
  - cbn [sm_len_init]. split; [intros; lia| intros; split; reflexivity].
  - rewrite sm_len_init_S.
    destruct (IH (sm_len_init_row (Z.to_nat A) len t0 0) A (t0 + 1) HA ltac:(lia)) as [V F]. split.
    + intros t v Ht Hv. destruct (Z.eq_dec t t0) as [->|NE].
      * destruct (F (258 * t0 + v) ltac:(lia)) as [F1 F2]. rewrite F1, F2, sm_len_init_row_get, sm_len_init_row_def.
        replace ((258 * t0 + 0 <=? 258 * t0 + v) && (258 * t0 + v <? 258 * t0 + 0 + Z.of_nat (Z.to_nat A)))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        split; reflexivity.
      * apply V; lia.
    + intros x Hx. destruct (F x ltac:(lia)) as [F1 F2]. rewrite F1, F2, sm_len_init_row_get, sm_len_init_row_def.
      destruct (Z.leb_spec (258 * t0 + 0) x), (Z.ltb_spec x (258 * t0 + 0 + Z.of_nat (Z.to_nat A))); cbn [andb orb]; try (split; reflexivity).
      exfalso. lia.
Qed.

(* [comment removed for export] *)
Definition LPV (len : zarr) (v j : Z) : Z := Z.lor (Z.shiftl (zget len (258 * (2 * j + 1) + v)) 16) (zget len (258 * (2 * j) + v)).
Lemma sm_lenpack_spec : forall n lp len v0, 0 <= v0 ->
  (forall v j, v0 <= v < v0 + Z.of_nat n -> 0 <= j < 3 ->
     zdef (sm_lenpack n lp len v0) (4 * v + j) = true /\ zget (sm_lenpack n lp len v0) (4 * v + j) = LPV len v j) /\
  (forall x, (forall v j, v0 <= v < v0 + Z.of_nat n -> 0 <= j < 3 -> x <> 4 * v + j) ->
     zget (sm_lenpack n lp len v0) x = zget lp x /\ zdef (sm_lenpack n lp len v0) x = zdef lp x).
Proof.
  induction n as [|n IH]; intros lp len v0 Hv0.
  - cbn [sm_lenpack]. split; [intros; lia| intros; split; reflexivity].
  - rewrite sm_lenpack_S.
    set (lp' := zset (zset (zset lp (4 * v0) _) (4 * v0 + 1) _) (4 * v0 + 2) _).
    destruct (IH lp' len (v0 + 1) ltac:(lia)) as [V F]. split.
    + intros v j Hv Hj. destruct (Z.eq_dec v v0) as [->|NE].
      * destruct (F (4 * v0 + j)) as [F1 F2]. { intros v' j' Hv' Hj'. lia. }
        rewrite F1, F2. subst lp'. unfold LPV. rewrite !zget_zset, !zdef_zset.
        assert (j = 0 \/ j = 1 \/ j = 2) as [->|[->| ->]] by lia.
        -- replace (4 * v0 + 0 =? 4 * v0 + 2) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (4 * v0 + 0 =? 4 * v0 + 1) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (4 * v0 + 0 =? 4 * v0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [orb].
           split; [reflexivity|]. replace (258 * (2 * 0 + 1) + v0) with (258 * 1 + v0) by lia. replace (258 * (2 * 0) + v0) with (258 * 0 + v0) by lia. reflexivity.
        -- replace (4 * v0 + 1 =? 4 * v0 + 2) with false by (symmetry; apply Z.eqb_neq; lia).
           rewrite Z.eqb_refl. cbn [orb]. split; [reflexivity|].
           replace (258 * (2 * 1 + 1) + v0) with (258 * 3 + v0) by lia. replace (258 * (2 * 1) + v0) with (258 * 2 + v0) by lia. reflexivity.
        -- rewrite Z.eqb_refl. cbn [orb]. split; [reflexivity|].
           replace (258 * (2 * 2 + 1) + v0) with (258 * 5 + v0) by lia. replace (258 * (2 * 2) + v0) with (258 * 4 + v0) by lia. reflexivity.
      * apply V; lia.
    + intros x Hx. destruct (F x) as [F1 F2]. { intros v j Hv Hj. apply Hx; lia. }
      rewrite F1, F2. subst lp'. rewrite !zget_zset, !zdef_zset.
      pose proof (Hx v0 0 ltac:(lia) ltac:(lia)). pose proof (Hx v0 1 ltac:(lia) ltac:(lia)). pose proof (Hx v0 2 ltac:(lia) ltac:(lia)).
      replace (x =? 4 * v0 + 2) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (x =? 4 * v0 + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (x =? 4 * v0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb]. split; reflexivity.
Qed.

Lemma LPV_range : forall len v j, 0 <= zget len (258 * (2 * j + 1) + v) <= 17 -> 0 <= zget len (258 * (2 * j) + v) <= 17 ->
  0 <= LPV len v j < 2097152.
Proof.
  intros len v j H1 H0. unfold LPV.
  set (a := zget len (258 * (2 * j + 1) + v)) in *. set (b := zget len (258 * (2 * j) + v)) in *.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  assert (NN : 0 <= Z.lor (a * 65536) b) by (apply Z.lor_nonneg; lia).
  split; [exact NN|].
  destruct (Z.eq_dec (Z.lor (a * 65536) b) 0) as [E|NZ]; [rewrite E; lia|].
  assert (POS : 0 < Z.lor (a * 65536) b) by lia.
  change 2097152 with (2 ^ 21). apply (proj2 (Z.log2_lt_pow2 _ 21 POS)).
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - apply Z.le_lt_trans with (m := Z.log2 1114112); [apply Z.log2_le_mono; lia| reflexivity].
  - apply Z.le_lt_trans with (m := Z.log2 17); [apply Z.log2_le_mono; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Definition CR (nG : Z) (cost : zarr) : Prop := forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535.
Lemma cost_slow_t_CR : forall n cost len icv t0 nG, CR nG cost -> CR nG (sm_cost_slow_t n cost len icv t0).
Proof.
  induction n as [|n IH]; intros cost len icv t0 nG H; cbn [sm_cost_slow_t]; [exact H|].
  apply IH. intros t Ht. rewrite zget_zset. destruct (t =? t0); [| apply H; exact Ht].
  pose proof (Z.mod_pos_bound (zget cost t0 + zget len (258 * t0 + icv)) 65536 ltac:(lia)). lia.
Qed.
Lemma cost_slow_CR : forall n cost len arr1 nG i, CR nG cost -> CR nG (sm_cost_slow n cost len arr1 nG i).
Proof.
  induction n as [|n IH]; intros cost len arr1 nG i H; [exact H|]. rewrite sm_cost_slow_S. apply IH. apply cost_slow_t_CR. exact H.
Qed.
Lemma zero6_CR : forall nG c, nG <= 6 -> CR nG (zero6 c).
Proof. intros nG c HG t Ht. rewrite zero6_get by lia. lia. Qed.
Lemma shiftr16_range : forall x, 0 <= Z.shiftr (x mod 4294967296) 16 <= 65535.
Proof.
  intros x. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as B.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. split; [apply Z.div_pos; lia|].
  assert (x mod 4294967296 / 65536 < 65536) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma COSTC_CR : forall arr1 len lp nG nMTF gs c, nG <= 6 -> CR nG (COSTC arr1 len lp nG gs (GE nMTF gs) c).
Proof.
  intros arr1 len lp nG nMTF gs c HG. destruct (fastb nG nMTF gs) eqn:FB.
  - rewrite COSTC_fast by exact FB. intros t Ht. rewrite !zget_zset.
    pose proof (land_65535 (psum arr1 lp gs 0 0 50 mod 4294967296)). pose proof (shiftr16_range (psum arr1 lp gs 0 0 50)).
    pose proof (land_65535 (psum arr1 lp gs 1 0 50 mod 4294967296)). pose proof (shiftr16_range (psum arr1 lp gs 1 0 50)).
    pose proof (land_65535 (psum arr1 lp gs 2 0 50 mod 4294967296)). pose proof (shiftr16_range (psum arr1 lp gs 2 0 50)).
    destruct (t =? 5); [lia|]. destruct (t =? 4); [lia|]. destruct (t =? 3); [lia|]. destruct (t =? 2); [lia|].
    destruct (t =? 1); [lia|]. destruct (t =? 0); [lia|]. rewrite zero6_get by lia. lia.
  - rewrite COSTC_slow by exact FB. apply cost_slow_CR. apply zero6_CR. exact HG.
Qed.

(* [comment removed for export] *)
Lemma RFI_entry_le : forall A nG rf m t v, 2 <= A <= 258 -> RFI A nG rf m -> 0 <= t < nG -> 0 <= v < A ->
  zdef rf (258 * t + v) = true /\ 0 <= zget rf (258 * t + v) <= m.
Proof.
  intros A nG rf m t v HA R Ht Hv. destruct (R t Ht) as [X Y]. destruct (X v Hv) as [D G]. split; [exact D|]. split; [exact G|].
  unfold rowsum in Y.
  pose proof (sumF_term_le (Z.to_nat A) (fun i => zget rf (258 * t + (i - 1))) 1 (v + 1)
                ltac:(intros b Hb; apply (proj2 (X (b - 1) ltac:(lia)))) ltac:(lia)) as T.
  cbv beta in T. replace (258 * t + (v + 1 - 1)) with (258 * t + v) in T by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sm_mklens_S_eq : forall n len rf h w p A t,
  sm_mklens (S n) len rf h w p A t =
  (let r := hbMakeCodeLengths len rf h w p (258 * t) (258 * t) A 17 in
   sm_mklens n (hs_len r) rf (hs_heap r) (hs_weight r) (hs_parent r) A (t + 1)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SMB.
  Variables (e0 e : est) (cost0 fave0 heap0 weight0 parent0 : zarr).
  Hypothesis GP : gm_post e0 e.
  Hypothesis NB : 1 <= e_nblock e0 <= NBLOCKMAX + 9.
  Local Notation arr1 := (e_arr1 e). Local Notation A := (sm_alpha e). Local Notation nG := (smA_ng e). Local Notation nMTF := (sm_nmtf e).

  Lemma basics : 3 <= A <= 258 /\ 2 <= nG <= 6 /\ 1 <= nMTF <= NBLOCKMAX + 10 /\ 1 <= e_nInUse e <= 256 /\ zbok arr1 /\
                 (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) /\ (nG = 6 <-> 2400 <= nMTF).
  Proof.
    cps_destruct GP as (NI & NM & _ & _ & _ & ZA1 & MV & _ & ENB & _).
    unfold sm_alpha, smA_ng, sm_nmtf.
    split; [lia|]. split; [apply sm_nGroups_range|]. split; [lia|]. split; [lia|]. split; [exact ZA1|]. split.
    - intros i Hi. unfold mtfv_at. pose proof (MV i Hi). lia.
    - apply sm_nGroups_6.
  Qed.
  Lemma KSEL_facts : 1 <= KSEL e <= 18002 /\ 50 * (KSEL e - 1) < nMTF <= 50 * KSEL e.
  Proof.
    cps_pose basics as (_ & _ & HM & _). unfold KSEL.
    set (M := sm_nmtf e) in *. clearbody M.
    pose proof (Z.div_mod (M + 49) 50 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (M + 49) 50 ltac:(lia)) as R.
    set (q := (M + 49) / 50) in *. set (r := (M + 49) mod 50) in *. lia.
  Qed.
  Theorem smB_static_ok : smB_static e.
  Proof.
    cps_pose basics as (HA & HG & HM & NI & ZA & MV & G6). pose proof KSEL_facts as [K1 K2].
    unfold smB_static.
    split; [exact HA|]. split; [exact HG|]. split; [lia|]. split; [exact NI|]. split; [exact ZA|]. split; [exact MV|].
    split; [exact K1|]. split; [exact K2| exact G6].
  Qed.

  (* [comment removed for export] *)
  Definition LR (l : zarr) : Prop := forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef l (258 * t + v) = true /\ 0 <= zget l (258 * t + v) <= 17.

  Lemma LR_init : LR (smA_len e).
  Proof.
    pose proof basics as (HA & _). intros t v Ht Hv. unfold smA_len.
    destruct (sm_len_init_spec 6 (e_len e) (sm_alpha e) 0 ltac:(lia) ltac:(lia)) as [V _].
    destruct (V t v ltac:(cbn; lia) Hv) as [G D]. rewrite G, D. unfold BZ_GREATER_ICOST. split; [reflexivity| lia].
  Qed.

  Lemma LR_setrow : forall l t gs ge, LR l -> 0 <= t < 6 -> LR (sm_setrow (Z.to_nat A) l t gs ge 0).
  Proof.
    pose proof basics as (HA & _).
    intros l t gs ge H Ht t' v Ht' Hv. destruct (sm_setrow_spec (Z.to_nat A) l t gs ge 0) as [V F].
    destruct (Z.eq_dec t' t) as [->|NE].
    - destruct (V v ltac:(lia)) as [G D]. rewrite G, D. split; [reflexivity|]. unfold BZ_LESSER_ICOST, BZ_GREATER_ICOST. destruct (_ && _)%bool; lia.
    - destruct (F (258 * t' + v) ltac:(nia)) as [G D]. rewrite G, D. apply H; assumption.
  Qed.

  Lemma LR_ip : LR (ip_len (smA_ip e)).
  Proof.
    cps_pose basics as (HA & HG & _).
    cps_pose (smA_facts_intro e0 e GP NB) as (_ & _ & _ & SK & EQ). cbv zeta in SK.
    unfold smA_ip. change (SIP (smA_len e) nG nMTF 0) with (sip0 e). rewrite EQ.
    assert (IND : forall k, (Z.of_nat k <= smA_ng e) -> LR (ip_len (sip_k e k))).
    { induction k as [|k IH]; intros Hk.
      - cbn. apply LR_init.
      - rewrite sip_k_S. rewrite sm_init_iter_eq. cbv zeta. cbn [ip_len].
        destruct (SK k ltac:(lia)) as (NP & _). apply LR_setrow; [apply IH; lia| lia]. }
    apply IND. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lp_ok : forall s, LR (it_len s) -> smB_lp e s.
  Proof.
    cps_pose basics as (HA & HG & _).
    intros s L. unfold smB_lp. intros G6 v j Hv Hj. unfold it_lpk.
    replace (nG =? 6) with true by (symmetry; apply Z.eqb_eq; exact G6).
    destruct (sm_lenpack_spec (Z.to_nat A) (it_lp s) (it_len s) 0 ltac:(lia)) as [V _].
    destruct (V v j ltac:(lia) Hj) as [D G]. rewrite D, G. split; [reflexivity|]. split; [reflexivity|].
    apply LPV_range; apply L; lia.
  Qed.

  (* [comment removed for export] *)
  Definition GI (j : Z) (g : sgs) : Prop :=
    g_nSel g = j /\ g_gs g = Z.min (50 * j) nMTF /\ 0 <= g_totc g <= 65535 * j /\
    RFI A nG (g_rfreq g) (g_gs g) /\
    (forall t, 0 <= t < 6 -> 0 <= zget (g_fave g) t <= j) /\
    (forall i, 0 <= i < j -> zdef (g_sel g) i = true /\ 0 <= zget (g_sel g) i < nG).

  Lemma GI_0 : forall s, GI 0 (G0 e s).
  Proof.
    cps_pose basics as (HA & HG & HM & _).
    intros s. unfold GI, G0. cbn [g_nSel g_gs g_totc g_rfreq g_fave g_sel].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split.
    - unfold it_rf0. apply RFI_zero; lia.
    - split; [| intros; lia]. intros t Ht. rewrite zero6_get by lia. lia.
  Qed.

  Lemma GI_step : forall j g len lp, GI j g -> 0 <= j < KSEL e -> GI (j + 1) (sm_group_iter arr1 len lp nG nMTF g).
  Proof.
    cps_pose basics as (HA & HG & HM & NI & ZA & MV & G6). pose proof KSEL_facts as [K1 K2].
    (intros j g len lp; cps_intros (NS & GS & TC & RF & FV & SL); intros Hj).
    assert (Egs : g_gs g = 50 * j) by lia.
    rewrite sm_group_iter_eq. cbv zeta.
    set (gs := g_gs g) in *. set (ge := GE nMTF gs).
    set (cost := COSTC arr1 len lp nG gs ge (g_cost g)).
    pose proof (COSTC_0 arr1 len lp nG gs ge (g_cost g)) as C0. fold cost in C0.
    pose proof (COSTC_CR arr1 len lp nG nMTF gs (g_cost g) ltac:(lia)) as CC. fold ge in CC. fold cost in CC.
    pose proof (sm_best_hit (Z.to_nat nG) cost 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BT.
    pose proof (sm_best_fst_bound (Z.to_nat nG) cost 0 999999999 (-1) 65535 ltac:(lia) ltac:(lia)
                  ltac:(intros t' Ht'; apply CC; lia)) as BC.
    set (r := sm_best (Z.to_nat nG) cost 0 999999999 (-1)) in *.
    assert (Hgs : 0 <= gs < nMTF) by lia.
    cps_destruct (GE_facts nMTF gs Hgs) as (G1 & G2 & G3). fold ge in G1, G2, G3.
    unfold GI; cbn [g_nSel g_gs g_sel g_rfreq g_totc g_fave].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [| split].
    - replace (ge + 1) with (gs + Z.of_nat (Z.to_nat (ge - gs + 1))) by lia.
      apply RFI_inc; [lia| lia| intros i Hi; apply MV; lia| exact RF].
    - intros t Ht. rewrite zget_zincr. pose proof (FV t Ht). destruct (Z.eqb_spec t (snd r)) as [->|NE]; [| lia].
      pose proof (FV (snd r) ltac:(lia)). lia.
    - intros i Hi. rewrite zget_zset, zdef_zset. destruct (Z.eqb_spec i (g_nSel g)) as [E|NE].
      + rewrite Z.mod_small by lia. split; [reflexivity| lia].
      + cbn [orb]. apply SL. lia.
  Qed.

  Lemma GI_Gj : forall s j, Z.of_nat j <= KSEL e -> GI (Z.of_nat j) (Gj e s j).
  Proof.
    intros s j. induction j as [|j IH]; intros Hj.
    - apply GI_0.
    - rewrite Gj_S. replace (Z.of_nat (S j)) with (Z.of_nat j + 1) by lia. apply GI_step; [apply IH; lia| lia].
  Qed.

  Lemma groups_run : forall s f j, Z.of_nat j <= KSEL e -> (Z.to_nat (KSEL e) - j <= f)%nat ->
    sm_groups f arr1 (it_len s) (it_lpk e s) nG nMTF (Gj e s j) = Gend e s.
  Proof.
    cps_pose basics as (HA & HG & HM & _). pose proof KSEL_facts as [K1 K2].
    intros s f. induction f as [|f IH]; intros j Hj Hf.
    - cbn [sm_groups]. unfold Gend. replace (Z.to_nat (KSEL e)) with j by lia. reflexivity.
    - rewrite sm_groups_S. cps_pose (GI_Gj s j Hj) as (NS & GS & _).
      destruct (Z.leb_spec nMTF (g_gs (Gj e s j))) as [L|L].
      + unfold Gend. replace (Z.to_nat (KSEL e)) with j by lia. reflexivity.
      + rewrite <- Gj_S. apply IH; lia.
  Qed.

  Lemma grp_ok : forall s, smB_grp e s.
  Proof.
    cps_pose basics as (HA & HG & HM & _). pose proof KSEL_facts as [K1 K2].
    intros s. unfold smB_grp. split.
    - intros j Hj. cps_pose (GI_Gj s j Hj) as (NS & GS & TC & RF & FV & SL). cbv zeta.
      split; [exact GS|]. split; [exact NS|]. split; [exact TC|]. split; [| split; [exact FV| exact SL]].
      intros t v Ht Hv. apply (RFI_entry_le A nG); [lia| exact RF| exact Ht| exact Hv].
    - change (G0 e s) with (Gj e s 0). apply groups_run; [lia|].
      assert (KSEL e <= nMTF + 1) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mklens_MLt : forall s n t0,
    (let '(l, h, w, p) := MLt e s t0 in sm_mklens n l (g_rfreq (Gend e s)) h w p A (Z.of_nat t0)) = MLt e s (t0 + n)%nat.
  Proof.
    intros s n. induction n as [|n IH]; intros t0.
    - rewrite Nat.add_0_r. destruct (MLt e s t0) as [[[l h] w] p]. reflexivity.
    - replace (t0 + S n)%nat with (S t0 + n)%nat by lia. rewrite <- IH. cbn [MLt].
      destruct (MLt e s t0) as [[[l h] w] p]. rewrite sm_mklens_S_eq. cbv zeta. unfold ml_step.
      replace (Z.of_nat t0 + 1) with (Z.of_nat (S t0)) by lia. reflexivity.
  Qed.

  Lemma RFG : forall s, RFI A nG (g_rfreq (Gend e s)) nMTF.
  Proof.
    cps_pose basics as (HA & HG & HM & _). pose proof KSEL_facts as [K1 K2].
    intros s. cps_pose (GI_Gj s (Z.to_nat (KSEL e)) ltac:(lia)) as (NS & GS & TC & RF & _).
    unfold Gend. replace nMTF with (g_gs (Gj e s (Z.to_nat (KSEL e)))) by lia. exact RF.
  Qed.

  Lemma ML_step : forall s t, (Z.of_nat t < nG) -> LR (ml_len e s t) ->
    let rf := g_rfreq (Gend e s) in let lb := 258 * Z.of_nat t in
    hm_facts (ml_len e s t) rf lb lb A /\
    ml_len e s (S t) = hs_len (hbMakeCodeLengths (ml_len e s t) rf znew znew znew lb lb A 17) /\
    (forall k, ~ (lb <= k < lb + A) -> zget (ml_len e s (S t)) k = zget (ml_len e s t) k) /\
    (forall k, zdef (ml_len e s t) k = true -> zdef (ml_len e s (S t)) k = true) /\
    LR (ml_len e s (S t)).
  Proof.
    cps_pose basics as (HA & HG & HM & _).
    intros s t Ht L. cbv zeta. pose proof (RFG s) as RF. set (rf := g_rfreq (Gend e s)) in *.
    assert (ROW : forall v, 0 <= v < A -> zdef rf (258 * Z.of_nat t + v) = true /\ 0 <= zget rf (258 * Z.of_nat t + v) < 8388608).
    { intros v Hv. destruct (RFI_entry_le A nG rf nMTF (Z.of_nat t) v ltac:(lia) RF ltac:(lia) Hv) as [D G]. split; [exact D| lia]. }
    destruct (RFI_budget A nG ltac:(lia) rf nMTF (Z.of_nat t) RF ltac:(lia)) as [FNN FS].
    assert (E1 : ml_len e s (S t) = hs_len (hbMakeCodeLengths (ml_len e s t) rf (snd (fst (fst (MLt e s t)))) (snd (fst (MLt e s t))) (snd (MLt e s t))
                                        (258 * Z.of_nat t) (258 * Z.of_nat t) A 17)).
    { unfold ml_len. cbn [MLt]. destruct (MLt e s t) as [[[l h] w] p]. reflexivity. }
    pose proof (hbMakeCodeLengths_lens A 8388607 (258 * Z.of_nat t) ltac:(lia) ltac:(lia) (ml_len e s t) rf
                  (snd (fst (fst (MLt e s t)))) (snd (fst (MLt e s t))) (snd (MLt e s t)) (258 * Z.of_nat t) (fun i Hi => proj1 (proj2 (ROW i Hi))) ltac:(lia)) as HL.
    cbv zeta in HL. rewrite <- E1 in HL. destruct HL as [LO LF].
    assert (ZD : forall k, zdef (ml_len e s (S t)) k = (((258 * Z.of_nat t <=? k) && (k <? 258 * Z.of_nat t + Z.of_nat (Z.to_nat A))) || zdef (ml_len e s t) k)%bool).
    { intros k. rewrite E1. apply hbMakeCodeLengths_zdef. }
    split; [| split; [| split; [| split]]].
    - apply (hm_facts_intro _ _ _ _ _ 8388607); [lia| lia| exact ROW| lia].
    - rewrite E1. apply hbMakeCodeLengths_len_indep; [lia| lia| intros v Hv; apply (proj2 (ROW v Hv))].
    - intros k Hk. apply LF. lia.
    - intros k Hk. rewrite ZD, Hk. apply Bool.orb_true_r.
    - intros t' v Ht' Hv. destruct (Z.eq_dec t' (Z.of_nat t)) as [->|NE].
      + split.
        * rewrite ZD. replace ((258 * Z.of_nat t <=? 258 * Z.of_nat t + v) && (258 * Z.of_nat t + v <? 258 * Z.of_nat t + Z.of_nat (Z.to_nat A)))%bool with true
            by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity.
        * pose proof (LO (v + 1) ltac:(lia)) as X. replace (258 * Z.of_nat t + (v + 1) - 1) with (258 * Z.of_nat t + v) in X by lia. lia.
      + destruct (L t' v Ht' Hv) as [D G]. split.
        * rewrite ZD, D. apply Bool.orb_true_r.
        * rewrite LF by nia. exact G.
  Qed.

  Lemma ML_all : forall s t, (Z.of_nat t <= nG) -> LR (it_len s) -> LR (ml_len e s t).
  Proof.
    intros s t. induction t as [|t IH]; intros Ht L.
    - unfold ml_len. cbn [MLt fst]. exact L.
    - cps_pose (ML_step s t ltac:(lia) (IH ltac:(lia) L)) as (_ & _ & _ & _ & X). exact X.
  Qed.

  Lemma sm_iter_shape : forall s,
    sm_iter arr1 nG A nMTF s =
      (let '(l, h, w, p) := MLt e s (Z.to_nat nG) in let g := Gend e s in
       SITS l (g_rfreq g) (it_lpk e s) (g_sel g) (g_cost g) (g_fave g) (g_nSel g) h w p).
  Proof.
    cps_pose basics as (HA & HG & HM & _). pose proof KSEL_facts as [K1 K2].
    intros s. unfold sm_iter.
    change (if nG =? 6 then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s) with (it_lpk e s).
    change {| g_rfreq := sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0; g_sel := it_sel s; g_cost := it_cost s;
              g_fave := zero6 (it_fave s); g_nSel := 0; g_totc := 0; g_gs := 0 |} with (Gj e s 0).
    rewrite (groups_run s (Z.to_nat (nMTF + 1)) 0 ltac:(lia) ltac:(lia)).
    pose proof (mklens_MLt s (Z.to_nat nG) 0) as E. cbn [MLt Nat.add] in E. change (Z.of_nat 0) with 0 in E. rewrite E.
    destruct (MLt e s (Z.to_nat nG)) as [[[l h] w] p]. reflexivity.
  Qed.

  Lemma ml_ok : forall s, LR (it_len s) -> smB_ml e s /\ LR (it_len (sm_iter arr1 nG A nMTF s)).
  Proof.
    cps_pose basics as (HA & HG & HM & _).
    intros s L. split.
    - unfold smB_ml. split; [| apply sm_iter_shape].
      intros t Ht. cps_pose (ML_step s t Ht (ML_all s t ltac:(lia) L)) as (F1 & F2 & F3 & F4 & _). cbv zeta in F1, F2, F3.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3| exact F4].
    - rewrite sm_iter_shape. pose proof (ML_all s (Z.to_nat nG) ltac:(lia) L) as X. unfold ml_len in X.
      destruct (MLt e s (Z.to_nat nG)) as [[[l h] w] p]. cbn [fst] in X. cbv zeta. cbn [it_len]. exact X.
  Qed.

  Theorem smB_facts_intro_sec : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Proof.
    unfold smB_facts. split; [apply smB_static_ok|].
    assert (ALL : forall k, LR (it_len (ITk e cost0 fave0 heap0 weight0 parent0 k))).
    { induction k as [|k IH].
      - cbn [ITk Nat.iter]. unfold IT0. cbn [it_len]. apply LR_ip.
      - rewrite ITk_S. apply (proj2 (ml_ok _ IH)). }
    intros k Hk. cbv zeta. pose proof (ALL k) as L.
    split; [exact L|]. split; [apply lp_ok; exact L|]. split; [apply grp_ok| apply (proj1 (ml_ok _ L))].
  Qed.
End SMB.

(* [comment removed for export] *)
Theorem smB_facts_intro : forall e0 e c f h w p,
  gm_post e0 e -> 1 <= e_nblock e0 <= NBLOCKMAX + 9 -> smB_facts e c f h w p.
Proof. intros. eapply smB_facts_intro_sec; eassumption. Qed.

End ACeilS1.
