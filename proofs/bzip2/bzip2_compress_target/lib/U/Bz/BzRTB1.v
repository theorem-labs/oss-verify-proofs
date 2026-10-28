(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmas1 BzCLemmasFs BzCRebuildF BzCPermF BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortPost. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCEmit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory BzR3aFs BzR2D1 BzR2D. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzR2E BzR2Eb.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5a.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS BzR4a BzR4d.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.BzR5cX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4d OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.BzR4e OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR1a BzR1e. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRT1 BzRT2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section BZPS. Context {BZP : BzParams}.

Lemma NBLOCKMAX_eq : NBLOCKMAX = 100000 * BLOCKSIZE100K - 19.
Proof. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Pe_arr1 : forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, e_arr1 (EST x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) = x3. Proof. reflexivity. Qed.
Lemma Pe_arr2 : forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, e_arr2 (EST x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) = x4. Proof. reflexivity. Qed.
Lemma Pe_ftab : forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, e_ftab (EST x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) = x5. Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Strategy expand [gp_nInUse gp_unseq gp_maps gp_EOB].
Lemma gp_nInUse_eq : forall x, gp_nInUse x = snd (mk_maps 256 (e_inUse x) (e_unseqToSeq x) 0 0).
Proof. intros x. unfold gp_nInUse, gp_maps. reflexivity. Qed.
Lemma gp_unseq_eq : forall x, gp_unseq x = fst (mk_maps 256 (e_inUse x) (e_unseqToSeq x) 0 0).
Proof. intros x. unfold gp_unseq, gp_maps. reflexivity. Qed.

(* [comment removed for export] *)
Definition EB (e : est) : Prop :=
  zbok (e_arr1 e) /\ zbok (e_arr2 e) /\ bh_w32 (e_ftab e) /\ 1 <= e_nblock e <= NBLOCKMAX + 9 /\ zdefr (e_inUse e) 0 256 /\ RLI (est_rl e).

(* [comment removed for export] *)
Notation EB_e1 e := (cb_sorted e) (only parsing).
Notation EB_e1g e := (est_set_bw (cb_sorted e) (cb_bhdr (cb_hdr (cb_sorted e)) (cb_sorted e))) (only parsing).
Notation EB_eg e := (fst (generateMTFValues (EB_e1g e) znew)) (only parsing).
Notation EB_nI e := (e_nInUse (EB_eg e)) (only parsing).
Notation EB_A e := (e_nInUse (EB_eg e) + 2) (only parsing).
Notation EB_nMTF e := (e_nMTF (EB_eg e)) (only parsing).
Notation EB_nG e := (sm_nGroups (e_nMTF (EB_eg e))) (only parsing).
Notation EB_it e :=
  (sm_iters BZ_N_ITERS (e_arr1 (EB_eg e)) (EB_nG e) (EB_A e) (EB_nMTF e)
    (SITS (ip_len (sm_init_tables 8 (e_mtfFreq (EB_eg e)) (EB_nG e) (EB_A e) (SIP (sm_len_init 6 (e_len (EB_eg e)) (EB_A e) 0) (EB_nG e) (EB_nMTF e) 0)))
          (e_rfreq (EB_eg e)) (e_len_pack (EB_eg e)) (e_selector (EB_eg e)) znew znew 0 znew znew znew)) (only parsing).
Notation EB_nS e := (it_nSel (EB_it e)) (only parsing).
Notation EB_selMtf e := (snd (sm_selmtf (Z.to_nat (EB_nS e)) (yy_init (Z.to_nat (EB_nG e)) znew 0) (it_sel (EB_it e)) (e_selectorMtf (EB_eg e)) 0)) (only parsing).
Notation EB_code e := (sm_assign (Z.to_nat (EB_nG e)) (e_code (EB_eg e)) (it_len (EB_it e)) (EB_A e) 0) (only parsing).
Notation EB_in16 e := (sm_in16 16 znew (e_inUse (EB_eg e)) 0) (only parsing).
(* [comment removed for export] *)
Definition body_ws (e : est) : list (Z * Z) :=
  ws_send (e_inUse (EB_eg e)) (EB_in16 e) (EB_selMtf e) (it_len (EB_it e)) (EB_code e) (e_arr1 (EB_eg e)) (it_sel (EB_it e))
          (EB_nG e) (EB_nS e) (EB_A e) (EB_nMTF e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ws_dtables_legal' : forall n lnT aS t, (forall t', t <= t' < t + Z.of_nat n -> 0 <= lnT t' 0 < 32) -> wlegal (ws_dtables n lnT aS t).
Proof.
  induction n as [|n IH]; intros lnT aS t H; cbn [ws_dtables]; [apply wlegal_nil|].
  apply wlegal_app. split; [| apply IH; intros; apply H; lia].
  apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 5) with 32; pose proof (H t ltac:(lia)); lia| apply ws_drow_legal].
Qed.
Lemma ws_lens_bits' : forall n len aS t, 0 <= aS -> (forall t', t <= t' < t + Z.of_nat n -> 0 <= zget len (258 * t' + 0) < 32) ->
  wbits (ws_lens n len aS t) = wbits (ws_dtables n (fun t' v => zget len (258 * t' + v)) (Z.to_nat aS) t) /\ wlegal (ws_lens n len aS t).
Proof.
  induction n as [|n IH]; intros len aS t HA H; cbn [ws_lens ws_dtables]; [split; [reflexivity| apply wlegal_nil]|].
  destruct (IH len aS (t + 1) HA ltac:(intros; apply H; lia)) as [E1 L1].
  pose proof (H t ltac:(lia)) as H0.
  destruct (ws_lens_row_bits (Z.to_nat aS) len t 0 (zget len (258 * t + 0)) [] wlegal_nil) as [ER LR]. rewrite !app_nil_r in ER.
  assert (L5 : wlegal [(5, zget len (258 * t + 0))]) by (apply wlegal_cons; split; [cbn [fst snd]; change (2 ^ 5) with 32; lia| apply wlegal_nil]).
  split.
  - change ((5, zget len (258 * t + 0)) :: ws_lens_row (Z.to_nat aS) len t 0 (zget len (258 * t + 0))) with ([(5, zget len (258 * t + 0))] ++ ws_lens_row (Z.to_nat aS) len t 0 (zget len (258 * t + 0))).
    change ((5, zget len (258 * t + 0)) :: ws_drow (Z.to_nat aS) (fun v : Z => zget len (258 * t + v)) 0 (zget len (258 * t + 0))) with ([(5, zget len (258 * t + 0))] ++ ws_drow (Z.to_nat aS) (fun v : Z => zget len (258 * t + v)) 0 (zget len (258 * t + 0))).
    rewrite !wbits_app; try assumption; try (apply wlegal_app; split; assumption); try apply ws_drow_legal; try (apply ws_dtables_legal'; intros; apply H; lia).
    + rewrite E1, ER. reflexivity.
    + apply wlegal_app. split; [exact L5| apply ws_drow_legal].
  - change ((5, zget len (258 * t + 0)) :: ws_lens_row (Z.to_nat aS) len t 0 (zget len (258 * t + 0))) with ([(5, zget len (258 * t + 0))] ++ ws_lens_row (Z.to_nat aS) len t 0 (zget len (258 * t + 0))).
    apply wlegal_app. split; [apply wlegal_app; split; assumption| exact L1].
Qed.
Lemma ws_rows_ext : forall n g g' bit i, (forall j, (g j =? 0) = (g' j =? 0)) -> ws_rows n g bit i = ws_rows n g' bit i.
Proof. induction n as [|n IH]; intros g g' bit i H; cbn [ws_rows]; [reflexivity|]. rewrite (H i), (IH g g') by exact H. reflexivity. Qed.
Lemma bit01_eqb0 : forall x, (bit01 x =? 0) = (x =? 0).
Proof. intros x. unfold bit01. destruct (x =? 0); reflexivity. Qed.

Section SymLegal.
  Variables (sel : Z -> Z) (Lf : Z -> Z -> Z) (A nG nS : Z).
  Hypothesis HA : 0 <= A.
  Hypothesis HS : forall g, 0 <= g < nS -> 0 <= sel g < nG.
  Hypothesis HL : forall t v, 0 <= t < nG -> 0 <= v < A -> 1 <= Lf t v <= 20.
  Hypothesis HK : forall t k, 0 <= t < nG -> 1 <= k -> wsum (Lf t) A k <= 2 ^ k.
  Lemma ws_sym_legal' : forall xs k, 0 <= k -> k + Z.of_nat (length xs) <= 50 * nS -> Forall (fun x => 0 <= x < A) xs -> wlegal (ws_sym sel Lf A k xs).
  Proof.
    induction xs as [|x xs IH]; intros k Hk Hlen HX; cbn [ws_sym length] in *; [apply wlegal_nil|].
    apply Forall_cons_iff in HX as [Hx HX].
    assert (G : 0 <= sel (k / 50) < nG).
    { apply HS. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    apply wlegal_cons. split; [| apply IH; [lia| lia| exact HX]]. cbn [fst snd].
    pose proof (HL (sel (k / 50)) x G Hx). split; [lia|].
    apply (ccode_lt (Lf (sel (k / 50))) A); [intros j Hj; pose proof (HL _ j G Hj); lia| intros n Hn; apply HK; [exact G| exact Hn]| exact Hx].
  Qed.
End SymLegal.

Section Blk.
  Variable e : est.
  Hypothesis HE : EB e.

  (* [comment removed for export] *)
  Local Notation nb := (e_nblock e).
  Local Notation e1 := (EB_e1 e).
  Local Notation e1g := (EB_e1g e).
  Local Notation eg := (EB_eg e).

  Lemma eb_nb : 1 <= nb <= 899990.
  Proof. cps_destruct HE as (_ & _ & _ & NB & _). rewrite NBLOCKMAX_eq in NB. pose proof BS_range. lia. Qed.

  (* [comment removed for export] *)
  Lemma e0_facts : zbok (e_arr1 (cb_e0 e)) /\ zbok (e_arr2 (cb_e0 e)) /\ bh_w32 (e_ftab (cb_e0 e)) /\ e_nblock (cb_e0 e) = nb /\
                   e_arr2 (cb_e0 e) = e_arr2 e /\ e_inUse (cb_e0 e) = e_inUse e /\ e_arr1 (cb_e0 e) = e_arr1 e.
  Proof.
    cps_destruct HE as (B1 & B2 & FT & _). cps_destruct (cb_e0_fields e) as (E1 & E2 & E3 & E4 & E5 & E6).
    rewrite E1, E2, E3, E4, E5. split; [exact B1|]. split; [exact B2|]. split; [exact FT|]. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition t : list Z := block_of (e_arr2 e) nb.
  Definition pi : nat -> nat := perm_pi (e_arr1 e1).
  Definition rho : nat -> nat := perm_rho (e_arr1 e1) nb.

  Lemma e1_sort :
    zbok (e_arr1 e1) /\ zbok (e_arr2 e1) /\ bh_w32 (e_ftab e1) /\ fm_perm (e_arr1 e1) nb /\
    (forall q, 0 <= q < nb -> exists p, 0 <= p < nb /\ rd8 (e_arr2 e) p = rd8 (e_arr2 e1) q) /\
    0 <= e_origPtr e1 < nb /\ e_nblock e1 = nb /\ e_inUse e1 = e_inUse e /\
    bwt t pi rho /\ e_origPtr e1 = Z.of_nat (origPtr rho) /\
    (forall q, 0 <= q < nb -> rd8 (e_arr2 e1) q = rd8 (e_arr2 e) q).
  Proof.
    cps_pose e0_facts as (B1 & B2 & FT & NB & A2 & IU & A1). pose proof eb_nb as NBR.
    pose proof (blockSort_out (cb_e0 e) B1 B2 FT ltac:(lia)) as BO. cbv zeta in BO. rewrite NB, A2, IU in BO.
    pose proof (blockSort_bwt_ok (cb_e0 e) B1 B2 FT ltac:(lia)) as BB. cbv zeta in BB. rewrite NB, A2 in BB.
    unfold t, pi, rho, cb_sorted.
    cps_destruct BO as (Z1 & Z2 & W3 & PM & OCC & OP & ENB & EIU & ENI). cps_destruct BB as (BW & _ & EO & AG & _).
    split; [exact Z1|]. split; [exact Z2|]. split; [exact W3|]. split; [exact PM|]. split; [exact OCC|]. split; [exact OP|].
    split; [exact ENB|]. split; [exact EIU|]. split; [exact BW|]. split; [exact EO| exact AG].
  Qed.

  (* [comment removed for export] *)
  Lemma e1_gm : gm_facts e1 /\ gm_facts e1g.
  Proof.
    cps_pose e1_sort as (Z1 & Z2 & W3 & PM & OCC & OP & ENB & EIU & BW & EO & AG).
    cps_destruct HE as (B1 & B2 & FT & NB & DEFR & RL). pose proof eb_nb as NBR.
    cps_pose (RLI_facts _ RL) as (_ & _ & _ & _ & COV & IU & _).
    assert (G : gm_facts e1).
    { unfold gm_facts. rewrite ENB, EIU. split; [exact Z1|]. split; [exact Z2|]. split; [lia|].
      split; [exact DEFR|]. split; [exact IU|]. split.
      - intros j Hj. cps_destruct (OCC j Hj) as (p & Hp & Ep). rewrite <- Ep. apply COV.
        unfold rl_bytes. cbn [rl_block rl_nblock est_rl]. rewrite <- (block_of_nth (e_arr2 e) (e_nblock e) p) by lia.
        apply nth_In. rewrite block_of_length. lia.
      - intros i Hi. apply (proj1 PM). exact Hi. }
    split; [exact G|]. apply gm_facts_set_bw. exact G.
  Qed.

  (* [comment removed for export] *)
  Definition us : list Z := ulist e1g (Z.to_nat nb).
  Lemma e1g_fields : e_nblock e1g = nb /\ e_arr2 e1g = e_arr2 e1 /\ e_arr1 e1g = e_arr1 e1 /\ e_inUse e1g = e_inUse e /\
                     e_bw e1g = cb_bhdr (cb_hdr e1) e1.
  Proof.
    cps_pose e1_sort as (_ & _ & _ & _ & _ & _ & ENB & EIU & _).
    cbn [e_nblock e_arr2 e_arr1 e_inUse e_bw est_set_bw]. rewrite ENB, EIU. repeat split; reflexivity.
  Qed.

  Lemma eg_mtfv :
    e_nMTF eg = Z.of_nat (length (gsyms e1g)) /\
    (forall k, (k < length (gsyms e1g))%nat -> mtfv_at (e_arr1 eg) (Z.of_nat k) = nth k (gsyms e1g) 0) /\
    e_nInUse eg = gp_nInUse e1g /\ e_unseqToSeq eg = gp_unseq e1g /\ Forall (fun u => 0 <= u < gp_nInUse e1g) us /\
    1 <= gp_nInUse e1g <= 256 /\ gp_EOB e1g = gp_nInUse e1g + 1 /\ gm_post e1g eg.
  Proof.
    destruct e1_gm as [_ G]. pose proof (generateMTFValues_mtfv e1g G) as X. cbv zeta in X.
    pose proof e1g_fields as (ENB & _). unfold us. rewrite <- ENB.
    cps_destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    repeat (split; [assumption|]). apply generateMTFValues_post. exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma eb_ranges : 1 <= EB_nI e <= 256 /\ EB_A e = EB_nI e + 2 /\ 1 <= EB_nMTF e <= nb + 1 /\ 2 <= EB_nG e <= 6 /\
                    (forall k, 0 <= k < EB_nMTF e -> 0 <= mtfv_at (e_arr1 eg) k < EB_A e).
  Proof.
    cps_pose eg_mtfv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & GP). pose proof e1g_fields as (ENB & _).
    rewrite X3.
    split; [exact X6|]. split; [reflexivity|].
    unfold gm_post in GP. cbv zeta in GP. cps_destruct GP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _). rewrite ENB in P2.
    split; [exact P2|]. split; [apply sm_nGroups_range|].
    intros k Hk. unfold mtfv_at. pose proof (P7 k Hk). rewrite X3 in H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_iter_kraft : forall A nG arr1 nMTF s, 2 <= A <= 258 -> 1 <= nG <= 6 -> 1 <= nMTF <= 4194304 ->
    (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) ->
    forall tt k, 0 <= tt < nG -> 1 <= k -> wsum (Lrow (it_len (sm_iter arr1 nG A nMTF s)) (258 * tt)) A k <= 2 ^ k.
  Proof.
    intros A nG arr1 nMTF s HA HG HM MV tt k Ht Hk. unfold sm_iter.
    set (lp := if nG =? 6 then _ else _).
    pose proof (groups_spec A nG HA HG arr1 (it_len s) lp nMTF ltac:(lia) MV (sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0)
                  (it_sel s) (it_cost s) (zero6 (it_fave s)) (RFI_zero A nG HA HG (it_rfreq s))) as GS. cbv zeta in GS.
    set (g := sm_groups _ _ _ _ _ _ _) in *.
    cps_destruct GS as (K & K1 & NS & KB & GG & SEL & RF).
    pose proof (sm_mklens_kraft A nG HA nMTF (Z.to_nat nG) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) 0 HM RF ltac:(lia) ltac:(lia)) as KR.
    cbv zeta in KR.
    destruct (sm_mklens (Z.to_nat nG) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) A 0) as [[[len heap] weight] parent].
    cbn [fst it_len] in KR |- *. apply KR; lia.
  Qed.
  Lemma sm_iters_kraft : forall n A nG arr1 nMTF s, (1 <= n)%nat -> 2 <= A <= 258 -> 1 <= nG <= 6 -> 1 <= nMTF <= 4194304 ->
    (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) ->
    forall tt k, 0 <= tt < nG -> 1 <= k -> wsum (Lrow (it_len (sm_iters n arr1 nG A nMTF s)) (258 * tt)) A k <= 2 ^ k.
  Proof.
    induction n as [|n IH]; intros A nG arr1 nMTF s Hn HA HG HM MV tt k Ht Hk; [lia|]. cbn [sm_iters].
    destruct n as [|n]; [cbn [sm_iters]; apply sm_iter_kraft; assumption|].
    apply IH; try assumption. lia.
  Qed.

  Lemma eb_tables :
    let it := EB_it e in let nG := EB_nG e in let nS := EB_nS e in let A := EB_A e in let nMTF := EB_nMTF e in
    1 <= nS <= 18001 /\ 50 * (nS - 1) < nMTF <= 50 * nS /\
    (forall i, 0 <= i < nS -> 0 <= zget (it_sel it) i < nG) /\
    (forall tt v, 0 <= tt < nG -> 0 <= v < A -> 1 <= zget (it_len it) (258 * tt + v) <= 17) /\
    (forall tt k, 0 <= tt < nG -> 1 <= k -> wsum (Lrow (it_len it) (258 * tt)) A k <= 2 ^ k) /\
    (forall tt v, 0 <= tt < nG -> 0 <= v < A -> zget (EB_code e) (258 * tt + v) = ccode (Lrow (it_len it) (258 * tt)) A v) /\
    (forall k, 0 <= k < nS -> 0 <= zget (EB_selMtf e) k < nG).
  Proof.
    cbv zeta. cps_pose eb_ranges as (RI & RA & RM & RG & MV). pose proof eb_nb as NBR.
    assert (HA : 2 <= EB_A e <= 258) by lia. assert (HG : 1 <= EB_nG e <= 6) by lia. assert (HM : 1 <= EB_nMTF e <= 4194304) by lia.
    match goal with |- context [sm_iters BZ_N_ITERS ?a ?g ?A ?m ?s0] =>
      pose proof (sm_iters_ITF A g HA HG BZ_N_ITERS a m s0 ltac:(unfold BZ_N_ITERS; lia) HM MV) as IT;
      pose proof (sm_iters_kraft BZ_N_ITERS A g a m s0 ltac:(unfold BZ_N_ITERS; lia) HA HG HM MV) as KR;
      set (it := sm_iters BZ_N_ITERS a g A m s0) in * end.
    cps_destruct IT as (K & K1 & NS & KB & SEL & RO & RF). rewrite NS.
    split; [lia|]. split; [exact KB|]. split; [exact SEL|]. split; [intros tt v Ht Hv; apply (RO tt Ht v Hv)|]. split; [exact KR|]. split.
    - intros tt v Ht Hv. pose proof (sm_assign_ccode (EB_A e) HA (Z.to_nat (EB_nG e)) (e_code eg) (it_len it) 0 ltac:(lia)) as AC. cbv zeta in AC.
      assert (LL : forall t v, 0 <= t < 0 + Z.of_nat (Z.to_nat (EB_nG e)) -> 0 <= v < EB_A e -> 1 <= zget (it_len it) (258 * t + v) <= 20).
      { intros t' v' Ht' Hv'. pose proof (RO t' ltac:(lia) v' Hv'). lia. }
      apply (proj1 (AC LL)); lia.
    - intros k Hk. assert (HG8 : 1 <= EB_nG e <= 8) by lia. apply (proj2 (sels_d_spec (EB_nG e) K (it_sel it) (e_selectorMtf eg) znew dst_zero k HG8 ltac:(lia) SEL)). exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma eb_it_len20 : forall tt v, 0 <= tt < EB_nG e -> 0 <= v < EB_A e -> 1 <= zget (it_len (EB_it e)) (258 * tt + v) <= 20.
  Proof. pose proof eb_tables as T. cbv zeta in T. cps_destruct T as (_ & _ & _ & RO & _). intros tt v Ht Hv. pose proof (RO tt v Ht Hv). lia. Qed.
  Lemma eb_nI_nneg : 0 <= EB_nI e.
  Proof. pose proof eb_ranges as (RI & _). lia. Qed.
  Lemma eb_body : e_bw (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = wapp (cb_bhdr (cb_hdr e1) e1) (body_ws e).
  Proof.
    cps_pose e1g_fields as (_ & _ & _ & _ & EBW). cps_pose eg_mtfv as (_ & _ & X3 & _ & _ & _ & _ & GP).
    unfold gm_post in GP. cbv zeta in GP. cps_destruct GP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GBW & _).
    pose proof (sendMTFValues_wapp eg znew znew znew znew znew znew znew) as SW. cbv zeta in SW. rewrite GBW, EBW in SW.
    unfold body_ws. apply SW; [exact eb_it_len20| exact eb_nI_nneg].
  Qed.
  Lemma eb_orig : 0 <= e_origPtr (cb_sorted e) < 2 ^ 24.
  Proof. cps_pose e1_sort as (_ & _ & _ & _ & _ & OP & _). pose proof eb_nb. change (2 ^ 24) with 16777216. lia. Qed.

  (* [comment removed for export] *)
  Lemma eb_syms :
    let xs := gsyms e1g in
    length us = Z.to_nat nb /\ Z.of_nat (length xs) = EB_nMTF e /\ mtfv_list (e_arr1 eg) 0 (Z.to_nat (EB_nMTF e)) = xs /\
    (exists body, xs = body ++ [gp_EOB e1g] /\ Forall (fun x => 0 <= x < gp_EOB e1g) body) /\
    runs_ok 20 0 xs /\ Forall (fun u => 0 <= u < gp_nInUse e1g) us /\ gp_EOB e1g = gp_nInUse e1g + 1 /\ gp_nInUse e1g = EB_nI e /\
    Z.of_nat (length xs) <= 50 * EB_nS e.
  Proof.
    cbv zeta. cps_pose eg_mtfv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & GP). pose proof eb_nb as NBR.
    pose proof eb_tables as T. cbv zeta in T. cps_destruct T as (NS & KB & _).
    assert (LUS : length us = Z.to_nat nb) by (unfold us; apply ulist_length).
    split; [exact LUS|]. split; [rewrite X1; lia|]. split; [rewrite X1, Nat2Z.id; apply mtfv_list_eq; exact X2|].
    split; [| split; [| split; [exact X5| split; [exact X7| split; [symmetry; exact X3| rewrite <- X1; lia]]]]].
    - unfold gsyms. rewrite X7, (proj1 e1g_fields). fold us. assert (H1 : 1 <= gp_nInUse e1g) by lia. assert (H0 : 0 <= 0) by lia.
      apply (genc_shape (gp_nInUse e1g) (gp_nInUse e1g + 1) H1 eq_refl us (fun k => k) 0 (MPERM_id _) X5 H0).
    - unfold gsyms. rewrite X7, (proj1 e1g_fields). fold us. assert (H1 : 1 <= gp_nInUse e1g) by lia. assert (H0 : 0 <= 0) by lia.
      apply (genc_runs_ok (gp_nInUse e1g) (gp_nInUse e1g + 1) H1 eq_refl us (fun k => k) 0 (MPERM_id _) X5 H0).
      rewrite LUS. change (2 ^ 20) with 1048576. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma eb_data :
    ws_data (Z.to_nat (EB_nMTF e + 1)) (it_len (EB_it e)) (EB_code e) (e_arr1 eg) (it_sel (EB_it e)) (EB_nMTF e) 0 0 =
    ws_sym (fun g => zget (it_sel (EB_it e)) g) (fun t => Lrow (it_len (EB_it e)) (258 * t)) (EB_A e) 0 (gsyms e1g).
  Proof.
    pose proof eb_tables as T. cbv zeta in T. cps_destruct T as (NS & KB & SEL & RO & KR & CC & SM). cps_pose eb_ranges as (RI & RA & RM & RG & MV).
    pose proof eb_syms as S. cbv zeta in S. cps_destruct S as (_ & LX & ML & _).
    rewrite <- ML. apply (ws_data_sym0 _ _ _ _ _ _ _ (EB_nG e)); [lia| | | exact MV].
    - intros g Hg H50. apply SEL. lia.
    - intros tt v Ht Hv. split; [reflexivity| apply CC; assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma eb_legal : wlegal (body_ws e).
  Proof.
    pose proof eb_tables as T. cbv zeta in T. cps_destruct T as (NS & KB & SEL & RO & KR & CC & SM). cps_pose eb_ranges as (RI & RA & RM & RG & MV).
    pose proof eb_syms as S. cbv zeta in S. cps_destruct S as (LUS & LX & ML & (body & XB & FB) & RUNS & FUS & EOB1 & NIE & L50).
    unfold body_ws, ws_send.
    apply wlegal_app. split. { rewrite ws_in16_bits16. apply ws_bits16_legal. intros; apply bit01_range. }
    apply wlegal_app. split. { rewrite ws_inuse_rows. apply ws_rows_legal. intros; apply bit01_range. }
    apply wlegal_app. split. { apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 3) with 8; lia|]. apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 15) with 32768; lia| apply wlegal_nil]. }
    apply wlegal_app. split. { rewrite ws_sels_unary. apply ws_unary_legal. }
    assert (HROWS : forall t', 0 <= t' < 0 + Z.of_nat (Z.to_nat (EB_nG e)) -> 0 <= zget (it_len (EB_it e)) (258 * t' + 0) < 32).
    { intros t' Ht'. pose proof (RO t' 0 ltac:(lia) ltac:(lia)). lia. }
    assert (HA0 : 0 <= EB_A e) by lia.
    apply wlegal_app. split. { exact (proj2 (ws_lens_bits' (Z.to_nat (EB_nG e)) (it_len (EB_it e)) (EB_A e) 0 HA0 HROWS)). }
    rewrite eb_data. apply (ws_sym_legal' _ _ _ (EB_nG e) (EB_nS e)); try lia.
    - exact SEL.
    - intros tt v Ht Hv. unfold Lrow. pose proof (RO tt v Ht Hv). lia.
    - exact KR.
    - rewrite XB. apply Forall_app. split; [eapply Forall_impl; [| exact FB]; cbv beta; intros; lia|]. constructor; [lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma us_nth : forall i, (i < Z.to_nat nb)%nat -> nth i us 0 = zget (gp_unseq e1g) (Lc t pi i).
  Proof.
    intros i Hi. cps_pose e1_sort as (Z1 & Z2 & W3 & PM & OCC & OP & ENB & EIU & BW & EO & AG). pose proof eb_nb as NBR.
    cps_pose e1g_fields as (GNB & GA2 & GA1 & _).
    unfold us, ulist. rewrite (nth_map_seq _ _ 0) by lia. cbn [Nat.add]. unfold uval. rewrite GNB, GA2, GA1.
    assert (NB1 : 1 <= nb) by lia. assert (HI : 0 <= Z.of_nat i < nb) by lia.
    pose proof (gm_sym_Lc (e_arr2 e) (e_arr1 e1) nb NB1 PM (e_arr2 e1) (Z.of_nat i) AG HI) as G. cbv zeta in G. rewrite G.
    unfold t, pi. rewrite Nat2Z.id. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma eb_misc :
    0 <= crc_final (e_blockCRC e) < 4294967296 /\
    e_origPtr e1 = Z.of_nat (origPtr rho) /\
    (forall c, 0 <= c < 256 -> zget (e_inUse e) c = 0 \/ zget (e_inUse e) c = 1) /\
    (forall b, In b t -> zget (e_inUse e) b = 1) /\
    length t = Z.to_nat nb /\ Z.of_nat (length t) < 2 ^ 20 /\ Z.of_nat (length t) + 10 <= 100000 * BLOCKSIZE100K /\
    e_inUse eg = e_inUse e /\ e_inUse e1g = e_inUse e /\ e_unseqToSeq eg = gp_unseq e1g /\ e_nInUse eg = gp_nInUse e1g /\
    rlcodes t (rl_data (est_rl e)) /\ e_blockCRC e = crc_list crc_init (rl_data (est_rl e)) /\ t = rl_bytes (est_rl e).
  Proof.
    cps_destruct HE as (B1 & B2 & FT & NB & DEFR & RL). pose proof eb_nb as NBR. pose proof BS_range as BSR.
    cps_pose (RLI_facts _ RL) as (RC & CRC & _ & _ & COV & IU & _ & RI & _).
    cps_pose e1_sort as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EO & _). cps_pose e1g_fields as (_ & _ & _ & GIU & _).
    cps_pose eg_mtfv as (_ & _ & X3 & X4 & _ & _ & _ & GP).
    assert (ET : t = rl_bytes (est_rl e)) by reflexivity.
    assert (LT : length t = Z.to_nat nb) by (unfold t; apply block_of_length).
    split. { destruct RI as [(_ & R2 & _) _]. cbn [rl_crc est_rl] in R2. apply crc_final_range. exact R2. }
    split; [exact EO|]. split; [exact IU|]. split; [rewrite ET; exact COV|]. split; [exact LT|].
    split; [rewrite LT; change (2 ^ 20) with 1048576; lia|]. split; [rewrite LT; rewrite NBLOCKMAX_eq in NB; lia|].
    unfold gm_post in GP. cbv zeta in GP. cps_destruct GP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GI & _).
    split; [rewrite GI; exact GIU|]. split; [exact GIU|]. split; [exact X4|]. split; [exact X3|].
    split; [rewrite ET; exact RC|]. split; [cbn [rl_crc est_rl] in CRC; exact CRC| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma eb_exchange :
    let inUse := e_inUse e in
    let in16 := sm_in16 16 znew inUse 0 in
    let f16 := fun i => bit01 (zget in16 i) in
    let bit := fun c => bit01 (zget inUse c) in
    let msel := fun j => zget (EB_selMtf e) j in
    let lnT := fun t v => zget (it_len (EB_it e)) (258 * t + v) in
    let Lf := fun t => Lrow (it_len (EB_it e)) (258 * t) in
    wbits (ws_bhdr_e (crc_final (e_blockCRC e)) (e_origPtr e1) ++ body_ws e) =
    wbits (ws_blk_hdr (crc_final (e_blockCRC e)) (e_origPtr e1) ++ ws_bits16 16 f16 0 ++ ws_rows 16 f16 bit 0 ++ [(3, EB_nG e); (15, EB_nS e)]
           ++ ws_unary (Z.to_nat (EB_nS e)) msel 0 ++ ws_dtables (Z.to_nat (EB_nG e)) lnT (Z.to_nat (EB_A e)) 0
           ++ ws_sym (fun g => zget (it_sel (EB_it e)) g) Lf (EB_A e) 0 (gsyms e1g)).
  Proof.
    cbv zeta. pose proof eb_tables as T. cbv zeta in T. cps_destruct T as (NS & KB & SEL & RO & KR & CC & SM). cps_pose eb_ranges as (RI & RA & RM & RG & MV).
    pose proof eb_syms as S. cbv zeta in S. cps_destruct S as (LUS & LX & ML & (body & XB & FB) & RUNS & FUS & EOB1 & NIE & L50).
    cps_pose eb_misc as (CR & EO & IU & COV & LT & L20 & LBS & GIE & _). pose proof eb_orig as OPR.
    pose proof eb_legal as BL. unfold body_ws, ws_send in BL |- *. rewrite GIE in BL |- *. rewrite eb_data in BL |- *.
    rewrite ws_in16_bits16, ws_inuse_rows, ws_sels_unary in BL |- *.
    rewrite (ws_rows_ext 16 (fun j => zget (sm_in16 16 znew (e_inUse e) 0) j) (fun i => bit01 (zget (sm_in16 16 znew (e_inUse e) 0) i))) in BL |- * by (intros j; symmetry; apply bit01_eqb0).
    assert (HROWS : forall t', 0 <= t' < 0 + Z.of_nat (Z.to_nat (EB_nG e)) -> 0 <= zget (it_len (EB_it e)) (258 * t' + 0) < 32).
    { intros t' Ht'. pose proof (RO t' 0 ltac:(lia) ltac:(lia)). lia. }
    assert (HA0 : 0 <= EB_A e) by lia.
    destruct (ws_lens_bits' (Z.to_nat (EB_nG e)) (it_len (EB_it e)) (EB_A e) 0 HA0 HROWS) as [LE LL].
    (* [comment removed for export] *)
    apply wlegal_app in BL as [W1 BL]. apply wlegal_app in BL as [W2 BL]. apply wlegal_app in BL as [W3 BL]. apply wlegal_app in BL as [W4 BL]. apply wlegal_app in BL as [W5 W6].
    pose proof (ws_bhdr_e_legal (crc_final (e_blockCRC e)) (e_origPtr e1) OPR) as W0.
    pose proof (ws_blk_hdr_legal (crc_final (e_blockCRC e)) (e_origPtr e1) ltac:(change (2 ^ 24) with 16777216 in OPR; exact OPR)) as W0'.
    pose proof (ws_dtables_legal' (Z.to_nat (EB_nG e)) (fun t v => zget (it_len (EB_it e)) (258 * t + v)) (Z.to_nat (EB_A e)) 0 HROWS) as W5'.
    assert (WL : forall a b, wlegal a -> wlegal b -> wlegal (a ++ b)) by (intros; apply wlegal_app; split; assumption).
    rewrite !(wbits_app (ws_bhdr_e _ _)) by auto 10.
    rewrite !(wbits_app (ws_blk_hdr _ _)) by auto 10.
    rewrite (ws_bhdr_e_bits _ _ OPR). f_equal.
    rewrite !(wbits_app (ws_bits16 _ _ _)) by auto 10. f_equal.
    rewrite !(wbits_app (ws_rows _ _ _ _)) by auto 10. f_equal.
    rewrite !(wbits_app [_; _]) by auto 10. f_equal.
    rewrite !(wbits_app (ws_unary _ _ _)) by auto 10. f_equal.
    rewrite (wbits_app (ws_lens _ _ _ _)), (wbits_app (ws_dtables _ _ _ _)) by auto 10. rewrite LE. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma eb_bw1 : (e_blockNo e = 1 \/ BWZ (e_bw e)) -> BWZ (cb_bhdr (cb_hdr e1) e1).
  Proof.
    intros ALT. cps_pose (cb_sorted_fields e) as (SN & SB & SI' & SW).
    apply cb_bhdr_BWZ. apply cb_hdr_BWZ; rewrite ?SW; [| cbn [bw_zb]; apply zbok_znew| cbn [bw_numZ]; lia].
    rewrite SB. destruct ALT as [A1|A2]; [left; exact A1| right]. destruct A2 as [(B1 & B2 & B3) B4].
    split; [unfold bw_ok; cbn [bw_buff bw_live bw_numZ]; lia| cbn [bw_zb]; apply zbok_znew].
  Qed.
  Lemma eb_sz : (e_blockNo e = 1 \/ BWZ (e_bw e)) -> BWZ (e_bw (fst (sendMTFValues eg znew znew znew znew znew znew znew))).
  Proof.
    intros ALT. pose proof (eb_bw1 ALT) as BW1. cps_pose eb_ranges as (RI & RA & RM & RG & MV). pose proof eb_nb as NBR.
    cps_pose e1g_fields as (_ & _ & _ & _ & GBW). cps_pose eg_mtfv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & GP).
    unfold gm_post in GP. cbv zeta in GP. cps_destruct GP as (_ & _ & _ & _ & _ & ZA1 & _ & _ & _ & GA2 & _ & EBG & GFT & _).
    apply sendMTF_BWZ; [lia| lia| exact MV| rewrite EBG, GBW; exact BW1].
  Qed.
  Lemma eb_sf : e_arr1 (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_arr1 eg /\
                e_arr2 (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_arr2 eg /\
                e_ftab (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_ftab eg.
  Proof.
    cps_destruct (sm_shape eg znew znew znew znew znew znew znew) as (b0 & n0 & s1 & s2 & l1 & c1 & r1 & l2 & E). rewrite E.
    rewrite Pe_arr1, Pe_arr2, Pe_ftab. repeat split; reflexivity.
  Qed.
  Lemma eb_arrs : forall b, (e_blockNo e = 1 \/ BWZ (e_bw e)) -> bw_zb (e_bw e) = znew -> bw_numZ (e_bw e) = 0 ->
    let e' := fst (compressBlock e b znew) in
    zbok (e_arr1 e') /\ zbok (e_arr2 e') /\ bh_w32 (e_ftab e') /\ (b = false -> BWZ (e_bw e')).
  Proof.
    intros il ALT ZB NZ. cbv zeta. pose proof (compressBlock_fields e il) as CFD. cbv zeta in CFD.
    pose proof eb_nb as NBR. replace (0 <? nb) with true in CFD by (symmetry; apply Z.ltb_lt; lia). cbv iota zeta in CFD.
    cps_destruct CFD as (EA1 & EFT & EA2 & EBW).
    cps_pose e1_sort as (Z1 & Z2 & W3 & _).
    cps_pose eg_mtfv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & GP).
    unfold gm_post in GP. cbv zeta in GP. cps_destruct GP as (_ & _ & _ & _ & _ & ZA1 & _ & _ & _ & GA2 & _ & EBG & GFT & _).
    pose proof (eb_sz ALT) as SZ. cps_pose eb_sf as (SA1 & SA2 & SFT).
    rewrite EA1, EFT, EA2, SA1, SA2, SFT, GA2, GFT. unfold est_set_bw. rewrite Pe_arr2, Pe_ftab.
    split; [exact ZA1|]. split; [| split; [exact W3|]].
    - apply lay_zbits_zbok; [exact Z2|]. rewrite EBW. apply (proj1 (cb_trailer_zbok il _ _ SZ)).
    - intros ->. rewrite EBW, cb_trailer_false. exact SZ.
  Qed.
End Blk.
End BZPS.
