(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_List.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Pres3 MI_WFree2 MI_WAMeta MI_WAMeta2 MI_WTry2 MI_WSlot MI_TF2 MI_Bits.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Tree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_List OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WFree2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WTry2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_TF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gm (st : mstate) (b : aptr) : optr := match s_groups st !! b with Some h => g_meta h | None => None end.

Record PF (st st' : mstate) : Prop := mkPF {
  pf_cnt : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st);
  pf_geo : forall x, geo_of (MR st' x) = geo_of (MR st x);
  pf_gm : forall b, gm st' b = gm st b;
  pf_regions : s_regions st' = s_regions st;
  pf_slots : s_slots st' = s_slots st;
  pf_usage : forall sc, usage st' sc = usage st sc
}.

Lemma PF_refl st : PF st st. Proof. constructor; reflexivity. Qed.
Lemma PF_trans a b c : PF a b -> PF b c -> PF a c.
Proof. intros [A1 A2 A3 A4 A5 A6] [B1 B2 B3 B4 B5 B6]; constructor; intros; congruence. Qed.

Lemma geo_set_avail v r : geo_of (m_set_avail v r) = geo_of r. Proof. destruct r; reflexivity. Qed.
Lemma geo_set_freed v r : geo_of (m_set_freed v r) = geo_of r. Proof. destruct r; reflexivity. Qed.
Lemma geo_set_prev v r : geo_of (m_set_prev v r) = geo_of r. Proof. destruct r; reflexivity. Qed.
Lemma geo_set_next v r : geo_of (m_set_next v r) = geo_of r. Proof. destruct r; reflexivity. Qed.

Lemma PF_upd_meta st m f : (forall r, geo_of (f r) = geo_of r) -> PF st (upd_meta m f st).
Proof.
  intros Hf. constructor; try reflexivity.
  intros x. unfold MR. destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite get_meta_rec_upd_same. apply Hf.
  - rewrite get_meta_rec_upd_other by exact NE. reflexivity.
Qed.

Lemma PF_upd_ctx st f :
  c_avail_meta_count (f (s_ctx st)) = c_avail_meta_count (s_ctx st) ->
  c_usage (f (s_ctx st)) = c_usage (s_ctx st) ->
  PF st (upd_ctx f st).
Proof. intros H1 H2. constructor; try reflexivity; [exact H1|]. intros sc. unfold usage, ctx. cbn. rewrite H2. reflexivity. Qed.

Lemma PF_set_active st sc v : PF st (set_active sc v st).
Proof. unfold set_active. apply PF_upd_ctx; reflexivity. Qed.

Lemma PF_set_head st h v : PF st (set_head h v st).
Proof. destruct h; [apply PF_set_active| unfold set_head; apply PF_upd_ctx; reflexivity]. Qed.

Lemma PF_set_bounce st i v : PF st (set_bounce i v st).
Proof. unfold set_bounce. apply PF_upd_ctx; reflexivity. Qed.

Lemma PF_decay_bounces st sc : PF st (decay_bounces sc st).
Proof. unfold decay_bounces. destruct (_ && _); [apply PF_set_bounce| apply PF_refl]. Qed.

Lemma PF_set_group_active_idx st g ai : PF st (set_group_active_idx g ai st).
Proof.
  unfold set_group_active_idx. destruct (get_group st g) as [h|] eqn:E; [| apply PF_refl].
  constructor; try reflexivity. intros b. unfold gm. cbn.
  destruct (aptr_eq_dec b g) as [->|NE].
  - rewrite lookup_insert_eq. unfold get_group in E. rewrite E. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma PF_dequeue st h m : PF st (dequeue h m st).
Proof.
  unfold dequeue. eapply PF_trans; [| apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity].
  destruct (negb _); [| apply PF_set_head].
  set (st1 := match m_prev _ with Some pv => _ | None => st end).
  assert (P1 : PF st st1) by (subst st1; destruct (m_prev _); [apply PF_upd_meta; intros; apply geo_set_next| apply PF_refl]).
  set (st2 := match m_next _ with Some nx => _ | None => st1 end).
  assert (P2 : PF st st2) by (subst st2; destruct (m_next _); [eapply PF_trans; [exact P1| apply PF_upd_meta; intros; apply geo_set_prev]| exact P1]).
  destruct (optr_eqb _ _); [eapply PF_trans; [exact P2| apply PF_set_head]| exact P2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition UBT {T} (t : M T) : Prop := exists w K, t = SVis (EUndef w) K.
End ACeilS1.


Ltac pair_eq E := let A := fresh in let B := fresh in pose proof (f_equal fst E) as A; pose proof (f_equal snd E) as B; cbn [fst snd] in A, B; subst.
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ZC (sc : Z) (st : mstate) : Prop :=
  active st sc = None \/ exists m, active st sc = Some m /\ m_avail (get_meta_rec st m) = 0 /\ m_freed (get_meta_rec st m) = 0.

Lemma lowbit_nz m : m <> 0 -> lowbit m <> 0.
Proof.
  intros Hm. destruct (Z.lt_ge_cases m 0) as [N|P].
  - cps_destruct (lowbit_nonzero (- m) ltac:(lia)) as (k & Hk & E & _).
    unfold lowbit in *. rewrite Z.opp_involutive, Z.land_comm in E. rewrite E. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia.
  - cps_destruct (lowbit_nonzero m ltac:(lia)) as (k & Hk & E & _). rewrite E. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia.
Qed.

Lemma try_avail_cases sc st :
  (exists st1 f, PF st st1 /\ ((f = 0 /\ ZC sc st) \/ f <> 0) /\ forall T (k : mstate -> Z -> M T) bail, try_avail sc st k bail = k st1 f)
  \/ (forall T (k : mstate -> Z -> M T) bail, UBT (try_avail sc st k bail)).
Proof.
  unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ left. exists st, 0. split; [apply PF_refl|]. split; [left; split; [reflexivity| left; exact HA]| intros; reflexivity]. }
  destruct (negb (m_avail (get_meta_rec st m) =? 0)) eqn:EA.
  { left. unfold ta_fin. eexists _, _. split; [apply PF_upd_meta; intros; apply geo_set_avail|].
    split; [right; apply lowbit_nz; apply negb_true_iff in EA; apply Z.eqb_neq in EA; exact EA| intros; reflexivity]. }
  apply negb_false_iff in EA. apply Z.eqb_eq in EA.
  set (step1 := if m_freed (get_meta_rec st m) =? 0 then _ else _).
  destruct step1 as [[st1 m1]|] eqn:E1.
  2:{ destruct (m_freed (get_meta_rec st m) =? 0) eqn:EF.
      - left. eexists _, 0. split; [apply PF_dequeue|]. split; [| intros; reflexivity].
        left. split; [reflexivity|]. right. exists m. apply Z.eqb_eq in EF. auto.
      - right. intros. eexists _, _. reflexivity. }
  assert (P1 : PF st st1).
  { subst step1. destruct (m_freed (get_meta_rec st m) =? 0).
    - destruct (active (dequeue (LActive sc) m st) sc); [| discriminate]. injection E1 as <- <-. apply PF_dequeue.
    - destruct (m_next (get_meta_rec st m)); [| discriminate]. injection E1 as <- <-. apply PF_set_active. }
  cbn zeta.
  set (p2 := if (m_freed (get_meta_rec st1 m1) =? mask_upto _) && _ then _ else _).
  destruct p2 as [[st2 m2] mask] eqn:E2.
  assert (P2 : PF st st2).
  { subst p2. destruct (_ && _).
    - destruct (m_next (get_meta_rec st1 m1)); injection E2 as <- <- <-; [eapply PF_trans; [exact P1| apply PF_set_active]| exact P1].
    - injection E2 as <- <- <-. exact P1. }
  set (p3 := if Z.land mask _ =? 0 then _ else _).
  destruct p3 as [st3 m3] eqn:E3.
  assert (P3 : PF st st3).
  { subst p3. destruct (Z.land mask _ =? 0).
    - destruct (negb (optr_eqb _ _)).
      + destruct (m_next (get_meta_rec st2 m2)).
        * injection E3 as <- <-. eapply PF_trans. exact P2. apply PF_set_active.
        * injection E3 as <- <-. exact P2.
      + destruct (m_mem (get_meta_rec st2 m2)).
        * pair_eq E3. eapply PF_trans. exact P2. apply PF_set_group_active_idx.
        * injection E3 as <- <-. exact P2.
    - injection E3 as <- <-. exact P2. }
  clearbody p3. clear E3.
  unfold activate_group, guard.
  destruct (m_avail (get_meta_rec st3 m3) =? 0).
  2:{ right. intros. eexists _, _. reflexivity. }
  cbn beta.
  match goal with |- context [negb (?mk =? 0)] => destruct (negb (mk =? 0)) eqn:EM end.
  - left. unfold ta_fin. eexists _, _. split.
    2:{ split; [right; apply lowbit_nz; apply negb_true_iff in EM; apply Z.eqb_neq in EM; exact EM|]. intros. reflexivity. }
    eapply PF_trans. exact P3. eapply PF_trans. { apply PF_upd_meta. intros r. rewrite geo_set_avail, geo_set_freed. reflexivity. }
    eapply PF_trans. apply PF_decay_bounces. apply PF_upd_meta. intros; apply geo_set_avail.
  - right. intros. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma try_avail_okC X L BL sc st LS :
  x_pend X = None -> x_fresh X = None -> 0 <= sc < 48 -> INVL X st L BL LS ->
  exists st1 first LS1,
    (forall T (k : mstate -> Z -> M T) bail, try_avail sc st k bail = k st1 first)
    /\ TA_POST X L BL sc st st1 first LS1 /\ PF st st1 /\ ((first = 0 /\ ZC sc st) \/ first <> 0).
Proof.
  intros HP HF Hsc INV.
  destruct (try_avail_cases sc st) as [(st1 & f & P & Z0 & E)|U].
  - cps_destruct (try_avail_ok (mstate * Z) X L BL sc (fun s z => SRet (s, z)) (SRet (st, 0)) HP HF Hsc st LS INV) as (st1' & first & LS1 & E' & POST).
    rewrite E in E'. inversion E'; subst. exists st1', first, LS1. auto.
  - exfalso. cps_destruct (try_avail_ok (mstate * Z) X L BL sc (fun s z => SRet (s, z)) (SRet (st, 0)) HP HF Hsc st LS INV) as (st1' & first & LS1 & E' & POST).
    cps_destruct (U (mstate * Z)%type (fun s z => SRet (s, z)) (SRet (st, 0))) as (w & K & EU). rewrite EU in E'. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record PF1 (st st' : mstate) : Prop := mkPF1 {
  pf1_cnt : c_avail_meta_count (s_ctx st') >= c_avail_meta_count (s_ctx st) - 1;
  pf1_geo : forall x, geo_of (MR st' x) = geo_of (MR st x);
  pf1_gm : forall b, gm st' b = gm st b;
  pf1_regions : s_regions st' = s_regions st;
  pf1_slots : s_slots st' = s_slots st;
  pf1_usage : forall sc, usage st' sc = usage st sc
}.

Lemma PF_PF1 st st' : PF st st' -> PF1 st st'.
Proof. intros [A B C D E F]; constructor; auto. rewrite A. lia. Qed.
Lemma PF1_trans_l a b c : PF a b -> PF1 b c -> PF1 a c.
Proof. intros [A1 A2 A3 A4 A5 A6] [B1 B2 B3 B4 B5 B6]; constructor; intros; first [lia| congruence]. Qed.
Lemma PF1_trans_r a b c : PF1 a b -> PF b c -> PF1 a c.
Proof. intros [A1 A2 A3 A4 A5 A6] [B1 B2 B3 B4 B5 B6]; constructor; intros; first [lia| congruence]. Qed.

Lemma PF_am_init st : PF st (am_init st).
Proof. unfold am_init. destruct (_ =? 0); [apply PF_upd_ctx; reflexivity| apply PF_refl]. Qed.

Lemma alloc_meta_cases st :
  0 < c_avail_meta_count (s_ctx st) ->
  (exists st1 m, PF1 st st1 /\ forall T (k : mstate -> optr -> M T) bail, alloc_meta st k bail = k st1 (Some m))
  \/ (forall T (k : mstate -> optr -> M T) bail, UBT (alloc_meta st k bail)).
Proof.
  intros HC. unfold alloc_meta. fold (am_init st).
  pose proof (PF_am_init st) as P0. set (s := am_init st) in *. clearbody s.
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { left. eexists _, m. split; [| intros; reflexivity]. apply PF_PF1. eapply PF_trans; [exact P0| apply PF_dequeue]. }
  assert (HC' : (c_avail_meta_count (ctx s) =? 0) = false) by (apply Z.eqb_neq; unfold ctx; rewrite (pf_cnt _ _ P0); lia).
  rewrite HC'. cbn [negb].
  unfold am_take. destruct (c_avail_meta (ctx s)) as [p|] eqn:EAM.
  - left. eexists _, p. split; [| intros; reflexivity].
    eapply PF1_trans_l; [exact P0|]. eapply PF1_trans_r; [| apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity].
    constructor; intros; try reflexivity. cbn. lia.
  - right. intros. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_meta_okC X st L BL LS :
  INVL X st L BL LS -> 0 < c_avail_meta_count (s_ctx st) ->
  exists st1 m LS1,
    (forall T (k : mstate -> optr -> M T) bail, alloc_meta st k bail = k st1 (Some m))
    /\ PF1 st st1
    /\ INVL (xidle X (m :: x_idle X)) st1 L BL LS1 /\ ~ In m (x_idle X) /\ AM_frame st st1.
Proof.
  intros INV HC.
  set (Post := fun (L1 : mled) (r : mstate * optr) =>
     match snd r with
     | Some m => exists LS1, INVL (xidle X (m :: x_idle X)) (fst r) L1 BL LS1 /\ ~ In m (x_idle X) /\ AM_frame st (fst r)
     | None => True
     end).
  assert (FT : ftree L (alloc_meta st (fun s mo => SRet (s, mo)) (SRet (st, @None aptr))) Post).
  { apply (alloc_meta_ft (mstate * optr) BL Post (fun s mo => SRet (s, mo)) (SRet (st, None)) X st L) with (LS := LS).
    - intros st1 L1 LS1 _ _ _. exact I.
    - intros st1 L1 LS1 m INV1 NI AF LF. cbn. exists LS1. auto.
    - exact INV.
    - apply amf_refl.
    - apply lf_refl. }
  destruct (alloc_meta_cases st HC) as [(st1 & m & P & E)|U].
  - rewrite E in FT. cbn in FT. cps_destruct FT as (LS1 & INV1 & NI & AF). exists st1, m, LS1. auto.
  - exfalso. cps_destruct (U _ (fun s mo => SRet (s, mo)) (SRet (st, None))) as (w & K & EU). rewrite EU in FT. exact FT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fm_st_facts st m :
  (forall x, x <> m -> geo_of (MR (fm_st st m) x) = geo_of (MR st x))
  /\ c_avail_meta_count (s_ctx (fm_st st m)) = c_avail_meta_count (s_ctx st)
  /\ (forall b, gm (fm_st st m) b = gm st b) /\ s_regions (fm_st st m) = s_regions st
  /\ s_slots (fm_st st m) = s_slots st /\ (forall sc, usage (fm_st st m) sc = usage st sc)
  /\ (forall sc, active (fm_st st m) sc = active st sc).
Proof.
  unfold fm_st, queue_st, q_link, q_single.
  set (st0 := put_meta m meta0 st).
  assert (G0 : forall x, x <> m -> geo_of (MR st0 x) = geo_of (MR st x)).
  { intros x NE. unfold st0, MR. rewrite get_meta_rec_put_other by exact NE. reflexivity. }
  assert (P : forall st', PF st0 st' ->
    (forall x, x <> m -> geo_of (MR st' x) = geo_of (MR st x))
    /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
    /\ (forall b, gm st' b = gm st b) /\ s_regions st' = s_regions st
    /\ s_slots st' = s_slots st /\ (forall sc, usage st' sc = usage st sc)).
  { intros st' [A B C D E F]. repeat split; auto. intros x NE. rewrite B. apply G0. exact NE. }
  destruct (get_head st0 LFree) as [hd|] eqn:EH.
  - match goal with |- context [upd_meta hd ?f ?s2] => set (st' := upd_meta hd f s2) end.
    assert (PP : PF st0 st').
    { subst st'. destruct (m_prev (get_meta_rec st0 hd)).
      - eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity|].
        eapply PF_trans; [apply PF_upd_meta; intros; apply geo_set_next| apply PF_upd_meta; intros; apply geo_set_prev].
      - eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity|].
        apply PF_upd_meta; intros; apply geo_set_prev. }
    cps_destruct (P st' PP) as (A & B & C & D & E & F). repeat split; auto.
    all: intros sc; subst st'; rewrite !active_upd_meta; destruct (m_prev (get_meta_rec st0 hd)); rewrite ?active_upd_meta; reflexivity.
  - match goal with |- context [set_head LFree ?v ?s2] => set (st' := set_head LFree v s2) end.
    assert (PP : PF st0 st').
    { subst st'. eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity| apply PF_set_head]. }
    cps_destruct (P st' PP) as (A & B & C & D & E & F). repeat split; auto.
    all: intros sc; subst st'; cbn [set_head]; unfold active, ctx; cbn; reflexivity.
Qed.

End ACeilS2.
