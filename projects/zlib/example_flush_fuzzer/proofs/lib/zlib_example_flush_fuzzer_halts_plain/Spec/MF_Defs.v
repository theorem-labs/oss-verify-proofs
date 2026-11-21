(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Malloc MI_Inv MI_Kit MI_WTry2 MI_WSlot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition KCLS (c : Z) : Prop := c = 31 \/ c = 40 \/ c = 44.
Definition NEWC (sc c : Z) : Prop := c = sc \/ c = 15 \/ c = 19 \/ c = 23.
Definition OLD (st st2 : mstate) (b m : aptr) : Prop :=
  (exists ai0, s_groups st !! b = Some (mkGhdr (Some m) ai0)) /\ same_geo (MR st2 m) (MR st m).

Record MFR (sc : Z) (st st2 : mstate) : Prop := mkMFR {
  mfr_old : forall b m ai, s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> OLD st st2 b m \/ NEWC sc (m_sizeclass (MR st2 m));
  mfr_bnc : (sc = 31 -> bounces st 24 <= 98) -> bounces st2 24 <= bounces st 24 + (if sc =? 31 then 1 else 0)
}.

Definition KPRE (sc req u : Z) : Prop :=
  (sc = 31 -> u <= 7) /\ (sc = 40 -> u <= 55 /\ (36844 < req -> u <= 5)) /\ (sc = 44 -> u <= 55 /\ (73708 < req -> u <= 5)).

Definition KNEW (st st2 : mstate) (g bg : aptr) : Prop :=
  m_last_idx (MR st2 g) = 0 /\ s_regions st !! (fst bg) = None /\ snd bg = 0 /\ gonly0 st2 (fst bg)
  /\ (forall b m ai, s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> b <> bg -> OLD st st2 b m).

Definition XNEW (sc req : Z) (st st2 : mstate) (g bg : aptr) : Prop :=
  KCLS sc -> KPRE sc req (usage st sc) -> bounces st 24 <= 99 -> OLD st st2 bg g \/ KNEW st st2 g bg.


Lemma OLD_refl st b m ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> OLD st st b m.
Proof. intros H. split; [exists ai; exact H| apply same_geo_refl]. Qed.


Lemma MFR_refl sc st : MFR sc st st.
Proof. constructor; [intros b m ai H; left; exact (OLD_refl _ _ _ _ H)| destruct (sc =? 31); lia]. Qed.

Lemma MFR_trans sc a b c : MFR sc a b -> MFR sc b c -> (bounces b 24 <= bounces a 24 \/ bounces c 24 <= bounces b 24) -> MFR sc a c.
Proof.
  intros [O1 B1] [O2 B2] HB. constructor.
  - intros bb m ai H. destruct (O2 _ _ _ H) as [[[ai1 H1] G]|N]; [| right; exact N].
    destruct (O1 _ _ _ H1) as [[E G0]|N]; [left; split; [exact E| exact (same_geo_trans _ _ _ G G0)]|].
    right. destruct G as (_ & _ & _ & E). rewrite E. exact N.
  - intros H98. destruct (Z.eqb_spec sc 31) as [E|NE].
    + specialize (B1 ltac:(intros; apply H98; exact E)). destruct HB as [HB|HB]; [specialize (B2 ltac:(intros; lia)); lia| lia].
    + specialize (B1 ltac:(intros; congruence)). specialize (B2 ltac:(intros; congruence)). lia.
Qed.

Definition MF0 (st st2 : mstate) : Prop :=
  (forall b m ai, s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> OLD st st2 b m) /\ bounces st2 24 <= bounces st 24.
Lemma MF0_MFR sc st st2 : MF0 st st2 -> MFR sc st st2.
Proof. intros [O B]. constructor; [intros b m ai H; left; exact (O _ _ _ H)| destruct (sc =? 31); lia]. Qed.
Lemma MFR_MF0_l sc a b c : MF0 a b -> MFR sc b c -> MFR sc a c.
Proof. intros H M. apply (MFR_trans sc a b c (MF0_MFR sc _ _ H) M). left. exact (proj2 H). Qed.
Lemma MFR_MF0_r sc a b c : MFR sc a b -> MF0 b c -> MFR sc a c.
Proof. intros M H. apply (MFR_trans sc a b c M (MF0_MFR sc _ _ H)). right. exact (proj2 H). Qed.
Lemma MF0_trans a b c : MF0 a b -> MF0 b c -> MF0 a c.
Proof.
  intros [O1 B1] [O2 B2]. split; [| lia]. intros bb m ai H. destruct (O2 _ _ _ H) as [[ai1 H1] G]. destruct (O1 _ _ _ H1) as [E G0].
  split; [exact E| exact (same_geo_trans _ _ _ G G0)].
Qed.
Lemma MF0_of st st2 : (forall b h, s_groups st2 !! b = Some h -> exists h0, s_groups st !! b = Some h0 /\ g_meta h0 = g_meta h) ->
  (forall x, same_geo (MR st2 x) (MR st x)) -> bounces st2 24 <= bounces st 24 -> MF0 st st2.
Proof.
  intros G M B. split; [| exact B]. intros b m ai H. destruct (G _ _ H) as ([gm ga] & H0 & E). cbn in E. subst gm.
  split; [exists ga; exact H0| apply M].
Qed.
Lemma MF0_eq st st2 : s_groups st2 = s_groups st -> s_metas st2 = s_metas st -> c_bounces (s_ctx st2) = c_bounces (s_ctx st) -> MF0 st st2.
Proof.
  intros G M B. apply MF0_of; [intros b h H; rewrite G in H; exists h; auto| intros x; unfold MR, get_meta_rec; rewrite M; apply same_geo_refl| unfold bounces, ctx; rewrite B; lia].
Qed.
Lemma MF0_taf st st2 sc : TA_frame st st2 sc -> (forall i, bounces st2 i <= bounces st i) -> MF0 st st2.
Proof. intros TF B. apply MF0_of; [apply (taf_gmeta _ _ _ TF)| apply (taf_geo _ _ _ TF)| apply B]. Qed.

Lemma NEWC_host sc j c : (j = 15 \/ j = 19 \/ j = 23) -> NEWC j c -> NEWC sc c.
Proof. unfold NEWC. intros Hj [->|H]; [right; exact Hj| right; exact H]. Qed.
Lemma MFR_host sc j st st2 : (j = 15 \/ j = 19 \/ j = 23) -> MFR j st st2 -> MF0 st st2 \/ MFR sc st st2 /\ bounces st2 24 <= bounces st 24.
Proof.
  intros Hj [O B]. right.
  assert (NE : (j =? 31) = false) by (apply Z.eqb_neq; lia). rewrite NE in B. specialize (B ltac:(intros; lia)).
  split; [| lia]. constructor; [| destruct (sc =? 31); lia].
  intros b m ai H. destruct (O _ _ _ H) as [HO|N]; [left; exact HO| right; exact (NEWC_host sc j _ Hj N)].
Qed.

Lemma KCLS_range c : KCLS c -> 28 <= c < 48 /\ 9 <= c /\ Z.land c 3 <> 1 /\ Z.land c 3 <> 2.
Proof. intros [->|[->| ->]]; cbn; repeat split; try lia; discriminate. Qed.
