(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF BzCFactsGm.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_grow_S : forall f mf tFreq A ge aFreq,
  sm_grow (S f) mf tFreq A ge aFreq =
  (if (aFreq <? tFreq) && (ge <? A - 1) then sm_grow f mf tFreq A (ge + 1) (aFreq + zget mf (ge + 1)) else (ge, aFreq)).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sm_init_tables_S : forall f mf nG A s,
  sm_init_tables (S f) mf nG A s = (if 0 <? ip_nPart s then sm_init_tables f mf nG A (sm_init_iter mf nG A s) else s).
Proof. reflexivity. Qed.
Lemma sm_setrow_S : forall n len t gs ge v,
  sm_setrow (S n) len t gs ge v = sm_setrow n (zset len (258 * t + v) (if (gs <=? v) && (v <=? ge) then BZ_LESSER_ICOST else BZ_GREATER_ICOST)) t gs ge (v + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma iter_succ : forall {X : Type} (n : nat) (f : X -> X) (x : X), Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sm_init_iter_eq : forall mf nG A s,
  sm_init_iter mf nG A s =
  (let nPart := ip_nPart s in let gs := ip_gs s in let remF := ip_remF s in
   let r := sm_grow 260 mf (remF / nPart) A (gs - 1) 0 in
   let adj := (gs <? fst r) && negb (nPart =? nG) && negb (nPart =? 1) && ((nG - nPart) mod 2 =? 1) in
   let ge' := if adj then fst r - 1 else fst r in let aFreq' := if adj then snd r - zget mf (fst r) else snd r in
   SIP (sm_setrow (Z.to_nat A) (ip_len s) (nPart - 1) gs ge' 0) (nPart - 1) (remF - aFreq') (ge' + 1)).
Proof.
  intros mf nG A s. unfold sm_init_iter. destruct (sm_grow 260 _ _ _ _ _) as [ge aFreq]. cbn [fst snd].
  destruct ((ip_gs s <? ge) && negb (ip_nPart s =? nG) && negb (ip_nPart s =? 1) && ((nG - ip_nPart s) mod 2 =? 1)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sumF_app : forall g j n m, sumF g j (n + m) = sumF g j n + sumF g (j + Z.of_nat n) m.
Proof.
  intros g j n. revert j. induction n as [|n IH]; intros j m; cbn [sumF Nat.add].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. replace (j + 1 + Z.of_nat n) with (j + Z.of_nat (S n)) by lia. lia.
Qed.
Lemma sumF_le_total : forall g j n m, (n <= m)%nat -> (forall b, j <= b < j + Z.of_nat m -> 0 <= g b) -> 0 <= sumF g j n <= sumF g j m.
Proof.
  intros g j n m Hnm NN. replace m with (n + (m - n))%nat by lia. rewrite sumF_app.
  pose proof (sumF_nonneg n g j ltac:(intros; apply NN; lia)).
  pose proof (sumF_nonneg (m - n) g (j + Z.of_nat n) ltac:(intros; apply NN; lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_setrow_spec : forall n len t gs ge v0,
  (forall v, v0 <= v < v0 + Z.of_nat n ->
     zget (sm_setrow n len t gs ge v0) (258 * t + v) = (if (gs <=? v) && (v <=? ge) then BZ_LESSER_ICOST else BZ_GREATER_ICOST) /\
     zdef (sm_setrow n len t gs ge v0) (258 * t + v) = true) /\
  (forall x, (x < 258 * t + v0 \/ 258 * t + v0 + Z.of_nat n <= x) ->
     zget (sm_setrow n len t gs ge v0) x = zget len x /\ zdef (sm_setrow n len t gs ge v0) x = zdef len x).
Proof.
  induction n as [|n IH]; intros len t gs ge v0.
  - cbn [sm_setrow]. split; [intros; lia| intros; split; reflexivity].
  - rewrite sm_setrow_S. destruct (IH (zset len (258 * t + v0) (if (gs <=? v0) && (v0 <=? ge) then BZ_LESSER_ICOST else BZ_GREATER_ICOST)) t gs ge (v0 + 1)) as [V F].
    split.
    + intros v Hv. destruct (Z.eq_dec v v0) as [->|NE].
      * destruct (F (258 * t + v0) ltac:(lia)) as [F1 F2]. rewrite F1, F2, zget_zset_same, zdef_zset_same. split; reflexivity.
      * apply V. lia.
    + intros x Hx. destruct (F x ltac:(lia)) as [F1 F2]. rewrite F1, F2, zget_zset_other, zdef_zset_other by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Init.
  Variables (mf : zarr) (A nG nMTF : Z).
  Hypothesis HA : 3 <= A <= 258.
  Hypothesis HG : 2 <= nG <= 6.
  Hypothesis MF : forall v, 0 <= v < A -> 0 <= zget mf v.
  Hypothesis SUM : sumF (fun v => zget mf v) 0 (Z.to_nat A) = nMTF.

  Local Notation g := (fun v : Z => zget mf v).

  Lemma nMTF_nonneg : 0 <= nMTF.
  Proof. rewrite <- SUM. apply sumF_nonneg. intros; apply MF; lia. Qed.

  (* [comment removed for export] *)
  Lemma part_le : forall gs n, 0 <= gs -> gs + Z.of_nat n <= A -> 0 <= sumF g gs n <= nMTF.
  Proof.
    intros gs n Hgs Hn. rewrite <- SUM.
    replace (Z.to_nat A) with (Z.to_nat gs + (n + (Z.to_nat A - Z.to_nat gs - n)))%nat by lia.
    rewrite sumF_app, sumF_app. replace (0 + Z.of_nat (Z.to_nat gs)) with gs by lia.
    pose proof (sumF_nonneg (Z.to_nat gs) g 0 ltac:(intros; apply MF; lia)).
    pose proof (sumF_nonneg n g gs ltac:(intros; apply MF; lia)).
    pose proof (sumF_nonneg (Z.to_nat A - Z.to_nat gs - n) g (gs + Z.of_nat n) ltac:(intros; apply MF; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition GRI (gs remF ge aFreq : Z) : Prop :=
    gs - 1 <= ge <= A - 1 /\ aFreq = sumF g gs (Z.to_nat (ge - gs + 1)) /\ 0 <= aFreq <= remF.

  Section Grow.
    Variables (gs remF : Z).
    Hypothesis GS : 0 <= gs <= A.
    Hypothesis RM : remF = sumF g gs (Z.to_nat (A - gs)).

    Lemma GRI_init : GRI gs remF (gs - 1) 0.
    Proof.
      unfold GRI. replace (Z.to_nat (gs - 1 - gs + 1)) with 0%nat by lia. cbn [sumF].
      pose proof (part_le gs (Z.to_nat (A - gs)) ltac:(lia) ltac:(lia)). rewrite <- RM in H. lia.
    Qed.

    Lemma GRI_step : forall ge aFreq, GRI gs remF ge aFreq -> ge < A - 1 ->
      0 <= ge + 1 < A /\ GRI gs remF (ge + 1) (aFreq + zget mf (ge + 1)).
    Proof.
      (intros ge aFreq; cps_intros (R1 & R2 & R3); intros LT). split; [lia|]. unfold GRI. split; [lia|].
      assert (E : aFreq + zget mf (ge + 1) = sumF g gs (Z.to_nat (ge + 1 - gs + 1))).
      { replace (Z.to_nat (ge + 1 - gs + 1)) with (Z.to_nat (ge - gs + 1) + 1)%nat by lia.
        rewrite sumF_app. cbn [sumF]. replace (gs + Z.of_nat (Z.to_nat (ge - gs + 1))) with (ge + 1) by lia. cbv beta. lia. }
      split; [exact E|]. rewrite E, RM.
      apply sumF_le_total; [lia|]. intros b Hb. apply MF. lia.
    Qed.

    Lemma GRI_shrink : forall ge aFreq, GRI gs remF ge aFreq -> gs <= ge -> GRI gs remF (ge - 1) (aFreq - zget mf ge).
    Proof.
      (intros ge aFreq; cps_intros (R1 & R2 & R3); intros LE). unfold GRI. split; [lia|].
      assert (E : aFreq - zget mf ge = sumF g gs (Z.to_nat (ge - 1 - gs + 1))).
      { rewrite R2. replace (Z.to_nat (ge - gs + 1)) with (Z.to_nat (ge - 1 - gs + 1) + 1)%nat by lia.
        rewrite sumF_app. cbn [sumF]. replace (gs + Z.of_nat (Z.to_nat (ge - 1 - gs + 1))) with ge by lia. cbv beta. lia. }
      split; [exact E|]. rewrite E, RM. apply sumF_le_total; [lia|]. intros b Hb. apply MF. lia.
    Qed.

    Lemma sm_grow_GRI : forall f tFreq ge aFreq, GRI gs remF ge aFreq -> A - 1 - ge < Z.of_nat f ->
      let r := sm_grow f mf tFreq A ge aFreq in
      GRI gs remF (fst r) (snd r) /\ ((snd r <? tFreq) && (fst r <? A - 1)) = false.
    Proof.
      induction f as [|f IH]; intros tFreq ge aFreq GR Hf; cbv zeta; [destruct GR; cbn in Hf; lia|].
      rewrite sm_grow_S. destruct ((aFreq <? tFreq) && (ge <? A - 1)) eqn:C.
      - apply andb_prop in C. destruct C as [_ C2]. apply Z.ltb_lt in C2.
        destruct (GRI_step ge aFreq GR C2) as [_ GR']. apply IH; [exact GR'| lia].
      - cbn [fst snd]. split; [exact GR| exact C].
    Qed.
  End Grow.

  (* [comment removed for export] *)
  Definition OI (k : Z) (s : sip) : Prop :=
    0 <= k /\ ip_nPart s = nG - k /\ 0 <= ip_gs s <= A /\ ip_remF s = sumF g (ip_gs s) (Z.to_nat (A - ip_gs s)) /\ 0 <= ip_remF s <= nMTF.

  Lemma OI_0 : forall len0, OI 0 (SIP len0 nG nMTF 0).
  Proof.
    intros len0. unfold OI; cbn [ip_nPart ip_gs ip_remF]. pose proof nMTF_nonneg.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [| lia]. replace (A - 0) with A by lia. symmetry. exact SUM.
  Qed.

  (* [comment removed for export] *)
  Lemma OI_step : forall k s, OI k s -> k < nG ->
    let nPart := ip_nPart s in let gs := ip_gs s in let remF := ip_remF s in
    let tFreq := remF / nPart in
    let r := sm_grow 260 mf tFreq A (gs - 1) 0 in
    let ge := fst r in let aFreq := snd r in
    let adj := (gs <? ge) && negb (nPart =? nG) && negb (nPart =? 1) && ((nG - nPart) mod 2 =? 1) in
    let ge' := if adj then ge - 1 else ge in let aFreq' := if adj then aFreq - zget mf ge else aFreq in
    1 <= nPart <= nG /\ 0 <= tFreq <= nMTF /\
    GRI gs remF ge aFreq /\ GRI gs remF ge' aFreq' /\ (adj = true -> gs <= ge /\ 0 <= ge < A) /\
    sm_init_iter mf nG A s = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nPart - 1) gs ge' 0) (nPart - 1) (remF - aFreq') (ge' + 1) /\
    OI (k + 1) (sm_init_iter mf nG A s).
  Proof.
    (intros k s; cps_intros (K0 & O1 & O2 & O3 & O4); intros Hk). cbv zeta.
    set (nPart := ip_nPart s) in *. set (gs := ip_gs s) in *. set (remF := ip_remF s) in *.
    assert (NP : 1 <= nPart <= nG) by lia.
    assert (TF : 0 <= remF / nPart <= nMTF).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
    pose proof (sm_grow_GRI gs remF ltac:(lia) O3 260 (remF / nPart) (gs - 1) 0 (GRI_init gs remF ltac:(lia) O3) ltac:(cbn; lia)) as GG.
    cbv zeta in GG. destruct GG as [GR EX].
    set (r := sm_grow 260 mf (remF / nPart) A (gs - 1) 0) in *.
    set (adj := (gs <? fst r) && negb (nPart =? nG) && negb (nPart =? 1) && ((nG - nPart) mod 2 =? 1)).
    assert (ADJ : adj = true -> gs <= fst r /\ 0 <= fst r < A).
    { intros E. subst adj. apply andb_prop in E. destruct E as [E _]. apply andb_prop in E. destruct E as [E _]. apply andb_prop in E. destruct E as [E _].
      apply Z.ltb_lt in E. destruct GR as (R1 & _). lia. }
    assert (GR' : GRI gs remF (if adj then fst r - 1 else fst r) (if adj then snd r - zget mf (fst r) else snd r)).
    { destruct adj eqn:EA; [| exact GR]. apply GRI_shrink; [lia| exact O3| exact GR| ]. destruct (ADJ eq_refl); lia. }
    assert (EQ : sm_init_iter mf nG A s = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nPart - 1) gs (if adj then fst r - 1 else fst r) 0) (nPart - 1)
                   (remF - (if adj then snd r - zget mf (fst r) else snd r)) ((if adj then fst r - 1 else fst r) + 1)).
    { rewrite sm_init_iter_eq. reflexivity. }
    split; [exact NP|]. split; [exact TF|]. split; [exact GR|]. split; [exact GR'|]. split; [exact ADJ|]. split; [exact EQ|].
    rewrite EQ. unfold OI; cbn [ip_nPart ip_gs ip_remF].
    cps_destruct GR' as (Q1 & Q2 & Q3). set (ge' := if adj then fst r - 1 else fst r) in *. set (af' := if adj then snd r - zget mf (fst r) else snd r) in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    assert (RS : remF - af' = sumF g (ge' + 1) (Z.to_nat (A - (ge' + 1)))).
    { rewrite O3, Q2. fold gs. replace (Z.to_nat (A - gs)) with (Z.to_nat (ge' - gs + 1) + Z.to_nat (A - (ge' + 1)))%nat by lia.
      rewrite sumF_app. replace (gs + Z.of_nat (Z.to_nat (ge' - gs + 1))) with (ge' + 1) by lia. lia. }
    split; [exact RS|]. rewrite RS. apply part_le; lia.
  Qed.

  Lemma OI_iter : forall (k : nat) len0, Z.of_nat k <= nG -> OI (Z.of_nat k) (Nat.iter k (sm_init_iter mf nG A) (SIP len0 nG nMTF 0)).
  Proof.
    induction k as [|k IH]; intros len0 Hk; [apply OI_0|].
    rewrite iter_succ.
    pose proof (OI_step (Z.of_nat k) _ (IH len0 ltac:(lia)) ltac:(lia)) as ST. cbv zeta in ST.
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. apply ST.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_init_tables_run : forall f (k : nat) len0, Z.of_nat k <= nG -> (Z.to_nat nG - k <= f)%nat ->
    sm_init_tables f mf nG A (Nat.iter k (sm_init_iter mf nG A) (SIP len0 nG nMTF 0)) =
    Nat.iter (Z.to_nat nG) (sm_init_iter mf nG A) (SIP len0 nG nMTF 0).
  Proof.
    induction f as [|f IH]; intros k len0 Hk Hf.
    - cbn [sm_init_tables]. replace k with (Z.to_nat nG) by lia. reflexivity.
    - rewrite sm_init_tables_S. cps_pose (OI_iter k len0 Hk) as (_ & O1 & _).
      destruct (Z.ltb_spec 0 (ip_nPart (Nat.iter k (sm_init_iter mf nG A) (SIP len0 nG nMTF 0)))) as [P|NP].
      + rewrite <- (iter_succ k (sm_init_iter mf nG A)). apply IH; lia.
      + replace k with (Z.to_nat nG) by lia. reflexivity.
  Qed.

  Theorem sm_init_tables_iter : forall len0,
    sm_init_tables 8%nat mf nG A (SIP len0 nG nMTF 0) = Nat.iter (Z.to_nat nG) (sm_init_iter mf nG A) (SIP len0 nG nMTF 0).
  Proof. intros len0. exact (sm_init_tables_run 8 0 len0 ltac:(lia) ltac:(lia)). Qed.
End Init.
