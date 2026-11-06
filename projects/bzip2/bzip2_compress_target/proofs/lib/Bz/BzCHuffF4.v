(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCHuff BzCPermF BzCRebuildF BzCHuffF1.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCHuff BzCPermF BzCRebuildF BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCHuffF2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Section Heap2.
  Variable w : zarr.
  Definition SENT (h : zarr) : Prop := zget h 0 = 0 /\ zget w 0 = 0.
  Definition KNN (h : zarr) (n : Z) : Prop := forall z, 1 <= z <= n -> 0 <= zget w (zget h z).

  Lemma div2_lt : forall e, 1 <= e -> e / 2 < e.
  Proof. intros. apply Z.div_lt_upper_bound; lia. Qed.
  Lemma div2_ge1 : forall e, 2 <= e -> 1 <= e / 2.
  Proof. intros. apply Z.div_le_lower_bound; lia. Qed.

  Lemma upheap_loop_spec : forall fuel h e tmp n,
    1 <= e <= n -> (e < 2 ^ Z.of_nat fuel) -> SENT h -> 0 <= zget w tmp -> KNN (zset h e tmp) n ->
    UI w (zset h e tmp) n e ->
    let r := upheap_loop fuel h w e tmp in
    let V := zset (fst r) (snd r) tmp in
    1 <= snd r <= e /\ HO w V n /\ (forall v, hcnt V n v = hcnt (zset h e tmp) n v) /\
    (forall z, (z < 1 \/ n < z) -> zget V z = zget h z) /\ KNN V n.
  Proof.
    induction fuel as [|fuel IH]; intros h e tmp n He Hf ST Kt KN U; cbn zeta; [cbn in Hf; lia|].
    cbn [upheap_loop]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    destruct U as [U1 U2]. unfold UI, HO in *.
    pose proof (div2_lt e ltac:(lia)) as DL.
    destruct (Z.ltb_spec (zget w tmp) (zget w (zget h (e / 2)))) as [LT|GE]; cycle 1.
    { cbn [fst snd]. split; [lia|]. split; [|split; [intros; reflexivity| split; [|exact KN]]].
      - intros z Hz. destruct (Z.eq_dec z e) as [->|NE]; [|apply U1; assumption].
        rewrite zget_zset_same. rewrite zget_zset_other by lia. exact GE.
      - intros z Hz. apply zget_zset_other. lia. }
    assert (E2 : 2 <= e).
    { destruct (Z.eq_dec e 1) as [->|]; [|lia]. exfalso. change (1/2) with 0 in LT. destruct ST as [S1 S2]. rewrite S1, S2 in LT. lia. }
    pose proof (div2_ge1 e E2) as DG.
    set (V := zset h e tmp) in *.
    assert (SW : forall z, zget (zset (zset h e (zget h (e / 2))) (e / 2) tmp) z = zget (zset (zset V (e / 2) (zget V e)) e (zget V (e / 2))) z).
    { intros z. subst V. rewrite !zget_zset. destruct (Z.eqb_spec z e), (Z.eqb_spec z (e/2)); subst; try reflexivity; try lia.
      - destruct (Z.eqb_spec (e/2) e); [lia|reflexivity].
      - rewrite Z.eqb_refl. reflexivity. }
    assert (VE : zget V e = tmp) by (subst V; apply zget_zset_same).
    assert (VO : forall z, z <> e -> zget V z = zget h z) by (intros; subst V; apply zget_zset_other; assumption).
    specialize (IH (zset h e (zget h (e / 2))) (e / 2) tmp n).
    cps_destruct IH as (A & B & C & D & E).
    - lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
    - destruct ST as [S1 S2]. split; [|exact S2]. rewrite zget_zset_other by lia. exact S1.
    - exact Kt.
    - intros z Hz. rewrite SW, !zget_zset.
      destruct (Z.eqb_spec z e) as [->|NZE]; [apply KN; lia|].
      destruct (Z.eqb_spec z (e/2)) as [->|NZP]; [rewrite VE; exact Kt| apply KN; lia].
    - (* [comment removed for export] *)
      assert (NZ : forall z, zget (zset (zset h e (zget h (e / 2))) (e / 2) tmp) z =
                             if z =? e then zget V (e/2) else if z =? e/2 then tmp else zget V z).
      { intros z. rewrite SW, !zget_zset, VE. reflexivity. }
      assert (P : zget w tmp < zget w (zget V (e/2))) by (rewrite VO by lia; exact LT).
      split.
      + intros z Hz Hne. rewrite !NZ.
        replace (z / 2 =? e / 2) with (z / 2 =? e / 2) by reflexivity.
        destruct (Z.eqb_spec z e) as [->|NZE].
        { replace (e / 2 =? e) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia. }
        destruct (Z.eqb_spec z (e/2)) as [->|NZP]; [congruence|].
        destruct (Z.eqb_spec (z/2) e) as [ZE|ZNE].
        { apply U2; [exact Hz| exact ZE| exact E2]. }
        destruct (Z.eqb_spec (z/2) (e/2)) as [ZP|ZNP].
        { pose proof (U1 z Hz NZE) as X. rewrite ZP in X. lia. }
        apply U1; [exact Hz| exact NZE].
      + intros c Hc Hce He2. rewrite !NZ.
        assert (GL : e/2/2 < e/2) by (apply Z.div_lt_upper_bound; lia).
        replace (e/2/2 =? e) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (e/2/2 =? e/2) with false by (symmetry; apply Z.eqb_neq; lia).
        pose proof (U1 (e/2) ltac:(lia) ltac:(lia)) as G1.
        destruct (Z.eqb_spec c e) as [->|NCE]; [exact G1|].
        destruct (Z.eqb_spec c (e/2)) as [->|NCP].
        { exfalso. assert (e/2/2 < e/2) by lia. rewrite Hce in *. lia. }
        pose proof (U1 c Hc NCE) as X. rewrite Hce in X. lia.
    - (* [comment removed for export] *)
      split; [lia|]. split; [exact B|]. split.
      + intros v. rewrite C. rewrite (hcnt_ext (zset (zset V (e / 2) (zget V e)) e (zget V (e / 2))) _ n v) by (intros; apply SW).
        apply hcnt_swap; lia.
      + split; [|exact E]. intros z Hz. rewrite D by exact Hz. rewrite zget_zset_other by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition DI (V : zarr) (n e : Z) : Prop :=
    (forall z, 2 <= z <= n -> z / 2 <> e -> zget w (zget V (z / 2)) <= zget w (zget V z)) /\
    (forall c, 2 <= c <= n -> c / 2 = e -> zget w (zget V (e / 2)) <= zget w (zget V c)).

  Lemma downheap_loop_spec : forall fuel h e tmp n,
    1 <= e <= n -> (n < e * 2 ^ Z.of_nat fuel) -> SENT h -> 0 <= zget w tmp -> KNN (zset h e tmp) n ->
    DI (zset h e tmp) n e ->
    let r := downheap_loop fuel h w n e tmp in
    let V := zset (fst r) (snd r) tmp in
    e <= snd r <= n /\ HO w V n /\ (forall v, hcnt V n v = hcnt (zset h e tmp) n v) /\
    (forall z, (z < 1 \/ n < z) -> zget V z = zget h z) /\ KNN V n.
  Proof.
    induction fuel as [|fuel IH]; intros h e tmp n He Hf ST Kt KN D; cbn zeta; [cbn in Hf; lia|].
    cbn [downheap_loop]. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    destruct D as [D1 D2]. unfold DI, HO in *.
    set (V := zset h e tmp) in *.
    assert (VE : zget V e = tmp) by (subst V; apply zget_zset_same).
    assert (VO : forall z, z <> e -> zget V z = zget h z) by (intros; subst V; apply zget_zset_other; assumption).
    destruct (Z.ltb_spec n (e * 2)) as [NOCH|CH].
    { (* [comment removed for export] *)
      cbn [fst snd]. split; [lia|]. split; [|split; [intros; reflexivity|split; [|exact KN]]].
      - intros z Hz. apply D1; [exact Hz|]. intros X. assert (e * 2 <= z) by (rewrite <- X; pose proof (Z.mul_div_le z 2); lia). lia.
      - intros z Hz. subst V. apply zget_zset_other. lia. }
    (* [comment removed for export] *)
    set (m := if (e * 2 <? n) && (zget w (zget h (e * 2 + 1)) <? zget w (zget h (e * 2))) then e * 2 + 1 else e * 2).
    assert (Hm : e * 2 <= m <= n /\ m / 2 = e /\ m <> e /\ (forall c, 2 <= c <= n -> c / 2 = e -> zget w (zget V m) <= zget w (zget V c))).
    { subst m. destruct (Z.ltb_spec (e * 2) n) as [L|G]; cbn [andb].
      - destruct (Z.ltb_spec (zget w (zget h (e * 2 + 1))) (zget w (zget h (e * 2)))) as [L2|G2]; cbn [andb].
        + split; [lia|]. split; [rewrite Z.div_add_l by lia; change (1/2) with 0; lia|]. split; [lia|].
          intros c Hc Hce.
          assert (c = e * 2 \/ c = e * 2 + 1) by (pose proof (Z.div_mod c 2 ltac:(lia)); pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
          destruct H as [-> | ->]; rewrite !VO by lia; lia.
        + split; [lia|]. split; [rewrite Z.div_mul by lia; reflexivity|]. split; [lia|].
          intros c Hc Hce.
          assert (c = e * 2 \/ c = e * 2 + 1) by (pose proof (Z.div_mod c 2 ltac:(lia)); pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
          destruct H as [-> | ->]; rewrite !VO by lia; lia.
      - split; [lia|]. split; [rewrite Z.div_mul by lia; reflexivity|]. split; [lia|].
        intros c Hc Hce.
        assert (c = e * 2 \/ c = e * 2 + 1) by (pose proof (Z.div_mod c 2 ltac:(lia)); pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
        destruct H as [-> | ->]; rewrite !VO by lia; lia. }
    clearbody m. cps_destruct Hm as (M1 & M2 & M3 & M4).
    rewrite <- (VO m) by exact M3.
    destruct (Z.ltb_spec (zget w tmp) (zget w (zget V m))) as [STOP|GO].
    { cbn [fst snd]. fold V. split; [lia|]. split; [|split; [intros; reflexivity|split; [|exact KN]]].
      - intros z Hz. destruct (Z.eq_dec (z/2) e) as [ZE|ZNE]; [|apply D1; assumption].
        rewrite ZE, VE. pose proof (M4 z Hz ZE). lia.
      - intros z Hz. subst V. apply zget_zset_other. lia. }
    (* [comment removed for export] *)
    assert (SW : forall z, zget (zset (zset h e (zget V m)) m tmp) z = zget (zset (zset V m (zget V e)) e (zget V m)) z).
    { intros z. rewrite !zget_zset, VE.
      destruct (Z.eqb_spec z m) as [->|NZM].
      - replace (m =? e) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - destruct (Z.eqb_spec z e) as [->|NZE]; [reflexivity|]. symmetry. apply VO. exact NZE. }
    assert (NZ : forall z, zget (zset (zset h e (zget V m)) m tmp) z = if z =? m then tmp else if z =? e then zget V m else zget V z).
    { intros z. rewrite !zget_zset. destruct (Z.eqb_spec z m) as [->|NZM]; [reflexivity|].
      destruct (Z.eqb_spec z e) as [->|NZE]; [reflexivity|]. symmetry. apply VO. exact NZE. }
    specialize (IH (zset h e (zget V m)) m tmp n).
    cps_destruct IH as (A & B & C & D & E).
    - lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. assert (0 < 2 ^ Z.of_nat fuel) by (apply Z.pow_pos_nonneg; lia). nia.
    - destruct ST as [S1 S2]. split; [|exact S2]. rewrite zget_zset_other by lia. exact S1.
    - exact Kt.
    - intros z Hz. rewrite NZ. destruct (Z.eqb_spec z m); [exact Kt|]. destruct (Z.eqb_spec z e); apply KN; lia.
    - split.
      + intros z Hz Hzm. rewrite !NZ.
        destruct (Z.eqb_spec z m) as [->|NZM].
        { rewrite M2. replace (e =? m) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia. }
        destruct (Z.eqb_spec (z/2) m) as [|_]; [congruence|].
        destruct (Z.eqb_spec z e) as [->|NZE].
        { destruct (Z.eqb_spec (e/2) e); [exfalso; pose proof (div2_lt e ltac:(lia)); lia|].
          apply D2; [lia| exact M2]. }
        destruct (Z.eqb_spec (z/2) e) as [ZE|ZNE]; [apply M4; assumption| apply D1; assumption].
      + intros c Hc Hcm. rewrite !NZ, M2.
        assert (HC2 : c = m * 2 \/ c = m * 2 + 1) by (pose proof (Z.div_mod c 2 ltac:(lia)); pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
        replace (e =? m) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
        replace (c =? m) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (c =? e) with false by (symmetry; apply Z.eqb_neq; lia).
        pose proof (D1 c Hc ltac:(rewrite Hcm; exact M3)) as X. rewrite Hcm in X. exact X.
    - split; [lia|]. split; [exact B|]. split.
      + intros v. rewrite C. rewrite (hcnt_ext (zset (zset V m (zget V e)) e (zget V m)) _ n v) by (intros; apply SW).
        apply hcnt_swap; lia.
      + split; [|exact E]. intros z Hz. rewrite D by exact Hz. rewrite zget_zset_other by lia. reflexivity.
  Qed.
End Heap2.
End BzCHuffF2.


Module BzCHuffF3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cntP_sumF : forall R m, cntP R m = sumF (fun i => if R i then 1 else 0) 0 m.
Proof.
  intros R m.
  assert (SS : forall (g : Z -> Z) j k, sumF g j (S k) = g j + sumF g (j + 1) k) by (intros; reflexivity).
  assert (SN : forall (g : Z -> Z) k j, sumF g j (S k) = sumF g j k + g (j + Z.of_nat k)).
  { intros g. induction k as [|k IHk]; intros j.
    - rewrite SS. cbn [sumF]. replace (j + Z.of_nat 0) with j by lia. lia.
    - rewrite SS, (IHk (j + 1)), SS. replace (j + 1 + Z.of_nat k) with (j + Z.of_nat (S k)) by lia. lia. }
  induction m as [|m IH]; cbn [cntP]; [reflexivity|]. rewrite IH, SN, Z.add_0_l. reflexivity.
Qed.

Lemma hcnt_upd : forall h n p u v, 1 <= p <= n ->
  hcnt (zset h p u) n v = hcnt h n v - (if zget h p =? v then 1 else 0) + (if u =? v then 1 else 0).
Proof.
  intros h n p u v Hp. unfold hcnt. rewrite !cntP_sumF.
  rewrite (sumF_upd (Z.to_nat n) (fun i => if zget h (i + 1) =? v then 1 else 0) _ 0 (p - 1)
             ((if u =? v then 1 else 0) - (if zget h p =? v then 1 else 0))); [lia|lia|].
  intros x. cbn beta. rewrite zget_zset. destruct (Z.eqb_spec (x + 1) p) as [E|NE].
  - replace (x =? p - 1) with true by (symmetry; apply Z.eqb_eq; lia). replace p with (x + 1) by lia. lia.
  - replace (x =? p - 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma hcnt_snoc : forall h n v, 1 <= n -> hcnt h n v = hcnt h (n - 1) v + (if zget h n =? v then 1 else 0).
Proof.
  intros h n v Hn. unfold hcnt. replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. cbn [cntP].
  replace (Z.of_nat (Z.to_nat (n - 1)) + 1) with n by lia. reflexivity.
Qed.

Lemma hcnt_0 : forall h v, hcnt h 0 v = 0.
Proof. intros. unfold hcnt. reflexivity. Qed.

Lemma hcnt_nonneg : forall h n v, 0 <= hcnt h n v.
Proof. intros. unfold hcnt. apply cntP_nonneg. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma HO_min : forall w h n, HO w h n -> forall z, 1 <= z <= n -> zget w (zget h 1) <= zget w (zget h z).
Proof.
  intros w h n HOh.
  assert (G : forall m : nat, forall z, 1 <= z <= n -> (Z.to_nat z <= m)%nat -> zget w (zget h 1) <= zget w (zget h z)).
  { induction m as [|m IH]; intros z Hz Hm; [lia|].
    destruct (Z.eq_dec z 1) as [->|NE]; [lia|].
    assert (D : 1 <= z / 2 < z) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    eapply Z.le_trans; [apply (IH (z / 2)); lia | apply HOh; lia]. }
  intros z Hz. apply (G (Z.to_nat z)); [exact Hz | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Wrap.
  Variable w : zarr.

  Lemma zset_same_ext : forall h p z, zget (zset h p (zget h p)) z = zget h z.
  Proof. intros. rewrite zget_zset. destruct (Z.eqb_spec z p) as [->|]; reflexivity. Qed.

  Lemma upheap_spec : forall h n, 1 <= n < 2 ^ 20 -> SENT w h -> KNN w h n ->
    (forall z, 2 <= z <= n - 1 -> zget w (zget h (z / 2)) <= zget w (zget h z)) ->
    let R := upheap h w n in
    HO w R n /\ (forall v, hcnt R n v = hcnt h n v) /\ (forall z, (z < 1 \/ n < z) -> zget R z = zget h z) /\ KNN w R n /\ SENT w R.
  Proof.
    intros h n Hn ST KN HOp. unfold upheap.
    pose proof (upheap_loop_spec w 20 h n (zget h n) n ltac:(lia) ltac:(cbn; lia) ST ltac:(apply KN; lia)) as U.
    cps_destruct U as (A & B & C & D & E).
    - intros z Hz. rewrite zset_same_ext. apply KN. exact Hz.
    - split.
      + intros z Hz Hne. rewrite !zset_same_ext. apply HOp. lia.
      + intros c Hc Hce He2. exfalso. assert (n * 2 <= c) by (rewrite <- Hce; pose proof (Z.mul_div_le c 2); lia). lia.
    - destruct (upheap_loop 20 h w n (zget h n)) as [h' zz]. cbn [fst snd] in *.
      split; [exact B|]. split; [intros v; rewrite C; apply hcnt_ext; intros; apply zset_same_ext|].
      split; [exact D|]. split; [exact E|].
      destruct ST as [S1 S2]. split; [|exact S2]. rewrite D by lia. exact S1.
  Qed.

  Lemma pop_spec : forall h n, 2 <= n < 2 ^ 20 -> SENT w h -> KNN w h n -> HO w h n ->
    let h1 := zset h 1 (zget h n) in
    let R := downheap h1 w (n - 1) 1 in
    HO w R (n - 1) /\ (forall v, hcnt R (n - 1) v = hcnt h n v - (if zget h 1 =? v then 1 else 0)) /\
    (forall z, (z < 1 \/ n - 1 < z) -> zget R z = zget h1 z) /\ KNN w R (n - 1) /\ SENT w R.
  Proof.
    intros h n Hn ST KN HOh. cbn zeta. set (h1 := zset h 1 (zget h n)). unfold downheap.
    assert (K1 : KNN w h1 (n - 1)).
    { intros z Hz. subst h1. rewrite zget_zset. destruct (Z.eqb_spec z 1); apply KN; lia. }
    assert (S1' : SENT w h1).
    { destruct ST as [S1 S2]. split; [|exact S2]. subst h1. rewrite zget_zset_other by lia. exact S1. }
    pose proof (downheap_loop_spec w 20 h1 1 (zget h1 1) (n - 1) ltac:(lia) ltac:(cbn; lia) S1' ltac:(apply K1; lia)) as U.
    cps_destruct U as (A & B & C & D & E).
    - intros z Hz. rewrite zset_same_ext. apply K1. exact Hz.
    - split.
      + intros z Hz Hne. rewrite !zset_same_ext.
        assert (P2 : 2 <= z / 2) by (assert (1 <= z / 2) by (apply Z.div_le_lower_bound; lia); lia).
        assert (z / 2 < z) by (apply Z.div_lt_upper_bound; lia).
        subst h1. rewrite !zget_zset_other by lia. apply HOh. lia.
      + intros c Hc Hce. rewrite !zset_same_ext. change (1 / 2) with 0.
        destruct S1' as [X1 X2]. rewrite X1, X2. apply K1. lia.
    - destruct (downheap_loop 20 h1 w (n - 1) 1 (zget h1 1)) as [h' zz]. cbn [fst snd] in *.
      split; [exact B|]. split.
      + intros v. rewrite C. rewrite (hcnt_ext h1) by (intros; apply zset_same_ext).
        subst h1. rewrite hcnt_upd by lia. rewrite (hcnt_snoc h n v) by lia. lia.
      + split; [exact D|]. split; [exact E|].
        destruct S1' as [X1 X2]. split; [|exact X2]. rewrite D by lia. exact X1.
  Qed.
End Wrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fill.
  Variable w : zarr.
  Variable A : Z.
  Hypothesis HA : 1 <= A <= 258.
  Hypothesis WNN : forall x, 1 <= x <= A -> 0 <= zget w x.

  Definition FI (heap parent : zarr) (m : Z) : Prop :=   (* [comment removed for export] *)
    SENT w heap /\ HO w heap m /\
    (forall x, hcnt heap m x = if (1 <=? x) && (x <=? m) then 1 else 0) /\
    (forall x, 1 <= x <= m -> zget parent x = -1).

  Lemma FI_entries : forall heap parent m, 0 <= m -> FI heap parent m -> forall z, 1 <= z <= m -> 1 <= zget heap z <= m.
  Proof.
    (intros heap parent m Hm; cps_intros (ST0 & O & C & P); intros z Hz).
    pose proof (hcnt_in heap m z Hz) as X. rewrite C in X.
    destruct (Z.leb_spec 1 (zget heap z)), (Z.leb_spec (zget heap z) m); cbn in X; lia.
  Qed.

  Lemma fill_spec : forall n heap parent i,
    1 <= i -> i - 1 + Z.of_nat n <= A -> FI heap parent (i - 1) ->
    let r := hm_fill n heap w parent (i - 1) i in
    snd r = i - 1 + Z.of_nat n /\ FI (fst (fst r)) (snd (fst r)) (i - 1 + Z.of_nat n).
  Proof.
    induction n as [|n IH]; intros heap parent i Hi Hn F; cbn zeta.
    - cbn [hm_fill fst snd]. rewrite Z.add_0_r. split; [reflexivity| exact F].
    - cbn [hm_fill]. replace (i - 1 + 1) with i by lia.
      cps_destruct F as (ST0 & O & C & P).
      set (heap1 := zset heap i i).
      assert (K1 : KNN w heap1 i).
      { intros z Hz. subst heap1. rewrite zget_zset. destruct (Z.eqb_spec z i) as [->|NE]; [apply WNN; lia|].
        pose proof (FI_entries heap parent (i - 1) ltac:(lia) (conj ST0 (conj O (conj C P))) z ltac:(lia)). apply WNN. lia. }
      assert (S1 : SENT w heap1).
      { destruct ST0 as [X1 X2]. split; [|exact X2]. subst heap1. rewrite zget_zset_other by lia. exact X1. }
      pose proof (upheap_spec w heap1 i ltac:(lia) S1 K1) as U. cbn zeta in U.
      cps_destruct U as (UA & UB & UC & UD & UE).
      { intros z Hz. subst heap1. assert (z / 2 < z) by (apply Z.div_lt_upper_bound; lia). rewrite !zget_zset_other by lia. apply O. lia. }
      specialize (IH (upheap heap1 w i) (zset parent i (-1)) (i + 1) ltac:(lia) ltac:(lia)).
      replace (i + 1 - 1) with i in IH by lia.
      destruct IH as [R1 R2].
      { split; [exact UE|]. split; [exact UA|]. split.
        - intros x. rewrite UB. subst heap1. rewrite hcnt_snoc by lia. rewrite zget_zset_same.
          rewrite (hcnt_ext heap) by (intros; apply zget_zset_other; lia). rewrite C.
          destruct (Z.leb_spec 1 x), (Z.leb_spec x (i - 1)), (Z.leb_spec x i), (Z.eqb_spec i x); cbn; lia.
        - intros x Hx. rewrite zget_zset. destruct (Z.eqb_spec x i); [reflexivity| apply P; lia]. }
      replace (i - 1 + Z.of_nat (S n)) with (i + Z.of_nat n) by lia.
      split; [exact R1 | exact R2].
  Qed.
End Fill.
End BzCHuffF3.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF3.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma pop_spec' : forall w h n, 1 <= n < 2 ^ 20 -> SENT w h -> KNN w h n -> HO w h n ->
  let h1 := zset h 1 (zget h n) in
  let R := downheap h1 w (n - 1) 1 in
  HO w R (n - 1) /\ (forall v, hcnt R (n - 1) v = hcnt h n v - (if zget h 1 =? v then 1 else 0)) /\
  (forall z, (z < 1 \/ n - 1 < z) -> zget R z = zget h1 z) /\ KNN w R (n - 1) /\ SENT w R.
Proof.
  intros w h n Hn ST KN HOh. destruct (Z.eq_dec n 1) as [->|NE]; [|apply pop_spec; try assumption; lia].
  cbn zeta. change (1 - 1) with 0.
  assert (DS : forall f hh nn zz tmp, downheap_loop (S f) hh w nn zz tmp =
      (let yy := Z.shiftl zz 1 in
       if nn <? yy then (hh, zz) else
       let yy := if (yy <? nn) && (zget w (zget hh (yy + 1)) <? zget w (zget hh yy)) then yy + 1 else yy in
       if zget w tmp <? zget w (zget hh yy) then (hh, zz) else downheap_loop f (zset hh zz (zget hh yy)) w nn yy tmp)) by (intros; reflexivity).
  assert (E : forall z, zget (downheap (zset h 1 (zget h 1)) w 0 1) z = zget h z).
  { intros z. unfold downheap. rewrite DS. cbn zeta. change (Z.shiftl 1 1) with 2. change (0 <? 2) with true. cbn iota.
    rewrite !zset_same_ext. reflexivity. }
  split; [intros z Hz; lia|]. split.
  - intros v. rewrite hcnt_0. rewrite (hcnt_snoc h 1) by lia. change (1-1) with 0. rewrite hcnt_0. lia.
  - split; [intros z Hz; rewrite E, zset_same_ext; reflexivity|]. split; [intros z Hz; lia|].
    destruct ST as [S1 S2]. split; [rewrite E; exact S1| exact S2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Combine.
  Variables (A T0 TMAX : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HT : T0 + A <= TMAX.
  Hypothesis HTM : TMAX <= 8388607.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition RS (wt par : zarr) (nN : Z) : Z :=
    sumF (fun x => if zget par x =? -1 then tw (zget wt x) else 0) 1 (Z.to_nat nN).

  Record CI (k : Z) (s : hms) : Prop := MKCI {
    ci_nN : hm_nNodes s = A + k;
    ci_nH : hm_nHeap s = A - k;
    ci_k : 0 <= k <= A - 1;
    ci_sent : SENT (hm_weight s) (hm_heap s);
    ci_ent : forall z, 1 <= z <= hm_nHeap s -> 1 <= zget (hm_heap s) z <= hm_nNodes s /\ zget (hm_parent s) (zget (hm_heap s) z) = -1;
    ci_cnt : forall x, 1 <= x <= hm_nNodes s -> zget (hm_parent s) x = -1 -> hcnt (hm_heap s) (hm_nHeap s) x = 1;
    ci_ho : HO (hm_weight s) (hm_heap s) (hm_nHeap s);
    ci_w : forall x, 1 <= x <= hm_nNodes s -> W32 (zget (hm_weight s) x) /\ 1 <= tw (zget (hm_weight s) x);
    ci_rs : RS (hm_weight s) (hm_parent s) (hm_nNodes s) <= T0 + k;
    ci_par : forall x, 1 <= x <= hm_nNodes s -> zget (hm_parent s) x <> -1 ->
               x < zget (hm_parent s) x <= hm_nNodes s /\ A < zget (hm_parent s) x;
    ci_edge : forall x, 1 <= x <= hm_nNodes s -> zget (hm_parent s) x <> -1 ->
               tw (zget (hm_weight s) x) + 1 <= tw (zget (hm_weight s) (zget (hm_parent s) x)) /\
               (forall c, 1 <= c <= hm_nNodes s -> zget (hm_parent s) c = x ->
                  tw (zget (hm_weight s) x) + tw (zget (hm_weight s) c) <= tw (zget (hm_weight s) (zget (hm_parent s) x)));
    ci_dom : forall x c r, 1 <= x <= hm_nNodes s -> zget (hm_parent s) x = -1 ->
               1 <= c <= hm_nNodes s -> zget (hm_parent s) c = x ->
               1 <= r <= hm_nNodes s -> zget (hm_parent s) r = -1 -> r <> x ->
               tw (zget (hm_weight s) c) <= tw (zget (hm_weight s) r)
  }.

  (* [comment removed for export] *)
  Lemma pop2_facts : forall k s, CI k s -> 1 < hm_nHeap s ->
    let h := hm_heap s in let wt := hm_weight s in let par := hm_parent s in let nH := hm_nHeap s in let nN := hm_nNodes s in
    let n1 := zget h 1 in
    let hp1 := downheap (zset h 1 (zget h nH)) wt (nH - 1) 1 in
    let n2 := zget hp1 1 in
    let hp2 := downheap (zset hp1 1 (zget hp1 (nH - 1))) wt (nH - 2) 1 in
    1 <= n1 <= nN /\ zget par n1 = -1 /\ 1 <= n2 <= nN /\ zget par n2 = -1 /\ n1 <> n2 /\
    zget wt n1 <= zget wt n2 /\
    (forall r, 1 <= r <= nN -> zget par r = -1 -> r <> n1 -> zget wt n2 <= zget wt r) /\
    HO wt hp2 (nH - 2) /\ KNN wt hp2 (nH - 2) /\ SENT wt hp2 /\
    (forall v, hcnt hp2 (nH - 2) v = hcnt h nH v - (if n1 =? v then 1 else 0) - (if n2 =? v then 1 else 0)) /\
    (forall z, 1 <= z <= nH - 2 -> 1 <= zget hp2 z <= nN /\ zget par (zget hp2 z) = -1 /\ zget hp2 z <> n1 /\ zget hp2 z <> n2).
  Proof.
    intros k s CIs HnH. destruct CIs. cbn zeta.
    set (h := hm_heap s) in *. set (wt := hm_weight s) in *. set (par := hm_parent s) in *.
    set (nH := hm_nHeap s) in *. set (nN := hm_nNodes s) in *.
    assert (KN : KNN wt h nH).
    { intros z Hz. destruct (ci_ent0 z Hz) as [R _]. pose proof (ci_w0 _ R) as [[W _] _]. exact W. }
    pose proof (pop_spec' wt h nH ltac:(lia) ci_sent0 KN ci_ho0) as P1. cbn zeta in P1. cps_destruct P1 as (A1 & B1 & C1 & D1 & E1).
    set (hp1 := downheap (zset h 1 (zget h nH)) wt (nH - 1) 1) in *.
    destruct (ci_ent0 1 ltac:(lia)) as [N1R N1P].
    (* [comment removed for export] *)
    assert (ENT1 : forall z, 1 <= z <= nH - 1 -> 1 <= zget hp1 z <= nN /\ zget par (zget hp1 z) = -1 /\ zget hp1 z <> zget h 1).
    { intros z Hz. pose proof (hcnt_in hp1 (nH - 1) z Hz) as X. rewrite B1 in X.
      destruct (Z.eqb_spec (zget h 1) (zget hp1 z)) as [EQ|NE].
      - rewrite <- EQ in X. rewrite (ci_cnt0 (zget h 1) N1R N1P) in X. lia.
      - cps_pose (hcnt_ex h nH (zget hp1 z) ltac:(lia)) as (z' & Hz' & Ez'). rewrite <- Ez'.
        destruct (ci_ent0 z' Hz') as [R P]. split; [exact R|]. split; [exact P|]. rewrite Ez'. congruence. }
    pose proof (pop_spec' wt hp1 (nH - 1) ltac:(lia) E1 D1 A1) as P2. cbn zeta in P2.
    replace (nH - 1 - 1) with (nH - 2) in P2 by lia. cps_destruct P2 as (A2 & B2 & C2 & D2 & E2).
    cps_destruct (ENT1 1 ltac:(lia)) as (N2R & N2P & N21).
    split; [exact N1R|]. split; [exact N1P|]. split; [exact N2R|]. split; [exact N2P|]. split; [congruence|].
    split.
    { (* [comment removed for export] *)
      pose proof (hcnt_in hp1 (nH - 1) 1 ltac:(lia)) as X. rewrite B1 in X.
      cps_pose (hcnt_ex h nH (zget hp1 1) ltac:(destruct (zget h 1 =? zget hp1 1); lia)) as (z' & Hz' & Ez').
      rewrite <- Ez'. apply (HO_min wt h nH ci_ho0). exact Hz'. }
    split.
    { (* [comment removed for export] *)
      intros r Hr Pr Nr. pose proof (ci_cnt0 r Hr Pr) as X.
      assert (Y : 1 <= hcnt hp1 (nH - 1) r) by (rewrite B1, X; destruct (Z.eqb_spec (zget h 1) r); [congruence|lia]).
      cps_destruct (hcnt_ex hp1 (nH - 1) r Y) as (z' & Hz' & <-). apply (HO_min wt hp1 (nH - 1) A1). exact Hz'. }
    split; [exact A2|]. split; [exact D2|]. split; [exact E2|]. split.
    { intros v. rewrite B2, B1. destruct (Z.eqb_spec (zget h 1) v), (Z.eqb_spec (zget hp1 1) v); lia. }
    intros z Hz. pose proof (hcnt_in (downheap (zset hp1 1 (zget hp1 (nH - 1))) wt (nH - 2) 1) (nH - 2) z Hz) as X. rewrite B2, B1 in X.
    set (v := zget (downheap (zset hp1 1 (zget hp1 (nH - 1))) wt (nH - 2) 1) z) in *.
    destruct (Z.eqb_spec (zget h 1) v) as [EQ|NE1].
    { rewrite <- EQ in X. rewrite (ci_cnt0 (zget h 1) N1R N1P) in X. destruct (zget hp1 1 =? zget h 1); lia. }
    destruct (Z.eqb_spec (zget hp1 1) v) as [EQ|NE2].
    { rewrite <- EQ in X. rewrite (ci_cnt0 (zget hp1 1) N2R N2P) in X. lia. }
    cps_pose (hcnt_ex h nH v ltac:(lia)) as (z' & Hz' & Ez'). rewrite <- Ez' in *.
    destruct (ci_ent0 z' Hz') as [R P]. repeat split; try lia; try exact P; congruence.
  Qed.

  Lemma sumF_snoc : forall (g : Z -> Z) k j, sumF g j (S k) = sumF g j k + g (j + Z.of_nat k).
  Proof.
    intros g. induction k as [|k IHk]; intros j.
    - cbn [sumF]. replace (j + Z.of_nat 0) with j by lia. lia.
    - change (sumF g j (S (S k))) with (g j + sumF g (j + 1) (S k)). rewrite (IHk (j + 1)).
      change (sumF g j (S k)) with (g j + sumF g (j + 1) k). replace (j + 1 + Z.of_nat k) with (j + Z.of_nat (S k)) by lia. lia.
  Qed.

  Lemma combine_iter_ok : forall k s, CI k s -> 1 < hm_nHeap s -> CI (k + 1) (hm_combine_iter s).
  Proof.
    intros k s CIs HnH.
    pose proof (pop2_facts k s CIs HnH) as PF. cbn zeta in PF.
    destruct CIs.
    set (h := hm_heap s) in *. set (wt := hm_weight s) in *. set (par := hm_parent s) in *.
    set (nH := hm_nHeap s) in *. set (nN := hm_nNodes s) in *.
    set (n1 := zget h 1) in *.
    set (hp1 := downheap (zset h 1 (zget h nH)) wt (nH - 1) 1) in *.
    set (n2 := zget hp1 1) in *.
    set (hp2 := downheap (zset hp1 1 (zget hp1 (nH - 1))) wt (nH - 2) 1) in *.
    cps_destruct PF as (N1R & N1P & N2R & N2P & N12 & K12 & K2R & HO2 & KN2 & ST2 & CNT2 & ENT2).
    set (M := nN + 1).
    set (par' := zset (zset (zset par n2 M) n1 M) M (-1)).
    set (wt' := zset wt M (addweights (zget wt n1) (zget wt n2))).
    set (h3 := zset hp2 (nH - 2 + 1) M).
    (* [comment removed for export] *)
    assert (IT : hm_combine_iter s = HMS (upheap h3 wt' (nH - 2 + 1)) wt' par' (nH - 2 + 1) M).
    { unfold hm_combine_iter. fold h wt par nH nN. fold n1 hp1. fold n2.
      replace (nH - 1 - 1) with (nH - 2) by lia. fold hp2. reflexivity. }
    rewrite IT.
    (* [comment removed for export] *)
    pose proof (ci_w0 n1 N1R) as [[W1a W1b] T1]. pose proof (ci_w0 n2 N2R) as [[W2a W2b] T2].
    pose proof (addweights_bounds (zget wt n1) (zget wt n2) (conj W1a W1b) (conj W2a W2b)) as AWB.
    pose proof (addweights_tw (zget wt n1) (zget wt n2) (conj W1a W1b) (conj W2a W2b)) as AWT.
    (* [comment removed for export] *)
    set (F := fun x => if zget par x =? -1 then tw (zget wt x) else 0).
    assert (Fnn : forall x, 1 <= x < 1 + Z.of_nat (Z.to_nat nN) -> 0 <= F x).
    { intros x Hx. subst F. cbn beta. destruct (zget par x =? -1); [|lia]. pose proof (ci_w0 x ltac:(lia)). lia. }
    set (F1 := fun x => if x =? n1 then 0 else F x).
    set (F2 := fun x => if x =? n2 then 0 else F1 x).
    assert (RS12 : RS wt par nN = sumF F2 1 (Z.to_nat nN) + tw (zget wt n1) + tw (zget wt n2)).
    { unfold RS. fold F.
      assert (E1 : sumF F1 1 (Z.to_nat nN) = sumF F 1 (Z.to_nat nN) + (- tw (zget wt n1))).
      { apply (sumF_upd (Z.to_nat nN) F F1 1 n1); [lia|].
        intros x. subst F1 F. cbn beta. destruct (Z.eqb_spec x n1) as [->|]; [rewrite N1P; cbn; lia|reflexivity]. }
      assert (E2 : sumF F2 1 (Z.to_nat nN) = sumF F1 1 (Z.to_nat nN) + (- tw (zget wt n2))).
      { apply (sumF_upd (Z.to_nat nN) F1 F2 1 n2); [lia|].
        intros x. subst F2 F1 F. cbn beta. destruct (Z.eqb_spec x n2) as [->|]; [|reflexivity].
        replace (n2 =? n1) with false by (symmetry; apply Z.eqb_neq; congruence). rewrite N2P. cbn. lia. }
      lia. }
    assert (F2nn : 0 <= sumF F2 1 (Z.to_nat nN)).
    { apply sumF_nonneg. intros x Hx. subst F2 F1. cbn beta. destruct (x =? n2); [lia|]. destruct (x =? n1); [lia|]. apply Fnn. exact Hx. }
    assert (S12 : tw (zget wt n1) + tw (zget wt n2) <= TMAX - 1) by lia.
    assert (WM : W32 (addweights (zget wt n1) (zget wt n2))) by (unfold W32; lia).
    (* [comment removed for export] *)
    assert (PAR' : forall x, zget par' x = if x =? M then -1 else if x =? n1 then M else if x =? n2 then M else zget par x).
    { intros x. subst par'. rewrite !zget_zset. reflexivity. }
    assert (WT' : forall x, zget wt' x = if x =? M then addweights (zget wt n1) (zget wt n2) else zget wt x).
    { intros x. subst wt'. apply zget_zset. }
    assert (WTo : forall x, x <= nN -> zget wt' x = zget wt x).
    { intros x Hx. rewrite WT'. replace (x =? M) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    (* [comment removed for export] *)
    assert (H3 : forall z, zget h3 z = if z =? nH - 2 + 1 then M else zget hp2 z) by (intros; subst h3; apply zget_zset).
    pose proof (upheap_spec wt' h3 (nH - 2 + 1) ltac:(lia)) as UP. cbn zeta in UP.
    cps_destruct UP as (UA & UB & UC & UD & UE).
    { destruct ST2 as [X1 X2]. split; [rewrite H3; replace (0 =? nH - 2 + 1) with false by (symmetry; apply Z.eqb_neq; lia); exact X1|].
      rewrite WTo by lia. exact X2. }
    { intros z Hz. rewrite H3. destruct (Z.eqb_spec z (nH - 2 + 1)) as [->|NE].
      - rewrite WT'. rewrite Z.eqb_refl. lia.
      - destruct (ENT2 z ltac:(lia)) as (R & _). rewrite WTo by lia. apply KN2. lia. }
    { intros z Hz. rewrite !H3.
      assert (1 <= z / 2 < z) by (split; [apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound]; lia).
      replace (z / 2 =? nH - 2 + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (z =? nH - 2 + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (ENT2 z ltac:(lia)) as (R & _). destruct (ENT2 (z/2) ltac:(lia)) as (R' & _).
      rewrite !WTo by lia. apply HO2. lia. }
    set (h4 := upheap h3 wt' (nH - 2 + 1)) in *.
    (* [comment removed for export] *)
    assert (CNT4 : forall v, hcnt h4 (nH - 2 + 1) v =
      hcnt h nH v - (if n1 =? v then 1 else 0) - (if n2 =? v then 1 else 0) + (if M =? v then 1 else 0)).
    { intros v. rewrite UB. subst h3. rewrite hcnt_upd by lia. rewrite hcnt_snoc by lia.
      replace (nH - 2 + 1 - 1) with (nH - 2) by lia. rewrite CNT2. lia. }
    assert (CNTM : hcnt h nH M = 0).
    { destruct (Z.eq_dec (hcnt h nH M) 0) as [E|NE]; [exact E|]. pose proof (hcnt_nonneg h nH M).
      cps_destruct (hcnt_ex h nH M ltac:(lia)) as (z & Hz & Ez). destruct (ci_ent0 z Hz) as [R _]. lia. }
    (* [comment removed for export] *)
    assert (ENT4 : forall z, 1 <= z <= nH - 2 + 1 -> zget h4 z = M \/ (1 <= zget h4 z <= nN /\ zget par (zget h4 z) = -1 /\ zget h4 z <> n1 /\ zget h4 z <> n2)).
    { intros z Hz. pose proof (hcnt_in h4 (nH - 2 + 1) z Hz) as X. rewrite CNT4 in X.
      destruct (Z.eqb_spec M (zget h4 z)) as [EM|NM]; [left; symmetry; exact EM|right].
      destruct (Z.eqb_spec n1 (zget h4 z)) as [E1|NV1]. { rewrite <- E1 in X. rewrite (ci_cnt0 n1 N1R N1P) in X. destruct (n2 =? n1); lia. }
      destruct (Z.eqb_spec n2 (zget h4 z)) as [E2|NV2]. { rewrite <- E2 in X. rewrite (ci_cnt0 n2 N2R N2P) in X. lia. }
      pose proof (hcnt_nonneg h nH (zget h4 z)). cps_destruct (hcnt_ex h nH (zget h4 z) ltac:(lia)) as (z' & Hz' & Ez').
      destruct (ci_ent0 z' Hz') as [R P]. rewrite Ez' in R, P. repeat split; try lia; try exact P; congruence. }
    constructor; cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes].
    - lia.
    - lia.
    - lia.
    - exact UE.
    - intros z Hz. destruct (ENT4 z Hz) as [E|(R & P & X1 & X2)].
      + rewrite E, PAR', Z.eqb_refl. lia.
      + split; [lia|]. rewrite PAR'.
        replace (zget h4 z =? M) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (zget h4 z =? n1) with false by (symmetry; apply Z.eqb_neq; exact X1).
        replace (zget h4 z =? n2) with false by (symmetry; apply Z.eqb_neq; exact X2). exact P.
    - intros x Hx Px. rewrite CNT4. rewrite PAR' in Px.
      destruct (Z.eqb_spec x M) as [->|NxM].
      + rewrite CNTM. replace (n1 =? M) with false by (symmetry; apply Z.eqb_neq; lia). replace (n2 =? M) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia.
      + destruct (Z.eqb_spec x n1) as [->|Nx1]; [lia|]. destruct (Z.eqb_spec x n2) as [->|Nx2]; [lia|].
        rewrite (ci_cnt0 x ltac:(lia) Px).
        replace (n1 =? x) with false by (symmetry; apply Z.eqb_neq; congruence).
        replace (n2 =? x) with false by (symmetry; apply Z.eqb_neq; congruence).
        replace (M =? x) with false by (symmetry; apply Z.eqb_neq; congruence). lia.
    - exact UA.
    - intros x Hx. rewrite WT'. destruct (Z.eqb_spec x M) as [->|NxM].
      + split; [exact WM|]. lia.
      + apply ci_w0. lia.
    - (* [comment removed for export] *)
      unfold RS. replace (Z.to_nat M) with (S (Z.to_nat nN)) by lia. rewrite sumF_snoc.
      replace (1 + Z.of_nat (Z.to_nat nN)) with M by lia.
      rewrite PAR', Z.eqb_refl. cbn beta iota. rewrite Z.eqb_refl. cbn beta iota. rewrite WT', Z.eqb_refl. cbn beta iota.
      rewrite (sumF_ext (Z.to_nat nN) _ F2).
      2:{ intros x Hx. rewrite PAR', WT'. subst F2 F1 F. cbn beta.
          replace (x =? M) with false by (symmetry; apply Z.eqb_neq; lia).
          destruct (Z.eqb_spec x n1) as [->|Nx1]; cbn beta iota.
          - replace (M =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (n1 =? n2) with false by (symmetry; apply Z.eqb_neq; exact N12). reflexivity.
          - destruct (Z.eqb_spec x n2) as [->|Nx2]; cbn beta iota.
            + replace (M =? -1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
            + reflexivity. }
      lia.
    - intros x Hx Px. rewrite PAR' in Px |- *.
      destruct (Z.eqb_spec x M) as [->|NxM]; [congruence|].
      destruct (Z.eqb_spec x n1) as [->|Nx1]; [lia|]. destruct (Z.eqb_spec x n2) as [->|Nx2]; [lia|].
      pose proof (ci_par0 x ltac:(lia) Px). lia.
    - (* [comment removed for export] *)
      intros x Hx Px. rewrite PAR' in Px. rewrite !PAR'.
      destruct (Z.eqb_spec x M) as [->|NxM]; [congruence|]. cbn beta iota.
      assert (CH : forall c, 1 <= c <= M -> zget par' c = x -> zget par c = x /\ 1 <= c <= nN).
      { intros c Hc Pc. rewrite PAR' in Pc. destruct (Z.eqb_spec c M); [lia|]. destruct (Z.eqb_spec c n1); [lia|]. destruct (Z.eqb_spec c n2); [lia|]. split; [exact Pc|lia]. }
      destruct (Z.eqb_spec x n1) as [->|Nx1]; cbn beta iota.
      + rewrite (WT' M), Z.eqb_refl. rewrite (WTo n1) by lia. split; [lia|].
        intros c Hc Pc. destruct (CH c Hc Pc) as [Pc' Hc']. rewrite (WTo c) by lia.
        pose proof (ci_dom0 n1 c n2 N1R N1P Hc' Pc' N2R N2P ltac:(congruence)). lia.
      + destruct (Z.eqb_spec x n2) as [->|Nx2]; cbn beta iota.
        * rewrite (WT' M), Z.eqb_refl. rewrite (WTo n2) by lia. split; [lia|].
          intros c Hc Pc. destruct (CH c Hc Pc) as [Pc' Hc']. rewrite (WTo c) by lia.
          pose proof (ci_dom0 n2 c n1 N2R N2P Hc' Pc' N1R N1P ltac:(congruence)).
          pose proof (tw_mono _ _ K12). lia.
        * pose proof (ci_par0 x ltac:(lia) Px) as [PX1 PX2].
          rewrite (WTo x) by lia. rewrite (WTo (zget par x)) by lia.
          destruct (ci_edge0 x ltac:(lia) Px) as [E1 E2]. split; [exact E1|].
          intros c Hc Pc. destruct (CH c Hc Pc) as [Pc' Hc']. rewrite WTo by lia. apply E2; assumption.
    - (* [comment removed for export] *)
      intros x c r Hx Px Hc Pc Hr Pr Nrx. rewrite PAR' in Px, Pc, Pr.
      destruct (Z.eqb_spec c M) as [->|NcM]; [cbn beta iota in Pc; lia|]. cbn beta iota in Pc.
      assert (TWr : zget par r = -1 /\ r <> n1 /\ r <> n2 /\ r <= nN \/ r = M).
      { destruct (Z.eqb_spec r M) as [->|NrM]; [right; reflexivity|left].
        destruct (Z.eqb_spec r n1); [lia|]. destruct (Z.eqb_spec r n2); [lia|]. repeat split; try assumption; lia. }
      destruct (Z.eqb_spec x M) as [->|NxM].
      + (* [comment removed for export] *)
        destruct TWr as [(Pr' & Rn1 & Rn2 & RnN)| -> ]; [|congruence].
        rewrite (WTo r) by lia.
        assert (Cn : c = n1 \/ c = n2).
        { destruct (Z.eqb_spec c n1) as [->|]; [left; reflexivity|]. destruct (Z.eqb_spec c n2) as [->|]; [right; reflexivity|].
          exfalso. cbn beta iota in Pc. destruct (Z.eq_dec (zget par c) (-1)) as [E|NE]; [rewrite E in Pc; lia|]. pose proof (ci_par0 c ltac:(lia) NE). lia. }
        pose proof (K2R r ltac:(lia) Pr' Rn1) as KR. pose proof (tw_mono _ _ KR). pose proof (tw_mono _ _ K12).
        destruct Cn as [-> | ->]; rewrite WTo by lia; lia.
      + destruct (Z.eqb_spec x n1) as [->|]; [lia|]. destruct (Z.eqb_spec x n2) as [->|]; [lia|].
        destruct (Z.eqb_spec c n1) as [->|]; [lia|]. destruct (Z.eqb_spec c n2) as [->|]; [lia|].
        rewrite (WTo c) by lia.
        destruct TWr as [(Pr' & Rn1 & Rn2 & RnN)| -> ].
        * rewrite (WTo r) by lia. apply (ci_dom0 x c r); try assumption; lia.
        * rewrite WT', Z.eqb_refl.
          pose proof (ci_dom0 x c n1 ltac:(lia) Px ltac:(lia) Pc N1R N1P ltac:(congruence)). lia.
  Qed.
End Combine.
