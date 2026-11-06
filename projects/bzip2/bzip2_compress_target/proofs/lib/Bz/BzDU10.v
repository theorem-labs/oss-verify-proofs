(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasMtf.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Strategy 10 [mtf_sh4 mtf_sh1 mtf_shdown mtf_pull mtfrb_i mtfrb_j].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_mtfa_set_mtfa : forall d a, d_mtfa (d_set_mtfa d a) = a. Proof. intros []; reflexivity. Qed.
Lemma d_mtfbase_set_mtfa : forall d a, d_mtfbase (d_set_mtfa d a) = d_mtfbase d. Proof. intros []; reflexivity. Qed.
Lemma d_mtfa_set_mtfbase : forall d a, d_mtfa (d_set_mtfbase d a) = d_mtfa d. Proof. intros []; reflexivity. Qed.
Lemma d_mtfbase_set_mtfbase : forall d a, d_mtfbase (d_set_mtfbase d a) = a. Proof. intros []; reflexivity. Qed.
Lemma set_mtfa_mtfa : forall d a b, d_set_mtfa (d_set_mtfa d a) b = d_set_mtfa d b. Proof. intros []; reflexivity. Qed.
Lemma set_mtfa_id : forall d, d_set_mtfa d (d_mtfa d) = d. Proof. intros []; reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_tail (L : dsv) (d : dst) (uc : Z) (s : dstrm) : dres :=
  let u := zget (d_s2u d) uc in
  let d2 := d_set_unzftab d (zincr (d_unzftab d) u) in
  let nb := sv_nblock L in
  let d3 := if smallb d2 then d_set_ll16 d2 (zset (d_ll16 d2) nb u) else d_set_tt d2 (zset (d_tt d2) nb u) in
  mtf_val_start BZ_X_MTF_5 (sv_set_nblock L (nb + 1)) d3 s.
Definition K_LJ (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc : Z) : dres := dgo F (lit_tail L d uc s).

Lemma K_LJ_fast : forall F L d s uc, d_small d = 0 ->
  K_LJ F L d s uc =
  K_HMTFC F (sv_set_nblock L (sv_nblock L + 1))
    (d_set_tt (d_set_unzftab d (zincr (d_unzftab d) (zget (d_s2u d) uc))) (zset (d_tt d) (sv_nblock L) (zget (d_s2u d) uc))) s.
Proof.
  intros F L d s uc H. unfold K_LJ, lit_tail, K_HMTFC, BZ_X_MTF_5.
  rewrite (smallb_false (d_set_unzftab d _)) by (destruct d; exact H). destruct d; reflexivity.
Qed.
Lemma K_LJ_small : forall F L d s uc, d_small d <> 0 ->
  K_LJ F L d s uc =
  K_HMTFC F (sv_set_nblock L (sv_nblock L + 1))
    (d_set_ll16 (d_set_unzftab d (zincr (d_unzftab d) (zget (d_s2u d) uc))) (zset (d_ll16 d) (sv_nblock L) (zget (d_s2u d) uc))) s.
Proof.
  intros F L d s uc H. unfold K_LJ, lit_tail, K_HMTFC, BZ_X_MTF_5.
  rewrite (smallb_true (d_set_unzftab d _)) by (destruct d; exact H). destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mtf_sh4_fuel : forall n m a pp nn, nn < 4 * Z.of_nat n + 4 -> nn < 4 * Z.of_nat m + 4 -> mtf_sh4 n a pp nn = mtf_sh4 m a pp nn.
Proof.
  induction n as [|n IH]; intros m a pp nn Hn Hm.
  - destruct m as [|m]; [reflexivity|]. cbn [mtf_sh4]. destruct (Z.ltb_spec 3 nn); [cbn in Hn; lia| reflexivity].
  - destruct m as [|m]; cbn [mtf_sh4].
    + destruct (Z.ltb_spec 3 nn); [cbn in Hm; lia| reflexivity].
    + destruct (Z.ltb_spec 3 nn); [| reflexivity]. apply IH; lia.
Qed.
Lemma mtf_sh1_fuel : forall n m a pp nn, nn < Z.of_nat n + 1 -> nn < Z.of_nat m + 1 -> mtf_sh1 n a pp nn = mtf_sh1 m a pp nn.
Proof.
  induction n as [|n IH]; intros m a pp nn Hn Hm.
  - destruct m as [|m]; [reflexivity|]. cbn [mtf_sh1]. destruct (Z.ltb_spec 0 nn); [cbn in Hn; lia| reflexivity].
  - destruct m as [|m]; cbn [mtf_sh1].
    + destruct (Z.ltb_spec 0 nn); [cbn in Hm; lia| reflexivity].
    + destruct (Z.ltb_spec 0 nn); [| reflexivity]. apply IH; lia.
Qed.
Lemma mtf_shdown_fuel : forall n m a k b, k - b < Z.of_nat n + 1 -> k - b < Z.of_nat m + 1 -> mtf_shdown n a k b = mtf_shdown m a k b.
Proof.
  induction n as [|n IH]; intros m a k b Hn Hm.
  - destruct m as [|m]; [reflexivity|]. cbn [mtf_shdown]. destruct (Z.ltb_spec b k); [cbn in Hn; lia| reflexivity].
  - destruct m as [|m]; cbn [mtf_shdown].
    + destruct (Z.ltb_spec b k); [cbn in Hm; lia| reflexivity].
    + destruct (Z.ltb_spec b k); [| reflexivity]. apply IH; lia.
Qed.
Lemma mtf_pull_fuel : forall n m a mb l, l < Z.of_nat n + 1 -> l < Z.of_nat m + 1 -> mtf_pull n a mb l = mtf_pull m a mb l.
Proof.
  induction n as [|n IH]; intros m a mb l Hn Hm.
  - destruct m as [|m]; [reflexivity|]. cbn [mtf_pull]. destruct (Z.ltb_spec 0 l); [cbn in Hn; lia| reflexivity].
  - destruct m as [|m]; cbn [mtf_pull].
    + destruct (Z.ltb_spec 0 l); [cbn in Hm; lia| reflexivity].
    + destruct (Z.ltb_spec 0 l); [| reflexivity]. apply IH; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_LFB (F : nat) (L : dsv) (d : dst) (s : dstrm) (pp k uc : Z) : dres :=
  K_LJ F L (d_set_mtfa d (zset (mtf_sh1 (Z.to_nat k) (d_mtfa d) pp k) pp uc)) s uc.
(* [comment removed for export] *)
Definition K_LFA (F : nat) (L : dsv) (d : dst) (s : dstrm) (pp nn uc : Z) : dres :=
  let '(a1, nn1) := mtf_sh4 (Z.to_nat nn) (d_mtfa d) pp nn in
  K_LJ F L (d_set_mtfa d (zset (mtf_sh1 (Z.to_nat nn1) a1 pp nn1) pp uc)) s uc.

Lemma K_LFB_step : forall F L d s pp k uc, 0 < k ->
  K_LFB F L d s pp k uc = K_LFB F L (d_set_mtfa d (zset (d_mtfa d) (pp + k) (zget (d_mtfa d) (pp + k - 1)))) s pp (k - 1) uc.
Proof.
  intros F L d s pp k uc Hk. unfold K_LFB. rewrite d_mtfa_set_mtfa, set_mtfa_mtfa.
  replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. cbn [mtf_sh1].
  destruct (Z.ltb_spec 0 k); [reflexivity| lia].
Qed.
Lemma K_LFB_exit : forall F L d s pp uc, K_LFB F L d s pp 0 uc = K_LJ F L (d_set_mtfa d (zset (d_mtfa d) pp uc)) s uc.
Proof. intros. unfold K_LFB. reflexivity. Qed.

Lemma K_LFA_step : forall F L d s pp nn uc, 3 < nn ->
  K_LFA F L d s pp nn uc =
  K_LFA F L (d_set_mtfa d
    (zset (zset (zset (zset (d_mtfa d) (pp + nn) (zget (d_mtfa d) (pp + nn - 1)))
                      (pp + nn - 1) (zget (d_mtfa d) (pp + nn - 2)))
                (pp + nn - 2) (zget (d_mtfa d) (pp + nn - 3)))
          (pp + nn - 3) (zget (d_mtfa d) (pp + nn - 4)))) s pp (nn - 4) uc.
Proof.
  intros F L d s pp nn uc Hnn. unfold K_LFA. rewrite d_mtfa_set_mtfa.
  replace (Z.to_nat nn) with (S (Z.to_nat nn - 1)) by lia. cbn [mtf_sh4].
  destruct (Z.ltb_spec 3 nn); [| lia].
  rewrite !zget_zset_other by lia.
  rewrite (mtf_sh4_fuel (Z.to_nat nn - 1) (Z.to_nat (nn - 4))) by lia.
  destruct (mtf_sh4 _ _ _ _) as [a1 nn1]. rewrite set_mtfa_mtfa. reflexivity.
Qed.
Lemma K_LFA_exit : forall F L d s pp nn uc, 0 <= nn <= 3 -> K_LFA F L d s pp nn uc = K_LFB F L d s pp nn uc.
Proof.
  intros F L d s pp nn uc Hnn. unfold K_LFA, K_LFB.
  rewrite (mtf_sh4_fuel (Z.to_nat nn) 0) by lia. cbn [mtf_sh4]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma K_HLIT_ret : forall F L d s, sv_nblockMAX L <= sv_nblock L -> K_HLIT F L d s = DRet BZ_DATA_ERROR L d s.
Proof.
  intros F L d s H. unfold K_HLIT, lit_arm. replace (sv_nblockMAX L <=? sv_nblock L) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma K_HLIT_fast : forall F L d s, sv_nblock L < sv_nblockMAX L -> 1 <= sv_nextSym L <= 16 ->
  K_HLIT F L d s =
  K_LFA F L d s (zget (d_mtfbase d) 0) (sv_nextSym L - 1) (zget (d_mtfa d) (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))).
Proof.
  intros F L d s Hnb Hns. unfold K_HLIT, lit_arm, K_LFA, K_LJ, lit_tail, mtf_decode.
  replace (sv_nblockMAX L <=? sv_nblock L) with false by (symmetry; apply Z.leb_gt; lia).
  replace (sv_nextSym L - 1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
  rewrite (mtf_sh4_fuel 4 (Z.to_nat (sv_nextSym L - 1))) by lia.
  destruct (mtf_sh4 _ _ _ _) as [a1 nn1] eqn:E4.
  assert (R : 0 <= nn1 <= 3).
  { assert (G : forall n a pp nn, 0 <= nn -> let r := snd (mtf_sh4 n a pp nn) in 0 <= r <= nn /\ (r <= 3 \/ r = nn - 4 * Z.of_nat n)).
    { induction n as [|n IH]; intros a pp nn Hnn.
      - cbn. lia.
      - cbn [mtf_sh4]. destruct (Z.ltb_spec 3 nn).
        + lazymatch goal with |- context [mtf_sh4 n ?a4 pp (nn - 4)] => pose proof (IH a4 pp (nn - 4) ltac:(lia)) as X end.
          cbv zeta in X |- *. rewrite Nat2Z.inj_succ. lia.
        + cbn. lia. }
    pose proof (G (Z.to_nat (sv_nextSym L - 1)) (d_mtfa d) (zget (d_mtfbase d) 0) (sv_nextSym L - 1) ltac:(lia)) as X.
    rewrite E4 in X. cbv zeta in X. cbn [snd] in X. lia. }
  rewrite (mtf_sh1_fuel 4 (Z.to_nat nn1)) by lia.
  destruct d; cbn -[zset zget zincr mtf_sh1 mtf_val_start dgo Z.add Z.sub Z.eqb]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_LRO (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc ii : Z) : dres :=
  let '(a4, mb4) := mtfrb_i (Z.to_nat (ii + 1)) ii (3855 + 16 * ii) (d_mtfa d) (d_mtfbase d) in
  K_LJ F L (d_set_mtfbase (d_set_mtfa d a4) mb4) s uc.
(* [comment removed for export] *)
Definition K_LRI (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc ii j : Z) : dres :=
  let '(a', kk') := mtfrb_j (Z.to_nat (16 - j)) (15 - j) ii (3855 + 16 * ii - j) (d_mtfa d) (d_mtfbase d) in
  K_LRO F L (d_set_mtfbase (d_set_mtfa d a') (zset (d_mtfbase d) ii (kk' + 1))) s uc (ii - 1).
(* [comment removed for export] *)
Definition K_LGT (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc : Z) : dres :=
  let b0 := zget (d_mtfbase d) 0 - 1 in
  let d' := d_set_mtfbase (d_set_mtfa d (zset (d_mtfa d) b0 uc)) (zset (d_mtfbase d) 0 b0) in
  if b0 =? 0 then K_LRO F L d' s uc 15 else K_LJ F L d' s uc.
(* [comment removed for export] *)
Definition K_LGD (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc l : Z) : dres :=
  let '(a2, mb2) := mtf_pull (Z.to_nat l) (d_mtfa d) (d_mtfbase d) l in
  K_LGT F L (d_set_mtfbase (d_set_mtfa d a2) mb2) s uc.
(* [comment removed for export] *)
Definition K_LGE (F : nat) (L : dsv) (d : dst) (s : dstrm) (lno uc : Z) : dres :=
  K_LGD F L (d_set_mtfbase d (zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1))) s uc lno.
(* [comment removed for export] *)
Definition K_LGC (F : nat) (L : dsv) (d : dst) (s : dstrm) (lno k uc : Z) : dres :=
  let b := zget (d_mtfbase d) lno in
  K_LGE F L (d_set_mtfa d (mtf_shdown (Z.to_nat (k - b)) (d_mtfa d) k b)) s lno uc.

Lemma K_LGC_step : forall F L d s lno k uc, zget (d_mtfbase d) lno < k ->
  K_LGC F L d s lno k uc = K_LGC F L (d_set_mtfa d (zset (d_mtfa d) k (zget (d_mtfa d) (k - 1)))) s lno (k - 1) uc.
Proof.
  intros F L d s lno k uc Hk. unfold K_LGC. rewrite d_mtfbase_set_mtfa, d_mtfa_set_mtfa, set_mtfa_mtfa.
  replace (Z.to_nat (k - zget (d_mtfbase d) lno)) with (S (Z.to_nat (k - 1 - zget (d_mtfbase d) lno))) by lia.
  cbn [mtf_shdown]. destruct (Z.ltb_spec (zget (d_mtfbase d) lno) k); [reflexivity| lia].
Qed.
Lemma K_LGC_exit : forall F L d s lno uc, K_LGC F L d s lno (zget (d_mtfbase d) lno) uc = K_LGE F L d s lno uc.
Proof. intros. unfold K_LGC. rewrite Z.sub_diag. cbn [Z.to_nat mtf_shdown]. rewrite set_mtfa_id. reflexivity. Qed.

Lemma K_LGE_eq : forall F L d s lno uc,
  K_LGE F L d s lno uc = K_LGD F L (d_set_mtfbase d (zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1))) s uc lno.
Proof. reflexivity. Qed.

Lemma K_LGD_step : forall F L d s uc l, 0 < l ->
  K_LGD F L d s uc l =
  K_LGD F L (d_set_mtfa (d_set_mtfbase d (zset (d_mtfbase d) l (zget (d_mtfbase d) l - 1)))
               (zset (d_mtfa d) (zget (d_mtfbase d) l - 1) (zget (d_mtfa d) (zget (d_mtfbase d) (l - 1) + 15)))) s uc (l - 1).
Proof.
  intros F L d s uc l Hl. unfold K_LGD.
  replace (Z.to_nat l) with (S (Z.to_nat (l - 1))) by lia. cbn [mtf_pull].
  destruct (Z.ltb_spec 0 l); [| lia]. rewrite zget_zset_other by lia.
  destruct d; cbn -[mtf_pull zset zget Z.add Z.sub K_LGT Z.to_nat].
  destruct (mtf_pull _ _ _ _) as [a2 mb2]. reflexivity.
Qed.
Lemma K_LGD_exit : forall F L d s uc, K_LGD F L d s uc 0 = K_LGT F L d s uc.
Proof. intros. unfold K_LGD. cbn [Z.to_nat mtf_pull]. destruct d; reflexivity. Qed.

Lemma K_LGT_eq : forall F L d s uc,
  K_LGT F L d s uc =
  let b0 := zget (d_mtfbase d) 0 - 1 in
  let d' := d_set_mtfbase (d_set_mtfa d (zset (d_mtfa d) b0 uc)) (zset (d_mtfbase d) 0 b0) in
  if b0 =? 0 then K_LRO F L d' s uc 15 else K_LJ F L d' s uc.
Proof. reflexivity. Qed.

Lemma mtfrb_j_kk : forall n jj ii kk a mb, snd (mtfrb_j n jj ii kk a mb) = kk - Z.of_nat n.
Proof.
  induction n as [|n IH]; intros jj ii kk a mb; cbn [mtfrb_j snd]; [cbn; lia|].
  rewrite IH. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma K_LRO_row : forall F L d s uc ii, 0 <= ii -> K_LRO F L d s uc ii = K_LRI F L d s uc ii 0.
Proof.
  intros F L d s uc ii Hii. unfold K_LRO, K_LRI.
  replace (Z.to_nat (ii + 1)) with (S (Z.to_nat (ii - 1 + 1))) by lia. cbn [mtfrb_i].
  rewrite !Z.sub_0_r. change (Z.to_nat 16) with 16%nat.
  destruct (mtfrb_j _ _ _ _ _ _) as [a' kk'] eqn:E.
  pose proof (f_equal snd E) as K. rewrite mtfrb_j_kk in K. cbn [snd] in K. change (Z.of_nat 16) with 16 in K.
  unfold K_LRO. rewrite d_mtfa_set_mtfbase, d_mtfa_set_mtfa, d_mtfbase_set_mtfbase.
  replace (3855 + 16 * (ii - 1)) with kk' by lia.
  destruct (mtfrb_i _ _ _ _ _) as [a4 mb4]. destruct d; reflexivity.
Qed.
Lemma K_LRO_exit : forall F L d s uc, K_LRO F L d s uc (-1) = K_LJ F L d s uc.
Proof. intros. unfold K_LRO. cbn [Z.to_nat Z.add mtfrb_i Pos.add]. destruct d; reflexivity. Qed.

Lemma K_LRI_step : forall F L d s uc ii j, 0 <= j <= 15 ->
  K_LRI F L d s uc ii j =
  K_LRI F L (d_set_mtfa d (zset (d_mtfa d) (3855 + 16 * ii - j) (zget (d_mtfa d) (zget (d_mtfbase d) ii + (15 - j))))) s uc ii (j + 1).
Proof.
  intros F L d s uc ii j Hj. unfold K_LRI. rewrite d_mtfa_set_mtfa, d_mtfbase_set_mtfa.
  replace (Z.to_nat (16 - j)) with (S (Z.to_nat (16 - (j + 1)))) by lia. cbn [mtfrb_j].
  replace (15 - j - 1) with (15 - (j + 1)) by lia. replace (3855 + 16 * ii - j - 1) with (3855 + 16 * ii - (j + 1)) by lia.
  destruct (mtfrb_j _ _ _ _ _ _) as [a' kk']. destruct d; reflexivity.
Qed.
Lemma K_LRI_exit : forall F L d s uc ii,
  K_LRI F L d s uc ii 16 = K_LRO F L (d_set_mtfbase d (zset (d_mtfbase d) ii (3840 + 16 * ii))) s uc (ii - 1).
Proof.
  intros. unfold K_LRI. change (Z.to_nat (16 - 16)) with 0%nat. cbn [mtfrb_j].
  replace (3855 + 16 * ii - 16 + 1) with (3840 + 16 * ii) by lia. rewrite set_mtfa_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma K_HLIT_gen : forall F L d s, sv_nblock L < sv_nblockMAX L -> 17 <= sv_nextSym L <= 256 ->
  let nn := sv_nextSym L - 1 in let lno := nn / 16 in let off := nn mod 16 in
  0 <= zget (d_mtfbase d) lno ->
  K_HLIT F L d s = K_LGC F L d s lno (zget (d_mtfbase d) lno + off) (zget (d_mtfa d) (zget (d_mtfbase d) lno + off)).
Proof.
  intros F L d s Hnb Hns. cbv zeta. intros Hb.
  pose proof (Z.div_pos (sv_nextSym L - 1) 16 ltac:(lia) ltac:(lia)) as L0.
  pose proof (Z.mod_pos_bound (sv_nextSym L - 1) 16 ltac:(lia)) as OFR.
  assert (LNO : 1 <= (sv_nextSym L - 1) / 16 <= 15).
  { pose proof (Z.div_mod (sv_nextSym L - 1) 16 ltac:(lia)). lia. }
  unfold K_HLIT, lit_arm, mtf_decode, K_LGC, K_LGE, K_LGD, K_LGT, K_LRO, K_LJ, lit_tail.
  replace (sv_nblockMAX L <=? sv_nblock L) with false by (symmetry; apply Z.leb_gt; lia).
  replace (sv_nextSym L - 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta.
  rewrite ?d_mtfbase_set_mtfa, ?d_mtfa_set_mtfa, ?d_mtfa_set_mtfbase, ?d_mtfbase_set_mtfbase.
  replace (zget (d_mtfbase d) ((sv_nextSym L - 1) / 16) + (sv_nextSym L - 1) mod 16 - zget (d_mtfbase d) ((sv_nextSym L - 1) / 16))
    with ((sv_nextSym L - 1) mod 16) by lia.
  rewrite (mtf_shdown_fuel 16 (Z.to_nat ((sv_nextSym L - 1) mod 16))) by lia.
  rewrite (mtf_pull_fuel 16 (Z.to_nat ((sv_nextSym L - 1) / 16))) by lia.
  destruct (mtf_pull _ _ _ _) as [a2 mb2].
  rewrite ?d_mtfbase_set_mtfa, ?d_mtfa_set_mtfa, ?d_mtfa_set_mtfbase, ?d_mtfbase_set_mtfbase.
  change (Z.to_nat (15 + 1)) with 16%nat. change (3855 + 16 * 15) with 4095.
  destruct (zget mb2 0 - 1 =? 0).
  - destruct (mtfrb_i _ _ _ _ _) as [a4 mb4]. destruct d; reflexivity.
  - destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ml_nomtfF (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ grp_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ blkF L d /\ cur_okF L d.
Lemma ml_nomtfF_of_ML : forall L d, dinv_ML L d -> ml_nomtfF L d.
Proof. (intros L d; cps_intros (A & G & T & M & B & C)). unfold ml_nomtfF. tauto. Qed.
Lemma ml_nomtfF_frame : forall L d d', ml_nomtfF L d ->
  d_nInUse d' = d_nInUse d -> d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d -> d_state d' = d_state d ->
  d_sel d' = d_sel d -> d_bs100k d' = d_bs100k d -> d_limit d' = d_limit d -> d_base d' = d_base d -> d_perm d' = d_perm d ->
  d_minLens d' = d_minLens d -> d_small d' = d_small d -> d_tt d' = d_tt d -> d_ll16 d' = d_ll16 d -> d_unzftab d' = d_unzftab d ->
  ml_nomtfF L d'.
Proof.
  (intros L d d'; cps_intros (A & G & T & B & C); intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15). unfold ml_nomtfF.
  split; [apply (alpha_ok_frame L L d d' A); try reflexivity; try assumption; rewrite E5; exact (alpha_ok_state L d A)|].
  split; [apply (grp_okF_frame L L d d' G); try reflexivity; assumption|].
  split; [apply (tabs_okF_frame d d'); assumption|].
  split; [apply (blkF_frame L L d d' B); try reflexivity; assumption|].
  apply (cur_okF_frame L L d d' C); try reflexivity; assumption.
Qed.
Lemma ml_nomtfF_set_mtfa : forall L d a, ml_nomtfF L d -> ml_nomtfF L (d_set_mtfa d a).
Proof. intros L d a H. apply (ml_nomtfF_frame L d _ H); destruct d; reflexivity. Qed.
Lemma ml_nomtfF_set_mtfbase : forall L d a, ml_nomtfF L d -> ml_nomtfF L (d_set_mtfbase d a).
Proof. intros L d a H. apply (ml_nomtfF_frame L d _ H); destruct d; reflexivity. Qed.

(* [comment removed for export] *)
Definition mtfa_ok (a : zarr) : Prop := forall k, 0 <= k < 4096 -> 0 <= zget a k < 256.
Lemma mtfa_ok_set : forall a i v, mtfa_ok a -> 0 <= v < 256 -> mtfa_ok (zset a i v).
Proof. intros a i v H Hv k Hk. rewrite zget_zset. destruct (k =? i); [lia| apply H; exact Hk]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mbrow (d : dst) (mb : Z -> Z) : Prop := forall l, 0 <= l < 16 -> zget (d_mtfbase d) l = mb l.
Lemma mbrow_set_mtfa : forall d a mb, mbrow d mb -> mbrow (d_set_mtfa d a) mb.
Proof. intros d a mb H l Hl. rewrite d_mtfbase_set_mtfa. apply H. exact Hl. Qed.
(* [comment removed for export] *)

Lemma mtf_inv_ext : forall f g, (forall l, 0 <= l < 16 -> f l = g l) -> mtf_inv g -> mtf_inv f.
Proof.
  (intros f g E; cps_intros (A & B & C)). unfold mtf_inv. rewrite !E by lia. split; [exact A|]. split; [| exact C].
  intros l Hl. rewrite !E by lia. apply B. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma mtf_okF_of_row : forall d mb, mbrow d mb -> mtf_inv mb -> mtfa_ok (d_mtfa d) -> mtf_okF d.
Proof.
  intros d mb R I A. unfold mtf_okF. split; [| exact A].
  apply (mtf_inv_ext (mtfb d) mb); [| exact I]. intros l Hl. unfold mtfb. apply R. exact Hl.
Qed.
Lemma mbrow_of_ML : forall L d, dinv_ML L d -> mbrow d (mtfb d) /\ mtf_inv (mtfb d) /\ mtfa_ok (d_mtfa d).
Proof. (intros L d; cps_intros (_ & _ & _ & [I A] & _)). split; [intros l Hl; reflexivity|]. split; [exact I| exact A]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dinv_ML_lit : forall L d mb uc,
  ml_nomtfF L d -> mbrow d mb -> mtf_inv mb -> mtfa_ok (d_mtfa d) -> 0 <= uc < 256 ->
  sv_nblock L < sv_nblockMAX L -> sv_nblockMAX L <= 900000 -> (forall i, 0 <= zget (d_s2u d) i < 256) ->
  let u := zget (d_s2u d) uc in
  let d2 := d_set_unzftab d (zincr (d_unzftab d) u) in
  dinv_HMTFC (sv_set_nblock L (sv_nblock L + 1)) (dstore d2 (sv_nblock L) u).
Proof.
  (intros L d mb uc; cps_intros (AL & GR & TB & BL & CU); intros ROW INV MA UC NB NB9 S2U). cbv zeta.
  set (u := zget (d_s2u d) uc). assert (UR : 0 <= u < 256) by (subst u; apply S2U).
  unfold zincr. set (d2 := d_set_unzftab d (zset (d_unzftab d) u (zget (d_unzftab d) u + 1))).
  cps_destruct BL as (NBR & SYMB & HIST). unfold alpha_ok in AL.
  pose proof (run_inv_entry d u (sv_nblock L) 1 ltac:(lia) UR SYMB HIST) as RI0. fold d2 in RI0.
  pose proof (run_inv_step d2 u (sv_nblock L) 1 0 ltac:(lia) ltac:(lia) UR RI0) as RI1.
  rewrite Z.add_0_r in RI1. change (0 + 1) with 1 in RI1.
  destruct (run_inv_exit _ _ _ _ RI1) as [SYM' HIST'].
  assert (FR : forall P : dst -> Prop,
    (forall d', d_nInUse d' = d_nInUse d -> d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d ->
       d_state d' = d_state d -> d_sel d' = d_sel d -> d_bs100k d' = d_bs100k d -> d_limit d' = d_limit d -> d_base d' = d_base d ->
       d_perm d' = d_perm d -> d_minLens d' = d_minLens d -> d_mtfbase d' = d_mtfbase d -> d_mtfa d' = d_mtfa d -> P d') ->
    P (dstore d2 (sv_nblock L) u)).
  { intros P H. apply H; subst d2; unfold dstore; destruct (smallb _); destruct d; reflexivity. }
  unfold dinv_HMTFC, dinv_ML.
  split.
  { apply FR. intros d' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. unfold alpha_ok. rewrite E1, E2, E3, E4, E5. destruct L; cbn in *; lia. }
  split.
  { apply FR. intros d' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. apply (grp_okF_frame L _ d d' GR); try assumption; destruct L; reflexivity. }
  split.
  { apply FR. intros d' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. destruct L; cbn in *. apply (tabs_okF_frame d d' _ _ TB); assumption. }
  split.
  { apply FR. intros d' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13.
    assert (M : mtf_okF d) by (apply (mtf_okF_of_row _ mb); assumption).
    apply (mtf_okF_frame d d' M E12 E13). }
  split.
  { unfold blkF. destruct L; cbn in *. split; [lia|]. split; [exact SYM'| exact HIST']. }
  apply FR. intros d' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13. apply (cur_okF_frame L _ d d' CU); try assumption; destruct L; reflexivity.
Qed.

Lemma dinv_ML_lit_fast : forall L d mb uc,
  ml_nomtfF L d -> mbrow d mb -> mtf_inv mb -> mtfa_ok (d_mtfa d) -> 0 <= uc < 256 ->
  sv_nblock L < sv_nblockMAX L -> sv_nblockMAX L <= 900000 -> (forall i, 0 <= zget (d_s2u d) i < 256) -> d_small d = 0 ->
  dinv_HMTFC (sv_set_nblock L (sv_nblock L + 1))
    (d_set_tt (d_set_unzftab d (zincr (d_unzftab d) (zget (d_s2u d) uc))) (zset (d_tt d) (sv_nblock L) (zget (d_s2u d) uc))).
Proof.
  intros L d mb uc A B C D E G H I SM.
  pose proof (dinv_ML_lit L d mb uc A B C D E G H I) as X. cbv zeta in X.
  rewrite (dstore_fast _ _ _) in X by (destruct d; exact SM). destruct d; exact X.
Qed.
Lemma dinv_ML_lit_small : forall L d mb uc,
  ml_nomtfF L d -> mbrow d mb -> mtf_inv mb -> mtfa_ok (d_mtfa d) -> 0 <= uc < 256 ->
  sv_nblock L < sv_nblockMAX L -> sv_nblockMAX L <= 900000 -> (forall i, 0 <= zget (d_s2u d) i < 256) -> d_small d <> 0 ->
  dinv_HMTFC (sv_set_nblock L (sv_nblock L + 1))
    (d_set_ll16 (d_set_unzftab d (zincr (d_unzftab d) (zget (d_s2u d) uc))) (zset (d_ll16 d) (sv_nblock L) (zget (d_s2u d) uc))).
Proof.
  intros L d mb uc A B C D E G H I SM.
  pose proof (dinv_ML_lit L d mb uc A B C D E G H I) as X. cbv zeta in X.
  rewrite (dstore_smallm _ _ _) in X by (destruct d; exact SM). destruct d; exact X.
Qed.

Lemma mbrow_ext : forall d f g, (forall l, 0 <= l < 16 -> f l = g l) -> mbrow d f -> mbrow d g.
Proof. intros d f g E R l Hl. rewrite (R l Hl). apply E. exact Hl. Qed.
(* [comment removed for export] *)
Lemma mbrow_set_gen : forall d d' mb i v, mbrow d mb -> d_mtfbase d' = zset (d_mtfbase d) i v -> mbrow d' (zfupd mb i v).
Proof. intros d d' mb i v R E l Hl. rewrite E, zget_zset, zfupd_eq. destruct (l =? i); [reflexivity| apply R; exact Hl]. Qed.
(* [comment removed for export] *)
Lemma K_LGC_exit' : forall F L d s lno k uc, k = zget (d_mtfbase d) lno -> K_LGC F L d s lno k uc = K_LGE F L d s lno uc.
Proof. intros F L d s lno k uc ->. apply K_LGC_exit. Qed.
